/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include<unordered_map>
#include<vector>
#include "model/model.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/var_subst.h"
#include "ast/array_decl_plugin.h"
#include "ast/well_sorted.h"
#include "ast/used_symbols.h"
#include "model/model_evaluator.h"
#include "api/api_context.h"

struct coverage_small {
    unsigned long c0;
    unsigned long c1;
};

struct coverage_big {
    std::vector<bool> c0;
    std::vector<bool> c1;
};

struct coverage_struct {
    struct coverage_small s;
    struct coverage_big b;
};

typedef struct coverage_struct coverage;

Z3_API int coverage_enable = 0;
Z3_API int coverage_bool = 0;
Z3_API int coverage_bv = 0;
Z3_API int coverage_all_bool = 0;
Z3_API int coverage_all_bv = 0;
Z3_API std::unordered_map<app*, coverage> covered;

Z3_API Z3_ast parse_bv(char const * n, Z3_sort s, Z3_context ctx);
Z3_API std::string bv_string(Z3_ast ast, Z3_context ctx);


typedef rational numeral;

Z3_ast parse_bv(char const * n, Z3_sort s, Z3_context ctx) {
    rational result = rational(0);
    while(*n) {
        char c = *n;
        if ('0' <= c && c <= '9') {
            result *= rational(16);
            result += rational(c - '0');
        }
        else if ('a' <= c && c <= 'f') {
            result *= rational(16);
            result += rational(10 + (c - 'a'));
        }

        ++n;
    }
    ast * a = mk_c(ctx)->mk_numeral_core(result, to_sort(s));
    return of_ast(a);
}

std::string bv_string(Z3_ast ast, Z3_context ctx) {
    std::string s;
    rational val;
    unsigned sz = 0;
    unsigned bv_size = 1;
    mk_c(ctx)->bvutil().is_numeral(to_expr(ast), val, bv_size);
    if (val.is_neg())
        val.neg();
    while (val.is_pos()) {
        rational c = val % rational(16);
        val = div(val, rational(16));
        char n;
        if (c <= rational(9)) {
            n = '0' + c.get_unsigned();
        } else {
            n = 'a' + (c.get_unsigned() - 10);
        }
        s += n;
        sz+=4;
    }
    while (sz < bv_size) {
        s += '0';
        sz+=4;
    }
    std::reverse(s.begin(), s.end());
    return s;
}

bool is_zero_bit(numeral & val, unsigned idx) {
    if (val.is_zero())
        return true;
    div(val, rational::power_of_two(idx), val);
    return (val % numeral(2)).is_zero();
}

void process_coverage(expr_ref & m_r, app * t, ast_manager & m) {
            if (coverage_enable != 2)
                return;
            auto res = covered.find(t);
            if (res == covered.end())
                return;
            if (!m_r) {
                return;
            }
            coverage & cov = res->second;
            params_ref p;
            bv_rewriter rewriter(m, p);
            numeral val;
            unsigned long value;
            unsigned sz;

            if (m.is_bool(m_r)) {
                sz = 1;
                if (m.is_true(m_r))
                    value = 1;
                else if (m.is_false(m_r))
                    value = 0;
                else
                    return;
            } else {
                bv_util util(m);

                if (!util.is_bv(m_r))
                    return;
                if (!rewriter.is_numeral(m_r, val, sz))
                    return;
                value = val.get_uint64();
            }
            if (cov.b.c0.size() == 0) {
                if (sz == 1) {
                    ++coverage_all_bool;
                } else {
                    coverage_all_bv += sz;
                }
                if (sz <= 64) {
                    cov.s.c0 = 0;
                    cov.s.c1 = 0;
                    cov.b.c0.resize(1, false);
                    cov.b.c1.resize(1, false);
                } else {
                    cov.b.c0.resize(sz, false);
                    cov.b.c1.resize(sz, false);
                }
            }
            if (sz <= 64) {
                for (unsigned long j = 0; j < sz; ++j) {
                    if ((value >> j) & 1) {
                        if (((cov.s.c1 >> j) & 1) == 0) {
                            cov.s.c1 |= 1ul << j;
                            if (sz > 1)
                                ++coverage_bv;
                            else
                                ++coverage_bool;
                        }
                    } else {
                        if (((cov.s.c0 >> j) & 1) == 0) {
                            cov.s.c0 |= 1ul << j;
                            if (sz > 1)
                                ++coverage_bv;
                            else
                                ++coverage_bool;
                        }
                    }
                }
            } else {
                int cur = coverage_bv;
                for (int j = 0; j < sz; ++j) {
                    if (is_zero_bit(val, j)) {
                        if (!cov.b.c0[j]) {
                            cov.b.c0[j] = true;
                            ++coverage_bv;
                        }
                    } else {
                        if (!cov.b.c1[j]) {
                            cov.b.c1[j] = true;
                            ++coverage_bv;
                        }
                    }
                }
            }
}

model::model(ast_manager & m):
    model_core(m),
    m_mev(*this) {
}

model::~model() {
    for (auto & kv : m_usort2universe) {
        m_manager.dec_ref(kv.m_key);
        m_manager.dec_array_ref(kv.m_value->size(), kv.m_value->c_ptr());
        dealloc(kv.m_value);
    }
}



void model::copy_const_interps(model const & source) {
    for (auto const& kv : source.m_interp) {
        register_decl(kv.m_key, kv.m_value);
    }
}

void model::copy_func_interps(model const & source) {
    for (auto const& kv : source.m_finterp) 
        register_decl(kv.m_key, kv.m_value->copy());
}

void model::copy_usort_interps(model const & source) {
    for (auto const& kv : source.m_usort2universe) 
        register_usort(kv.m_key, kv.m_value->size(), kv.m_value->c_ptr());
}

model * model::copy() const {
    model * m = alloc(model, m_manager);

    m->copy_const_interps(*this);
    m->copy_func_interps(*this);
    m->copy_usort_interps(*this);

    return m;
}

void visit(expr * e) {
    app * a = to_app(e);
    coverage cov;
    auto res = covered.emplace(a, cov);
    if (!res.second)
        return;
    for (int i = 0; i < a->get_num_args(); ++i)
        visit(a->get_args()[i]);
}

bool model::eval_expr(expr * e, expr_ref & result, bool model_completion) {
    if (coverage_enable == 1) {
        visit(e);
        return true;
    }
    scoped_model_completion _smc(*this, model_completion);
    try {
        result = (*this)(e);
        return true;
    }
    catch (model_evaluator_exception & ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg() << "\n";);
        return false;
    }
}

struct model::value_proc : public some_value_proc {
    model & m_model;
    value_proc(model & m):m_model(m) {}
    expr * operator()(sort * s) override {
        ptr_vector<expr> * u = nullptr;
        if (m_model.m_usort2universe.find(s, u)) {
            if (u->size() > 0)
                return u->get(0);
        }
        return nullptr;
    }
};

expr * model::get_some_value(sort * s) {
    value_proc p(*this);
    return m_manager.get_some_value(s, &p);
}

ptr_vector<expr> const & model::get_universe(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    SASSERT(u != 0);
    return *u;
}

bool model::has_uninterpreted_sort(sort * s) const {
    ptr_vector<expr> * u = nullptr;
    m_usort2universe.find(s, u);
    return u != nullptr;
}

unsigned model::get_num_uninterpreted_sorts() const {
    return m_usorts.size();
}

sort * model::get_uninterpreted_sort(unsigned idx) const {
    return m_usorts[idx];
}

void model::register_usort(sort * s, unsigned usize, expr * const * universe) {
    sort2universe::obj_map_entry * entry = m_usort2universe.insert_if_not_there2(s, 0);
    m_manager.inc_array_ref(usize, universe);
    if (entry->get_data().m_value == 0) {
        // new entry
        m_usorts.push_back(s);
        m_manager.inc_ref(s);
        ptr_vector<expr> * new_u = alloc(ptr_vector<expr>);
        new_u->append(usize, universe);
        entry->get_data().m_value = new_u;
    }
    else {
        // updating
        ptr_vector<expr> * u = entry->get_data().m_value;
        SASSERT(u);
        m_manager.dec_array_ref(u->size(), u->c_ptr());
        u->append(usize, universe);
    }
}

model * model::translate(ast_translation & translator) const {
    model * res = alloc(model, translator.to());

    // Translate const interps
    for (auto const& kv : m_interp) 
        res->register_decl(translator(kv.m_key), translator(kv.m_value));

    // Translate func interps
    for (auto const& kv : m_finterp) {
        func_interp * fi = kv.m_value;
        res->register_decl(translator(kv.m_key), fi->translate(translator));
    }

    // Translate usort interps
    for (auto const& kv : m_usort2universe) {
        ptr_vector<expr> new_universe;
        for (unsigned i=0; i < kv.m_value->size(); i++)
            new_universe.push_back(translator(kv.m_value->get(i)));
        res->register_usort(translator(kv.m_key),
                            new_universe.size(),
                            new_universe.c_ptr());
    }

    return res;
}

expr_ref model::operator()(expr* t) {
    return m_mev(t);
}

expr_ref_vector model::operator()(expr_ref_vector const& ts) {
    expr_ref_vector rs(m());
    for (expr* t : ts) rs.push_back((*this)(t));
    return rs;
}

bool model::is_true(expr* t) {
    return m().is_true((*this)(t));
}

bool model::is_false(expr* t) {
    return m().is_false((*this)(t));
}

bool model::is_true(expr_ref_vector const& ts) {
    for (expr* t : ts) if (!is_true(t)) return false;
    return true;
}

void model::reset_eval_cache() {
    m_mev.reset();
}

