#ifndef __BV_OPS_H_
#define __BV_OPS_H_

#include <z3++.h>

#include "bv.h"

namespace stoch
{
namespace nonstd
{

/**
 *  Comparison
**/

template <typename T, typename U> struct bv_ult;

template <>
struct bv_ult <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();

        return v1.x < v2.x;
    }

    static const std::string op;
};

template <>
struct bv_ult <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvult(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_ult <small_bv, bool>::op = "u<";
const std::string bv_ult <z3::expr, z3::expr>::op = "u<";

template <typename T, typename U> struct bv_slt;

template <>
struct bv_slt <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        bv_ult <small_bv, bool> ult;
        return (v1.msb() && !v2.msb()) || ((v1.msb() == v2.msb()) && ult(v1, v2));
    }

    static const std::string op;
};

template <>
struct bv_slt <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvslt(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_slt <small_bv, bool>::op = "s<";
const std::string bv_slt <z3::expr, z3::expr>::op = "s<";

template <typename T, typename U> struct bv_ule;

template <>
struct bv_ule <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        return v1.x <= v2.x;
    }

    static const std::string op;
};

template <>
struct bv_ule <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvule(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_ule <small_bv, bool>::op = "u<=";
const std::string bv_ule <z3::expr, z3::expr>::op = "u<=";

template <typename T, typename U> struct bv_sle;

template <>
struct bv_sle <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        bv_ule <small_bv, bool> ule;
        return (v1.msb() && !v2.msb()) || ((v1.msb() == v2.msb()) && ule(v1, v2));
    }

    static const std::string op;
};

template <>
struct bv_sle <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvsle(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_sle <small_bv, bool>::op = "s<=";
const std::string bv_sle <z3::expr, z3::expr>::op = "s<=";

template <typename T, typename U> struct bv_eq;

template <>
struct bv_eq <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        return v1.len == v2.len && v1.x == v2.x;
    }

    static const std::string op;
};

template <>
struct bv_eq <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 == v2;
    }

    static const std::string op;
};

const std::string bv_eq <small_bv, bool>::op = "==";
const std::string bv_eq <z3::expr, z3::expr>::op = "==";

template <typename T, typename U> struct bv_uge;

template <>
struct bv_uge <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();

        return v1.x >= v2.x;
    }

    static const std::string op;
};

template <>
struct bv_uge <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvuge(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_uge <small_bv, bool>::op = "u>=";
const std::string bv_uge <z3::expr, z3::expr>::op = "u>=";

template <typename T, typename U> struct bv_sge;

template <>
struct bv_sge <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        return bv_sle <small_bv, bool> ()(v2, v1);
    }

    static const std::string op;
};

template <>
struct bv_sge <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvsge(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_sge <small_bv, bool>::op = "s>=";
const std::string bv_sge <z3::expr, z3::expr>::op = "s>=";

template <typename T, typename U> struct bv_ugt;

template <>
struct bv_ugt <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        return v1.x > v2.x;
    }

    static const std::string op;
};

template <>
struct bv_ugt <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvugt(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_ugt <small_bv, bool>::op = "u>";
const std::string bv_ugt <z3::expr, z3::expr>::op = "u>";

template <typename T, typename U> struct bv_sgt;

template <>
struct bv_sgt <small_bv, bool> : std::binary_function <small_bv, small_bv, bool>
{
    bool operator()(const small_bv& v1, const small_bv& v2)
    {
        return bv_slt <small_bv, bool> ()(v2, v1);
    }

    static const std::string op;
};

template <>
struct bv_sgt <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvsgt(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_sgt <small_bv, bool>::op = "s>";
const std::string bv_sgt <z3::expr, z3::expr>::op = "s>";

/**
 *  Bitwise logic
**/

template <typename T, typename U> struct bv_not;

template <>
struct bv_not <small_bv, small_bv> : std::unary_function <small_bv, small_bv>
{
    small_bv operator()(const small_bv& v)
    {
        return small_bv(v.len, ~v.x);
    }

    static const std::string op;
};

template <>
struct bv_not <z3::expr, z3::expr> : std::unary_function <z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v)
    {
        return ~v;
    }

    static const std::string op;
};

const std::string bv_not <small_bv, small_bv>::op = "~";
const std::string bv_not <z3::expr, z3::expr>::op = "~";

template <typename T, typename U> struct bv_and;

template <>
struct bv_and <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x & v2.x);
    }

    static const std::string op;
};

template <>
struct bv_and <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 & v2;
    }

    static const std::string op;
};

const std::string bv_and <small_bv, small_bv>::op = "&";
const std::string bv_and <z3::expr, z3::expr>::op = "&";

template <typename T, typename U> struct bv_or;

template <>
struct bv_or <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x | v2.x);
    }

    static const std::string op;
};

template <>
struct bv_or <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 | v2;
    }

    static const std::string op;
};

const std::string bv_or <small_bv, small_bv>::op = "|";
const std::string bv_or <z3::expr, z3::expr>::op = "|";

template <typename T, typename U> struct bv_xor;

template <>
struct bv_xor <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x ^ v2.x);
    }

    static const std::string op;
};

template <>
struct bv_xor <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 ^ v2;
    }

    static const std::string op;
};

const std::string bv_xor <small_bv, small_bv>::op = "^";
const std::string bv_xor <z3::expr, z3::expr>::op = "^";

/**
 *  Arithmetic
 *  TODO Confirm semantics wrt divide-by-zero.
**/

template <typename T, typename U> struct bv_add;

template <>
struct bv_add <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x + v2.x);
    }

    static const std::string op;
};

template <>
struct bv_add <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 + v2;
    }

    static const std::string op;
};

const std::string bv_add <small_bv, small_bv>::op = "+";
const std::string bv_add <z3::expr, z3::expr>::op = "+";

template <typename T, typename U> struct bv_sub;

template <>
struct bv_sub <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x - v2.x);
    }

    static const std::string op;
};

template <>
struct bv_sub <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 - v2;
    }

    static const std::string op;
};

const std::string bv_sub <small_bv, small_bv>::op = "-";
const std::string bv_sub <z3::expr, z3::expr>::op = "-";

template <typename T, typename U> struct bv_neg;

template <>
struct bv_neg <small_bv, small_bv> : std::unary_function <small_bv, small_bv>
{
    small_bv operator()(const small_bv& v)
    {
        return small_bv(v.len, -v.x);
    }

    static const std::string op;
};

template <>
struct bv_neg <z3::expr, z3::expr> : std::unary_function <z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v)
    {
        return -v;
    }

    static const std::string op;
};

const std::string bv_neg <small_bv, small_bv>::op = "-";
const std::string bv_neg <z3::expr, z3::expr>::op = "-";

template <typename T, typename U> struct bv_mul;

template <>
struct bv_mul <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        return small_bv(v1.len, v1.x * v2.x);
    }

    static const std::string op;
};

template <>
struct bv_mul <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return v1 * v2;
    }

    static const std::string op;
};

const std::string bv_mul <small_bv, small_bv>::op = "*";
const std::string bv_mul <z3::expr, z3::expr>::op = "*";

template <typename T, typename U> struct bv_udiv;

template <>
struct bv_udiv <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        return small_bv(v1.len, v2.x == 0 ? 0 : (v1.x / v2.x));
    }

    static const std::string op;
};

template <>
struct bv_udiv <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        z3::context& ctxt = v1.ctx();
        z3::expr zero(ctxt.bv_val(0, v1.get_sort().bv_size()));
        z3::expr guard(v2 == zero);
        z3::expr ans(ctxt, Z3_mk_bvudiv(ctxt, v1, v2));
        return z3::expr(ctxt, Z3_mk_ite(ctxt, guard, zero, ans));
    }

    static const std::string op;
};

const std::string bv_udiv <small_bv, small_bv>::op = "u/";
const std::string bv_udiv <z3::expr, z3::expr>::op = "u/";

template <typename T, typename U> struct bv_urem;

template <>
struct bv_urem <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        return small_bv(v1.len, v2.x == 0 ? 0 : (v1.x % v2.x));
    }

    static const std::string op;
};

template <>
struct bv_urem <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        z3::context& ctxt = v1.ctx();
        z3::expr zero(ctxt.bv_val(0, v1.get_sort().bv_size()));
        z3::expr guard(v2 == zero);
        z3::expr ans(ctxt, Z3_mk_bvurem(ctxt, v1, v2));
        return z3::expr(ctxt, Z3_mk_ite(ctxt, guard, zero, ans));
    }

    static const std::string op;
};

const std::string bv_urem <small_bv, small_bv>::op = "u%";
const std::string bv_urem <z3::expr, z3::expr>::op = "u%";

template <typename T, typename U> struct bv_sdiv;

template <>
struct bv_sdiv <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        bv_neg <small_bv, small_bv> neg;
        bv_udiv <small_bv, small_bv> udiv;
        size_t choice = (v1.msb() ? 1 : 0) + (v2.msb() ? 2 : 0);
        switch (choice)
        {
            case 0:
            {
                return udiv(v1, v2);
            }
            case 1:
            {
                return neg(udiv(neg(v1), v2));
            }
            case 2:
            {
                return neg(udiv(v1, neg(v2)));
            }
            case 3:
            {
                return udiv(neg(v1), neg(v2));
            }
            default:
            {
                assert(false);
            }
        }
    }

    static const std::string op;
};

template <>
struct bv_sdiv <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        z3::context& ctxt = v1.ctx();
        z3::expr zero(ctxt.bv_val(0, v1.get_sort().bv_size()));
        z3::expr guard(v2 == zero);
        z3::expr ans(ctxt, Z3_mk_bvsdiv(ctxt, v1, v2));
        return z3::expr(ctxt, Z3_mk_ite(ctxt, guard, zero, ans));
    }

    static const std::string op;
};

const std::string bv_sdiv <small_bv, small_bv>::op = "s/";
const std::string bv_sdiv <z3::expr, z3::expr>::op = "s/";

template <typename T, typename U> struct bv_srem;

template <>
struct bv_srem <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        bv_neg <small_bv, small_bv> neg;
        bv_urem <small_bv, small_bv> urem;
        size_t choice = (v1.msb() ? 1 : 0) + (v2.msb() ? 2 : 0);
        switch (choice)
        {
            case 0:
            {
                return urem(v1, v2);
            }
            case 1:
            {
                return neg(urem(neg(v1), v2));
            }
            case 2:
            {
                return urem(v1, neg(v2));
            }
            case 3:
            {
                return neg(urem(neg(v1), neg(v2)));
            }
            default:
            {
                assert(false);
            }
        }
    }

    static const std::string op;
};

template <>
struct bv_srem <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        z3::context& ctxt = v1.ctx();
        z3::expr zero(ctxt.bv_val(0, v1.get_sort().bv_size()));
        z3::expr guard(v2 == zero);
        z3::expr ans(ctxt, Z3_mk_bvsrem(ctxt, v1, v2));
        return z3::expr(ctxt, Z3_mk_ite(ctxt, guard, zero, ans));
    }

    static const std::string op;
};

const std::string bv_srem <small_bv, small_bv>::op = "s%";
const std::string bv_srem <z3::expr, z3::expr>::op = "s%";

/**
 *  Shifts
**/

template <typename T, typename U> struct bv_shl;

template <>
struct bv_shl <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        v2.mask();
        if (v2.x >= v1.width())
        {
            return small_bv(v1.len, 0);
        }
        return small_bv(v1.len, v1.x << v2.x);
    }

    static const std::string op;
};

template <>
struct bv_shl <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvshl(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_shl <small_bv, small_bv>::op = "<<";
const std::string bv_shl <z3::expr, z3::expr>::op = "<<";

template <typename T, typename U> struct bv_lshr;

template <>
struct bv_lshr <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();
        if (v2.x >= v1.width())
        {
            return small_bv(v1.len, 0);
        }
        return small_bv(v1.len, v1.x >> v2.x);
    }

    static const std::string op;
};

template <>
struct bv_lshr <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvlshr(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_lshr <small_bv, small_bv>::op = "l>>";
const std::string bv_lshr <z3::expr, z3::expr>::op = "l>>";

template <typename T, typename U> struct bv_ashr;

template <>
struct bv_ashr <small_bv, small_bv> : std::binary_function <small_bv, small_bv, small_bv>
{
    small_bv operator()(const small_bv& v1, const small_bv& v2)
    {
        v1.mask();
        v2.mask();

        if (v1.x >= v1.neg_max().x)
        {
            // [v1] is negative
            if (v2.x >= v1.len)
            {
                return small_bv(v1.len, -1);
            }
            else if (v2.x == 0)
            {
                return v1;
            }

            small_bv::unsigned_t u1(1);
            small_bv::unsigned_t neg_mask = ~((u1 << (v1.len - v2.x)) - 1);
            small_bv::unsigned_t ans = ((v1.x >> v2.x) | neg_mask);

            return small_bv(v1.len, ans);
        }
        else
        {
            // [v1] is non-negative
            if (v2.x >= v1.width())
            {
                return small_bv(v1.len, 0);
            }
            return small_bv(v1.len, v1.x >> v2.x);
        }
    }

    static const std::string op;
};

template <>
struct bv_ashr <z3::expr, z3::expr> : std::binary_function <z3::expr, z3::expr, z3::expr>
{
    z3::expr operator()(const z3::expr& v1, const z3::expr& v2)
    {
        return z3::expr(v1.ctx(), Z3_mk_bvashr(v1.ctx(), v1, v2));
    }

    static const std::string op;
};

const std::string bv_ashr <small_bv, small_bv>::op = "a>>";
const std::string bv_ashr <z3::expr, z3::expr>::op = "a>>";

} // namespace nonstd
} // namespace stoch

#endif // __BV_OPS_H_

