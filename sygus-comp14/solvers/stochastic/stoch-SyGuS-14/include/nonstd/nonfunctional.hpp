#ifndef __NONSTD_NONFUNCTIONAL_HPP_
#define __NONSTD_NONFUNCTIONAL_HPP_

#include "nonstd.hpp"

namespace stoch {
namespace nonstd {

template <typename T, typename U> struct plus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x + y;
    }

    static const string op;
};

template <typename T, typename U>
const string plus <T, U>::op = "+";

template <typename T, typename U> struct minus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x - y;
    }

    static const string op;
};

template <typename T, typename U>
const string minus <T, U>::op = "-";

template <typename T, typename U> struct multiplies : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x * y;
    }

    static const string op;
};

template <typename T, typename U>
const string multiplies <T, U>::op = "*";

template <typename T, typename U> struct divides : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x / y;
    }

    static const string op;
};

template <typename T, typename U>
const string divides <T, U>::op = "/";

/* template <typename T, typename U> struct modulus : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x % y;
    }

    static const string op;
};

template <typename T, typename U>
const string modulus <T, U>::op = "%"; */

template <typename T, typename U> struct negate : public std::unary_function <T, U>
{
    T operator() (const T& x) const
    {
        return -x;
    }

    static const string op;
};

template <typename T, typename U>
const string negate <T, U>::op = "-";

template <typename T, typename U> struct equal_to : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x == y;
    }

    static const string op;
};

template <typename T, typename U>
const string equal_to <T, U>::op = "=";

template <typename T, typename U> struct not_equal_to : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x != y;
    }

    static const string op;
};

template <typename T, typename U>
const string not_equal_to <T, U>::op = "!=";

template <typename T, typename U> struct greater : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x > y;
    }

    static const string op;
};

template <typename T, typename U>
const string greater <T, U>::op = ">";

template <typename T, typename U> struct less : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x < y;
    }

    static const string op;
};

template <typename T, typename U>
const string less <T, U>::op = "<";

template <typename T, typename U> struct greater_equal : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x >= y;
    }

    static const string op;
};

template <typename T, typename U>
const string greater_equal <T, U>::op = ">=";

template <typename T, typename U> struct less_equal : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x <= y;
    }

    static const string op;
};

template <typename T, typename U>
const string less_equal <T, U>::op = "<=";

template <typename T, typename U> struct logical_and : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x && y;
    }

    static const string op;
};

template <typename T, typename U>
const string logical_and <T, U>::op = "and";

template <typename T, typename U> struct logical_or : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x || y;
    }

    static const string op;
};

template <typename T, typename U>
const string logical_or <T, U>::op = "or";

template <typename T, typename U> struct logical_eq : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x == y;
    }

    static const string op;
};

template <typename T, typename U>
const string logical_eq <T, U>::op = "=";

template <typename T, typename U> struct logical_xor : public std::binary_function <T, T, U>
{
    U operator() (const T& x, const T& y) const
    {
        return x != y;
    }

    static const string op;
};

template <typename T, typename U>
const string logical_xor <T, U>::op = "!=";

template <typename T, typename U> struct logical_not : public std::unary_function <T, U>
{
    T operator() (const T& x) const
    {
        return !x;
    }

    static const string op;
};

template <typename T, typename U>
const string logical_not <T, U>::op = "not";

} // namespace nonstd
} // namespace stoch

#endif // __NONSTD_NONFUNCTIONAL_HPP_

