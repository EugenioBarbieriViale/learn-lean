-- Exercises from "Mathematics in Lean"
-- https://leanprover-community.github.io/mathematics_in_lean/index.html

import Mathlib
import Mathlib.Data.Real.Basic

-- 2.  Basics
-- 2.1 Calculating
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm a c]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc a]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [mul_comm]
  rw [hyp']
  rw [sub_self]

section
variable (a b c : ℝ)

#check a
#check a + b
#check mul_comm a

end

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- 2.2. Proving Identities in Algebraic Structures
example : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]
theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm, add_comm b, neg_add_cancel, zero_add]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← zero_add b, ← neg_add_cancel a]
  rw [← zero_add c, ← neg_add_cancel a]
  rw [add_assoc, add_assoc, h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← zero_add a, ← zero_add c]
  rw [← neg_add_cancel b]
  rw [add_assoc, add_assoc, add_comm b, add_comm b, h]

theorem mul_zero {a : R} : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul {a : R} : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, add_zero, zero_add]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← add_zero b, ← add_neg_cancel a, ← add_assoc, add_comm b]
  rw [h, zero_add]
  
theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← add_zero a, ← add_neg_cancel b, ← add_assoc, h, zero_add]

theorem minus_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [← add_neg_cancel a, add_comm]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem two_mul (a : R) : 2 * a = a + a := by
  have h : a + a = (1 + 1) * a := by
    rw [add_mul, one_mul]
  rw [h]
  norm_num

end MyRing

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup
variable {G : Type*} [Group G]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  group

end MyGroup

-- 2.3 Using Theorems and Lemmas
example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  apply lt_of_le_of_lt h₂
  exact h₃

example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (h : a ≤ b) : Real.exp a ≤ Real.exp b := by
  rw [Real.exp_le_exp]
  exact h

example (h₀ : a ≤ b) (h₁ : c < d) : a + Real.exp c + e < b + Real.exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply Real.exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + Real.exp (a + d) ≤ c + Real.exp (a + e) := by
  sorry

