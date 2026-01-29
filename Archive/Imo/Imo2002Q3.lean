/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# IMO 2002 Q3

Find all pairs of positive integers $m,n ≥ 3$ for which there exist infinitely many
positive integers $a$ such that $(a^m+a-1) / (a^n+a^2-1)$ is itself an integer.

# Solution

It suffices to find $(m,n)$ pairs for which $a^n+a^2-1 ∣ a^m+a-1$, where both sides are viewed as
polynomials in $a$. Given the bounds on $m$ and $n$, there exists a real root $0 < r < 1$ of
$a^n+a^2-1$, whence $r^n+r^2 = r^m+r = 1$. If $2n ≤ m$ we have
$$1-r = r^m ≤ (r^n)^2 = (1-r^2)^2$$
$$0 ≤ r(r-1)(r^2+r-1)$$
but this is impossible because $r-1 < 0$ and $r^2+r-1 > r^m+r-1 = 0$.
Thus $m < 2n$, and from the polynomial divisibility condition we clearly have $n < m$.

From the same condition we also have
$$a^n+a^2-1 ∣ (a^m+a-1)(a+1) + (a^n+a^2-1) = a^m(a+1) - a^n.$$
Since $a^n$ is coprime to $a^n+a^2-1$ we have
$$a^n+a^2-1 ∣ a^{m-n}(a+1)-1.$$
The dividend's degree is $m-n+1$, which must be at least $n$ by degree considerations and
at most $n$ by $m < 2n$. So $m = 2n-1$, and comparing coefficients gives $m = 5, n = 3$
as the only solution.
-/

open Polynomial

namespace Imo2002Q3

variable {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)

include hm in
lemma natDegree_numerpol : (X ^ m + X - C (1 : ℤ)).natDegree = m := by
  compute_degree <;> grind

include hm in
lemma monic_numerpol : (X ^ m + X - C (1 : ℤ)).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X, Nat.one_lt_cast]
    lia
  · rw [eq_intCast, Int.cast_one, degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · rw [degree_X_pow, degree_X, Nat.one_lt_cast]
      lia

include hn in
lemma natDegree_denompol : (X ^ n + X ^ 2 - C (1 : ℤ)).natDegree = n := by
  compute_degree <;> grind

include hn in
lemma monic_denompol : (X ^ n + X ^ 2 - C (1 : ℤ)).Monic := by
  apply Monic.sub_of_left
  · apply monic_X_pow_add
    rw [degree_X_pow, Nat.cast_lt]
    lia
  · rw [eq_intCast, Int.cast_one, degree_one, degree_add_eq_left_of_degree_lt]
    · simp_rw [degree_X_pow, Nat.cast_pos]
      lia
    · simp_rw [degree_X_pow, Nat.cast_lt]
      lia

include hn in
/-- The given condition implies `x ^ n + x ^ 2 - 1 ∣ x ^ m + x - 1` as polynomials. -/
lemma dvd_of_hyp (h : {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite) :
    X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ m + X - C 1 := by
  set F := X ^ m + X - C (1 : ℤ)
  set G := X ^ n + X ^ 2 - C (1 : ℤ)
  have monG : G.Monic := monic_denompol hn
  rw [← modByMonic_eq_zero_iff_dvd monG]
  contrapose! h
  suffices ∃ Z : ℤ, ∀ a > 0, a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1 → a ≤ Z by
    obtain ⟨Z, hZ⟩ := this
    refine (Finset.Ioc 0 Z).finite_toSet.subset fun a ma ↦ ?_
    rw [Finset.coe_Ioc, Set.mem_Ioc]
    exact ⟨ma.1, hZ _ ma.1 ma.2⟩
  let IR := Int.castRingHom ℝ
  have tto : ((F %ₘ G).map IR).degree < (G.map IR).degree := by
    simp_rw [degree_map_eq_of_injective IR.injective_int]
    exact degree_modByMonic_lt F monG
  have mapGne0 : G.map IR ≠ 0 := ne_zero_of_degree_gt tto
  have mapRne0 : (F %ₘ G).map IR ≠ 0 := by rwa [Polynomial.map_ne_zero_iff IR.injective_int]
  rw [← div_tendsto_zero_iff_degree_lt _ _ mapGne0, Metric.tendsto_atTop] at tto
  specialize tto 1 zero_lt_one
  obtain ⟨Z₁, hZ₁⟩ := tto
  have enrG := eventually_no_roots _ mapGne0
  rw [Filter.eventually_atTop] at enrG
  obtain ⟨Z₂, hZ₂⟩ := enrG
  simp_rw [IsRoot.def] at hZ₂
  have enrR := eventually_no_roots _ mapRne0
  rw [Filter.eventually_atTop] at enrR
  obtain ⟨Z₃, hZ₃⟩ := enrR
  simp_rw [IsRoot.def] at hZ₃
  refine ⟨⌈max Z₁ (max Z₂ Z₃)⌉, fun a apos da ↦ ?_⟩
  by_contra! ca
  rw [← Int.cast_lt (R := ℝ)] at ca
  replace ca := (Int.le_ceil _).trans ca.le
  have lZ₁ : Z₁ ≤ a := (le_max_left ..).trans ca
  specialize hZ₁ _ lZ₁
  have lZ₂ : Z₂ ≤ a := ((le_max_left ..).trans (le_max_right ..)).trans ca
  specialize hZ₂ _ lZ₂
  have lZ₃ : Z₃ ≤ a := ((le_max_right ..).trans (le_max_right ..)).trans ca
  specialize hZ₃ _ lZ₃
  simp_rw [eval_intCast_map, Int.cast_eq, eq_intCast, ← ne_eq] at hZ₁ hZ₂ hZ₃
  have key : (((a ^ m + a - 1) / (a ^ n + a ^ 2 - 1) : ℤ) : ℝ) =
      (F /ₘ G).eval a + (F %ₘ G).eval a / G.eval a := by
    calc
      _ = ((a ^ m + a - 1 : ℤ) : ℝ) / (a ^ n + a ^ 2 - 1 : ℤ) := Int.cast_div_charZero da
      _ = (G * (F /ₘ G) + F %ₘ G).eval a / G.eval a := by
        rw [add_comm _ (F %ₘ G), modByMonic_add_div F monG]
        simp [F, G]
      _ = _ := by
        rw [eval_add, eval_mul, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_left₀ _ hZ₂]
  rw [← sub_eq_iff_eq_add', ← Int.cast_sub] at key
  rw [← key, dist_zero_right, Real.norm_eq_abs] at hZ₁
  norm_cast at hZ₁
  rw [Int.abs_lt_one_iff] at hZ₁
  rw [hZ₁, Int.cast_zero] at key
  exact (div_ne_zero hZ₃ hZ₂).symm key

include hn in
lemma exists_root_denompol :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1, ((X ^ n + X ^ 2 - C (1 : ℤ)).map (Int.castRingHom ℝ)).eval r = 0 := by
  simp only [eq_intCast, Int.cast_one, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, map_X, Polynomial.map_one, eval_sub, eval_add, eval_pow, eval_X, eval_one]
  let f (r : ℝ) := r ^ n + r ^ 2 - 1
  have cf : ContinuousOn f (Set.Icc 0 1) := by fun_prop
  have ivt := intermediate_value_Ioo zero_le_one cf
  simp only [ne_eq, show n ≠ 0 by lia, not_false_eq_true, zero_pow, OfNat.ofNat_ne_zero, add_zero,
    zero_sub, one_pow, add_sub_cancel_right, f] at ivt
  have zeromem : 0 ∈ Set.Ioo (-1 : ℝ) 1 := by simp
  specialize ivt zeromem
  rwa [Set.mem_image] at ivt

/-- A root of `x ^ n + x ^ 2 - 1` obtained from `exists_root_denompol`. -/
noncomputable def r₀ : ℝ :=
  (exists_root_denompol hn).choose

lemma r₀_spec : r₀ hn ∈ Set.Ioo (0 : ℝ) 1 ∧
    ((X ^ n + X ^ 2 - C (1 : ℤ)).map (Int.castRingHom ℝ)).IsRoot (r₀ hn) :=
  (exists_root_denompol hn).choose_spec

lemma r₀_spec' (h : X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ m + X - C 1) :
    ((X ^ m + X - C (1 : ℤ)).map (Int.castRingHom ℝ)).IsRoot (r₀ hn) := by
  rw [← map_dvd_map _ (Int.castRingHom ℝ).injective_int (monic_denompol hn)] at h
  exact (r₀_spec hn).2.dvd h

include hn in
lemma m_lt_twice_n (h : X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ m + X - C 1) : m < 2 * n := by
  by_contra! hm
  obtain ⟨rb, rpoln⟩ := r₀_spec hn
  have rpolm := r₀_spec' hn h
  set r := r₀ hn
  simp only [eq_intCast, Int.cast_one, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
    map_X, Polynomial.map_one, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, Set.mem_Ioo,
    eval_one] at rpolm rpoln rb
  have key : 1 - r ≤ (1 - r ^ 2) ^ 2 := by
    calc
      _ = r ^ m := by linarith only [rpolm]
      _ ≤ (r ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm]
        exact pow_le_pow_of_le_one rb.1.le rb.2.le hm
      _ = _ := by
        congr 1
        linarith only [rpoln]
  replace key : 0 ≤ r * (r - 1) * (r ^ 2 + r - 1) := by linarith
  apply absurd key
  rw [not_le]
  apply mul_neg_of_neg_of_pos (by nlinarith only [rb])
  rw [← rpolm]
  gcongr ?_ + _ - _
  exact pow_lt_pow_right_of_lt_one₀ rb.1 rb.2 (by lia)

include hm hn in
lemma n_lt_m (h : X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ m + X - C 1) : n < m := by
  have nlem := natDegree_le_of_dvd h (monic_numerpol hm).ne_zero
  rw [natDegree_numerpol hm, natDegree_denompol hn] at nlem
  apply lt_of_le_of_ne nlem
  by_contra h'
  subst h'
  rw [← dvd_sub_self_left,
    show X ^ n + X ^ 2 - C (1 : ℤ) - (X ^ n + X - C 1) = X ^ 2 - X by ring] at h
  have subn0 : X ^ 2 - X ≠ (0 : Polynomial ℤ) := by
    rw [sq, ← sub_one_mul]
    exact mul_ne_zero (X_sub_C_ne_zero 1) X_ne_zero
  have hn' := natDegree_le_of_dvd h subn0
  suffices (X ^ 2 - X : Polynomial ℤ).natDegree = 2 by
    rw [natDegree_denompol hn] at hn'
    lia
  compute_degree!

include hn in
lemma m_n_eq (c₁ : m < 2 * n) (c₂ : n < m)
    (h : X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ m + X - C 1) : m = 5 ∧ n = 3 := by
  suffices X ^ n + X ^ 2 - C (1 : ℤ) = X ^ (m - n) * (X + 1) - C 1 by
    rw [sub_left_inj, mul_add_one, ← pow_succ] at this
    have c₃ : n = m - n + 1 := by
      have deq := congr(natDegree $this)
      rw [natDegree_add_eq_left_of_degree_lt] at deq
      · rw [natDegree_add_eq_left_of_degree_lt] at deq
        · simpa only [natDegree_X_pow] using deq
        · simp_rw [degree_X_pow, Nat.cast_lt]
          lia
      · simp_rw [degree_X_pow, Nat.cast_lt]
        lia
    rw [← c₃, add_right_inj] at this
    have deq := congr(natDegree $this)
    simp_rw [natDegree_X_pow] at deq
    lia
  suffices X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ (m - n) * (X + C 1) - C 1 by
    refine (eq_of_monic_of_dvd_of_natDegree_le (monic_denompol hn) ?_ this ?_).symm
    · apply Monic.sub_of_left
      · exact (monic_X_pow _).mul (monic_X_add_C _)
      · rw [degree_C one_ne_zero, degree_mul, degree_X_pow, degree_X_add_C]
        norm_cast
        lia
    · rw [natDegree_sub_eq_left_of_natDegree_lt]
      · rw [natDegree_mul (by simp) (X_add_C_ne_zero 1), natDegree_X_pow, natDegree_X_add_C,
          natDegree_sub_eq_left_of_natDegree_lt]
        · rw [natDegree_add_eq_left_of_natDegree_lt]
          · rw [natDegree_X_pow]
            lia
          · simp_rw [natDegree_X_pow]
            lia
        · rw [natDegree_C, natDegree_add_eq_left_of_natDegree_lt]
          · rw [natDegree_X_pow]
            lia
          · simp_rw [natDegree_X_pow]
            lia
      · rw [natDegree_C, natDegree_mul (by simp) (X_add_C_ne_zero 1), natDegree_X_pow,
          natDegree_X_add_C]
        lia
  suffices X ^ n + X ^ 2 - C (1 : ℤ) ∣ X ^ n * (X ^ (m - n) * (X + C 1) - C 1) by
    refine IsRelPrime.dvd_of_dvd_mul_left (IsRelPrime.pow_right ?_) this
    rw [← Nat.sub_one_add_one (show n ≠ 0 by lia), pow_succ, sq, ← add_mul, sub_eq_add_neg]
    refine (IsRelPrime.neg_left ?_).mul_add_right_left _
    rw [C_1]
    exact isRelPrime_one_left
  rw [C_1, mul_sub_one, ← mul_assoc, ← pow_add, show n + (m - n) = m by lia, ← dvd_add_self_right,
    show X ^ m * (X + (1 : Polynomial ℤ)) - X ^ n + (X ^ n + X ^ 2 - 1) =
    (X ^ m + X - 1) * (X + 1) by ring]
  exact h.mul_right _

include hm hn in
theorem result : {a : ℤ | 0 < a ∧ a ^ n + a ^ 2 - 1 ∣ a ^ m + a - 1}.Infinite ↔ m = 5 ∧ n = 3 := by
  constructor <;> intro h
  · replace h := dvd_of_hyp hn h
    have c₁ := m_lt_twice_n hn h
    have c₂ := n_lt_m hm hn h
    exact m_n_eq hn c₁ c₂ h
  · rw [h.1, h.2]
    conv =>
      enter [1, 1, a]
      rw [show a ^ 5 + a - 1 = (a ^ 2 - a + 1) * (a ^ 3 + a ^ 2 - 1) by ring]
    simp only [dvd_mul_left, and_true]
    exact Set.Ioi_infinite _

end Imo2002Q3
