import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
import Mathlib.NumberTheory.Padics.ProperSpace

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.qzEnd :
    ∀ (l : ℕ) [Fact l.Prime] (f : QZ l →ₗ[ℤ_[l]] QZ l), ∃ c : ℤ_[l], ∀ x, f x = c • x := by
  intro l _ f
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hz : ∀ q : ℚ_[l], QZ.mk l q = 0 ↔ ‖q‖ ≤ 1 := by
    intro q
    show (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro h
      exact ⟨⟨q, h⟩, rfl⟩
  set x : ℕ → QZ l := fun k => QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) with hx
  have hA : ∀ (c : ℤ_[l]) (k : ℕ), c • x k = 0 ↔ ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro c k
    show QZ.mk l ((c : ℚ_[l]) * ((l : ℚ_[l]) ^ k)⁻¹) = 0 ↔ _
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) := by positivity
    rw [hz, norm_mul, norm_inv, Padic.norm_p_pow, mul_inv_le_iff₀ hpos, one_mul]
    exact Iff.rfl
  have hC : ∀ (k : ℕ) (y : QZ l), (l ^ k) • y = 0 → ∃ a : ℤ_[l], y = a • x k := by
    intro k y hy
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) y
    have h1 : QZ.mk l ((l : ℚ_[l]) ^ k * q) = 0 := by
      rw [← hy]
      show _ = (Submodule.Quotient.mk ((l ^ k) • q) : ℚ_[l] ⧸ ZlSub l)
      rw [nsmul_eq_mul]
      push_cast
      rfl
    rw [hz] at h1
    refine ⟨⟨(l : ℚ_[l]) ^ k * q, h1⟩, ?_⟩
    show QZ.mk l q = QZ.mk l (((l : ℚ_[l]) ^ k * q) * ((l : ℚ_[l]) ^ k)⁻¹)
    congr 1
    field_simp
  have hstep : ∀ k, x k = (l : ℤ_[l]) • x (k + 1) := by
    intro k
    show QZ.mk l (((l : ℚ_[l]) ^ k)⁻¹) = QZ.mk l ((l : ℚ_[l]) * ((l : ℚ_[l]) ^ (k + 1))⁻¹)
    congr 1
    rw [pow_succ]
    field_simp
  have hkill : ∀ k, (l ^ k) • x k = 0 := by
    intro k
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], hA]
    push_cast
    rw [PadicInt.norm_p_pow]
  have hex : ∀ k, ∃ a : ℤ_[l], f (x k) = a • x k := by
    intro k
    apply hC
    rw [← map_nsmul, hkill, map_zero]
  choose a ha using hex
  have hdiff : ∀ k, ‖a (k + 1) - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    rw [← hA, sub_smul, sub_eq_zero, ← ha k, hstep k, map_smul, ha (k + 1)]
    exact smul_comm _ _ _
  have hr : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hcs : CauchySeq a := by
    refine cauchySeq_of_le_geometric ((l : ℝ)⁻¹) 1 hr (fun n => ?_)
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact hdiff n
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
  have hmono : ∀ k m, k ≤ m → ‖a m - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
      rw [sub_self, norm_zero]
      positivity
    | succ m hkm ih =>
      have := PadicInt.nonarchimedean (a (m + 1) - a m) (a m - a k)
      rw [sub_add_sub_cancel] at this
      refine this.trans (max_le ((hdiff m).trans ?_) ih)
      exact zpow_le_zpow_right₀ hl.le (by omega)
  have hck : ∀ k, ‖c - a k‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
    intro k
    have ht : Filter.Tendsto (fun m => ‖a m - a k‖) Filter.atTop (nhds ‖c - a k‖) :=
      (hc.sub_const (a k)).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨k, fun m hm => hmono k m hm⟩)
  have hfx : ∀ k, f (x k) = c • x k := by
    intro k
    have := (hA (c - a k) k).2 (hck k)
    rw [sub_smul, sub_eq_zero] at this
    rw [this, ha k]
  refine ⟨c, fun y => ?_⟩
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 y
  obtain ⟨b, rfl⟩ := hC k y hk
  rw [map_smul, hfx, smul_comm]
