import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.UnramDoubleCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
  {ϖ : L} {σ : L →+* L} {q n : ℕ}

def intConj (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict (intL L) fun x => by
    show Valued.v (σ x) ≤ 1
    rw [hσ]; exact x.2

open scoped Valued in

theorem exists_dvd_norm_sub_X (hU : IsUnramInv ϖ σ q) (f : Polynomial (intL L)) (hf : f.Monic)
    (hfc : f.map (intConj hU.2.1) = f) (h0 : IsUnit (f.coeff 0)) :
    ∃ p : Polynomial (intL L), f ∣ p * p.map (intConj hU.2.1) - Polynomial.X := by
  haveI := P.fSatake_nontriv hU
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  obtain ⟨hσσ, hσ, h3, h4, ⟨x, hx1, hx2⟩, hq, hcard⟩ := hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  haveI : IsDiscreteValuationRing A := (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    refine NormIntegers.isAdicComplete_of_fg (C := L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let c : A →+* A := intConj hσ
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal A, c x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X A _ c hc hI hω f hf hfc h0

theorem exists_antiJ_frame (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ h ∈ GLint (Fin n) (intL L), cT σ h.1 * 1 * h.1 = antiJ L n := by
  let c := intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hBι : B.map ι = antiJ L n := by
    refine Matrix.ext fun i j => ?_
    show ι (if i.val + j.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite ι, map_one, map_zero]
  have hB : cT c B = B := by
    refine Matrix.ext fun i j => ?_
    show c (if j.val + i.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite c, map_one, map_zero, add_comm j.val]
  have hBB : B * B = 1 := Matrix.map_injective (f := ι) Subtype.val_injective (by
    show (B * B).map ι = (1 : Matrix _ _ _).map ι
    rw [Matrix.map_mul, hBι, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.map_one _ (map_zero ι) (map_one ι)])
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (exists_dvd_norm_sub_X hU) hB
    (IsUnit.of_mul_eq_one _ hBB)
  have h1 : (B * cT c (Polynomial.aeval B p)) * Polynomial.aeval B p = 1 := by rw [Matrix.mul_assoc, hp, hBB]
  refine ⟨bc ι ⟨Polynomial.aeval B p, _, mul_eq_one_comm.1 h1, h1⟩, ⟨_, rfl⟩, ?_⟩
  show cT σ ((Polynomial.aeval B p).map ι) * 1 * (Polynomial.aeval B p).map ι = _
  rw [Matrix.mul_one, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp, hBι]

theorem doubleCoset_one (hU : IsUnramInv ϖ σ q) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L),
    ∀ h ∈ GLint (Fin n) (intL L), ∀ k ∈ GLint (Fin n) (intL L), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (intL L).subtype (c := intConj hU.2.1) (σ := σ) (fun _ => rfl)
      (fun x => Subtype.ext (hU.1 x)) (exists_dvd_norm_sub_X hU) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hU.2.1 (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2

open GlobalTheory.InertDoubleCoset in

theorem doubleCoset_GU_of_GL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  intro L _ _ _ ϖ σ q n hU g g' a b ha hb e
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := doubleCoset_one hU _
    (conj_mem_UJ σ (inv_frame σ eh) g.2) _ (conj_mem_UJ σ (inv_frame σ eh) g'.2) (h * a * h⁻¹)
    (mul_mem (mul_mem hh ha) (inv_mem hh)) (h * b * h⁻¹) (mul_mem (mul_mem hh hb) (inv_mem hh)) (by rw [e]; group)
  have m : ∀ k ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k' ∈ KU σ n, (k' : GL (Fin n) L) = h⁻¹ * k * h := fun k hk =>
    ⟨⟨_, conj_mem_UJ σ eh hk.1⟩, ⟨conj_mem_UJ σ eh hk.1,
      mul_mem (s := GLint (Fin n) (intL L)) (mul_mem (inv_mem hh) hk.2) hh⟩, rfl⟩
  obtain ⟨l₁, m₁, e₁⟩ := m k₁ h₁
  obtain ⟨l₂, m₂, e₂⟩ := m k₂ h₂
  refine ⟨l₁, m₁, l₂, m₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, e₁, e₂]
  calc (g' : GL (Fin n) L) = h⁻¹ * (h⁻¹⁻¹ * g' * h⁻¹) * h := by group
    _ = _ := by rw [e']; group

end GlobalTheory.UnramDoubleCoset

end
