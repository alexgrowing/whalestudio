import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple

open GlobalTheory.MeetsGen CategoryTheory

noncomputable section

namespace GlobalTheory.MeetsUnit

variable {G : Type} [Group G] [Fintype G]

theorem single_mul_cU (U : Subgroup G) [Fintype U] (f : U → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * cU U f = cU U f * MonoidAlgebra.single h 1 := by
  unfold cU
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  have e1 : MonoidAlgebra.single (h * g) (1 : ℂ) = MonoidAlgebra.single h 1 * MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have e2 : MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ) * MonoidAlgebra.single h 1 = MonoidAlgebra.single g⁻¹ 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [Equiv.coe_mulLeft]
  rw [mul_assoc _ (MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ)), e2, e1]
  simp only [mul_assoc]

theorem single_mul_uElt (U : Subgroup G) [Fintype U] (f : U → ℂ) (e : MonoidAlgebra ℂ G)
    (hC : ∀ a, e * a = a * e) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * uElt U f e = uElt U f e * MonoidAlgebra.single h 1 := by
  have hc := single_mul_cU U f h
  have he := hC (MonoidAlgebra.single h 1)
  simp only [uElt, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [he, mul_assoc (cU U f) e, he, ← mul_assoc, ← mul_assoc, hc]

theorem trace_cU (V : FDRep ℂ G) (U : Subgroup G) [Fintype U] (f : U → ℂ) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (cU U f)) =
      (Fintype.card G : ℂ) * ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * V.character u := by
  have hp : Representation.asAlgebraHom V.ρ (pU U f) = ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) • V.ρ u := by
    simp only [pU, map_sum, Representation.asAlgebraHom_single]
  unfold cU
  rw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun g _ => by
    rw [map_mul (Representation.asAlgebraHom V.ρ), map_mul (Representation.asAlgebraHom V.ρ), Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul,
      one_smul, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, map_sum]
  simp only [map_smul, smul_eq_mul, FDRep.character]

def lreg : Representation ℂ G (MonoidAlgebra ℂ G) :=
  (Algebra.lmul ℂ (MonoidAlgebra ℂ G)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem lreg_apply (g : G) (x : MonoidAlgebra ℂ G) : lreg g x = MonoidAlgebra.single g 1 * x := rfl

theorem exists_rightInv_uElt : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ)
    (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) →
    (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 →
      ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) →
    ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  intro G _ _ U _ ψ e hI hC hχ
  classical
  set f : U → ℂ := fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ) with hf
  set w := uElt U f e with hw
  have hinj : Function.Injective (LinearMap.mulLeft ℂ w) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    let K : Submodule ℂ (MonoidAlgebra ℂ G) := LinearMap.ker (LinearMap.mulLeft ℂ w)
    have hK : ∀ x, x ∈ K ↔ w * x = 0 := fun x => LinearMap.mem_ker
    let A : Subrepresentation (lreg (G := G)) := ⟨K, fun g x hx => by
      rw [hK] at hx ⊢
      rw [lreg_apply, ← mul_assoc, ← single_mul_uElt U f e hC g, mul_assoc, hx, mul_zero]⟩
    haveI : Nontrivial A.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.2 (fun hb => hy0 ((Submodule.eq_bot_iff _).1 hb y hy))
    obtain ⟨τ, hτs, φ, hφ, hφ0⟩ := PI.GreenLabelSurjWork.exists_simple_constituent A.toRepresentation
    haveI := hτs
    haveI := PI.CharIdemW.nontrivial_of_simple τ
    have hcomm : ∀ a : MonoidAlgebra ℂ G, (∀ k : G, MonoidAlgebra.single k (1 : ℂ) * a = a * MonoidAlgebra.single k 1) →
        ∀ k : G, τ.ρ k * Representation.asAlgebraHom τ.ρ a = Representation.asAlgebraHom τ.ρ a * τ.ρ k := by
      intro a ha k
      rw [← Representation.asAlgebraHom_single_one, ← map_mul, ← map_mul, ha k]
    obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm w (single_mul_uElt U f e hC))
    obtain ⟨ν, hν⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm e (fun k => hC _ |>.symm))
    have hφw : ∀ x, φ (Representation.asAlgebraHom τ.ρ w x) = 0 := by
      intro x
      rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ w, LinearMap.sum_apply, map_sum]
      simp only [LinearMap.smul_apply, map_smul]
      have h1 : ∀ g, φ (τ.ρ g x) = A.toRepresentation g (φ x) := fun g => LinearMap.congr_fun (hφ g) x
      simp only [h1]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      show ∑ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) = 0
      have h2 : ∀ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) =
          MonoidAlgebra.single g (w.coeff g) * (φ x : MonoidAlgebra ℂ G) := fun g => by
        rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]
      simp only [h2]
      rw [← Finset.sum_mul, GlobalTheory.GoodFactor.sum_single]
      exact (hK _).1 (φ x).2
    have hμ0 : μ = 0 := by
      by_contra h
      apply hφ0
      refine LinearMap.ext fun x => ?_
      have h3 : x = μ⁻¹ • Representation.asAlgebraHom τ.ρ w x := by
        rw [hμ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [h3, map_smul, hφw, smul_zero, LinearMap.zero_apply]
    have h10 : (1 : Module.End ℂ τ) ≠ 0 := one_ne_zero
    have hνν : ν * ν = ν := by
      have h4 : Representation.asAlgebraHom τ.ρ (e * e) = Representation.asAlgebraHom τ.ρ e := by rw [hI]
      rw [map_mul, hν, smul_mul_smul_comm, one_mul] at h4
      exact smul_left_injective ℂ h10 h4
    have hTw : Representation.asAlgebraHom τ.ρ w =
        Representation.asAlgebraHom τ.ρ (cU U f) * Representation.asAlgebraHom τ.ρ e + 1 -
          Representation.asAlgebraHom τ.ρ e := by
      rw [hw, uElt, map_add, map_mul, map_sub, map_one, add_sub_assoc]
    rw [hμ, hμ0, zero_smul, hν] at hTw
    have hν01 : ν * (ν - 1) = 0 := by linear_combination hνν
    rcases mul_eq_zero.mp hν01 with h0 | h0
    · rw [h0, zero_smul, mul_zero, zero_add, sub_zero] at hTw
      exact h10 hTw.symm
    · have hν1 : ν = 1 := sub_eq_zero.mp h0
      rw [hν1, one_smul, mul_one, add_sub_cancel_right] at hTw
      have htr := trace_cU τ U f
      rw [← hTw, map_zero] at htr
      have hirr := GlobalTheory.GoodFactor.isIrrChar_character τ hτs
      have hfix : ∑ g, e.coeff g * τ.character g = τ.character 1 := by
        have h5 : LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ e) = ∑ g, e.coeff g * τ.character g := by
          rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ e, map_sum]
          simp only [map_smul, smul_eq_mul, FDRep.character]
        rw [← h5, hν, hν1, one_smul, FDRep.character, map_one τ.ρ]
      have hne := hχ _ hirr hfix
      have h6 : ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * τ.character u =
          (Fintype.card U : ℂ)⁻¹ * ∑ u : U, τ.character u * f u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [h6] at htr
      have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hU : (Fintype.card U : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact mul_ne_zero hG (mul_ne_zero hU hne) htr.symm
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj 1
  exact ⟨v, hv⟩

end GlobalTheory.MeetsUnit
