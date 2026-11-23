import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselTranslateVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstIsotropicVectorCoordinatesNeZeroStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntLocIffValBar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineIdeal

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem exists_dominant {k : ℕ} (f : Fin k → Fv F v) (hf : ∃ j, f j ≠ 0) :
    ∃ j, f j ≠ 0 ∧ ∀ c : Fv F v,
      (∀ i, c * f i ∈ v.adicCompletionIntegers F) ↔ c * f j ∈ v.adicCompletionIntegers F := by
  obtain ⟨j0, hj0⟩ := hf
  haveI : Nonempty (Fin k) := ⟨j0⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖f i‖₊
  refine ⟨j, fun h0 => hj0 ?_, fun c => ⟨fun h => h j, fun h i => ?_⟩⟩
  · have := hj j0
    rw [h0, nnnorm_zero] at this
    exact nnnorm_eq_zero.1 (le_antisymm this zero_le)
  · rw [← nnnorm_le_one_iff_mem] at h ⊢
    rw [nnnorm_mul] at h ⊢
    exact (mul_le_mul_of_nonneg_left (hj i) zero_le).trans h

theorem exists_unit_gen (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {k : ℕ} {u l : Fin k → Fv F v ⊗[F] E}
    (hl : ∑ j, l j * u j = 1) :
    ∃ α : (Fv F v ⊗[F] E)ˣ, ∀ c : Fv F v ⊗[F] E,
      (∀ j, c * u j ∈ intLoc F E v) ↔ ((α⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * c ∈ intLoc F E v := by
  have hne : ∀ ρ : E →ₐ[F] Fv F v, ∃ j, splitProj ρ (u j) ≠ 0 := fun ρ => by
    by_contra hc
    push_neg at hc
    have := congrArg (splitProj ρ) hl
    rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by rw [map_mul, hc j, mul_zero]] at this
    exact zero_ne_one this
  obtain ⟨j1, h1, hj1⟩ := exists_dominant (fun j => splitProj τ (u j)) (hne τ)
  obtain ⟨j2, h2, hj2⟩ := exists_dominant (fun j => splitProj (τ.comp σ) (u j)) (hne _)
  beta_reduce at h1 h2 hj1 hj2
  refine ⟨⟨(splitAlgEquiv h τ).symm ((splitProj τ (u j1))⁻¹, (splitProj (τ.comp σ) (u j2))⁻¹),
    (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)), ?_, ?_⟩, fun c => ?_⟩
  · rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
    exact map_one _
  · show _ ↔ (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)) * c ∈ intLoc F E v
    simp only [mem_intLoc_iff_split h τ, map_mul, splitProj_symm, splitProj_comp_symm, forall_and]
    rw [hj1 (splitProj τ c), hj2 (splitProj (τ.comp σ) c), mul_comm (splitProj τ c),
      mul_comm (splitProj (τ.comp σ) c)]

end Local

set_option maxHeartbeats 1600000 in

theorem exists_unit_mult_latLoc : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D v hτ n L hL g ε hε
  obtain ⟨τ⟩ := hτ
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := D.host.F) (Fv D.host.F v) h1
  let w : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E := g.val *ᵥ fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i
  obtain ⟨l, hl⟩ : ∃ l : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    refine ⟨Pi.single i ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (ε i)⁻¹) ᵥ* (g⁻¹ : GL (Fin n) _).val, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (by simpa using hi)]
    rfl
  let u := Φ.map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ w
  have hl' : ∑ j, (l ᵥ* S.map (inclR (F := D.host.F) (Fv D.host.F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, hl]
  have key : ∀ a : Fv D.host.F v ⊗[D.host.F] D.host.E,
      a • w ∈ latLoc D.host.F L v ↔ ∀ j, a * u j ∈ intLoc D.host.F D.host.E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  obtain ⟨α, hα⟩ := exists_unit_gen (isCMExt_host D) τ hl'
  refine ⟨α, fun c => ?_⟩
  have hcw : g.val *ᵥ (c • fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i) = c • w := Matrix.mulVec_smul _ _ _
  rw [hcw, key, hα]

end GlobalTheory.LineIdeal

end
