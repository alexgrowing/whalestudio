import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharactersStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem halfMod_eq_detPow {D : D7} {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := rfl

theorem halfMod_rank_zero {D : D7} (n : ℕ) (a : GL (Fin 0) (AE D)) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, Subsingleton.elim a 1, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem wittDecomposition_levi_emb_acts_isotropic {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.e.map (incA D) = d.e.map (incA D) ⬝ a.1 := by
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]

theorem wittDecomposition_levi_emb_acts_anisotropicCore {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.i₀.map (incA D) = d.i₀.map (incA D) ⬝ mt S₀ g := by
  have e2 : d.i₀.map (incA D) = d.j0 := rfl
  rw [e2, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]

theorem heisO_extX_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ)
    (f : WO S T → ℂ) : heisO ψ S T (d.extX T 0) f = f := by
  funext w
  simp only [heisO, map_zero, add_zero, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem levi_origin_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨hz, -, hl⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, -, -, hiso⟩ := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hom.std
    refine ⟨1, 1, continuous_const, fun _ => rfl, continuous_const, fun _ _ => rfl, fun a g f hf => ?_⟩
    rw [hz S S₀ T d μ 𝓕 hμ, hz S S₀ T d μ 𝓕 hμ, (hl S S₀ d).1, one_mul, hiso χS χT om om₀ hom hom₀ g 1 f hf,
      halfMod_rank_zero]
    simp
  · obtain ⟨hsp, hr, -, -, -, hm, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    obtain ⟨α, ξ, hα, hξ, h⟩ := GlobalTheory.T.leviFactor_scalars_automorphicCharacters D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT om hom χS χT om₀ hom₀
    refine ⟨α, ξ, hα.1, hα.2, hξ.1, hξ.2, fun a g f hf => ?_⟩
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hr]; exact hμ
    rw [hm, hm, heisO_extX_zero, heisO_extX_zero, halfMod_eq_detPow]
    exact h μ 𝓕 hμ' a g (d.levi a * d.emb0 g) (wittDecomposition_levi_emb_acts_isotropic d a g) (wittDecomposition_levi_emb_acts_anisotropicCore d a g) f hf

end GlobalTheory.Unf
