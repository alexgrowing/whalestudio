import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerEmbRat

open GlobalTheory.MixModel

private theorem mt_mul_mt_inv' {D : D7} {S : HSp D} (γ : GA D S) : mt S γ * mt S γ⁻¹ = 1 := by
  simp [Formalism.L2.Theta.mt, map_inv]

private theorem actO_mul_mt_one {D : D7} {S T : HSp D} (γ : GA D S) (u : WO S T) :
    actO S T γ 1 (u ⬝ mt S γ) = u := by
  unfold actO
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, mt_mul_mt_inv', Matrix.mul_one]

theorem om_rat_right {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H : IsWeilDatumO ψ S T χS χT om) {γ : GA D S}
    (hγ : γ ∈ GQ S) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) :
    om (γ, 1) f u = f (u ⬝ mt S γ) := by

  have hback : actO S T γ 1 (u ⬝ mt S γ) = u := actO_mul_mt_one γ u
  have key := GlobalTheory.WeilRat.om_rat_actO D ψ H.std S T χS χT om H γ hγ 1 (one_mem _) f hf (u ⬝ mt S γ)
  rwa [hback] at key

theorem rational_unitary_acts_on_thetaRestriction_smaller_alt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ g' ∈ GQ V', ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.emb0 g', 1) f) = ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs d hdC hdB ψ χS χT ω hω χS' χT' ω' hω' μ 𝓨 hμ g' hg' f hf

  have hiso : ∀ y : Mx D W.rank r, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ d.pY := by
    intro y
    subst hdC
    rfl
  have hmid : ∀ x : WO V' W, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x = x ⬝ d.p0 := by
    intro x
    subst hdB
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart, HypDec.p0, HypDec.q0, rat, Matrix.mul_assoc]
    rfl
  have hθ : IsThetaFunO ψ V' W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) :=
    ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ 𝓨 hμ).1 f hf).2.1
  funext x
  rw [om_rat_right hω' hg' hθ x]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res]
  congr 1
  funext y
  rw [om_rat_right hω (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hg') hf, hiso, hmid, hmid, Matrix.add_mul, Matrix.mul_assoc, d.wittDecomp_projY_anisotropicEmbedding,
    Matrix.mul_assoc, d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc]

end GlobalTheory.TowerEmbRat
