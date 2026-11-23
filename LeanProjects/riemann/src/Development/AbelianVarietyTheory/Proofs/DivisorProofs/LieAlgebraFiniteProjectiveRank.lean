import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieProj

theorem lie_finite_projective_rank : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)),
    Module.Finite R X.Lie ∧ Module.Projective R X.Lie ∧ ∀ p, Module.rankAtStalk (R := R) X.Lie p = Module.finrank ℚ F := by
  intro F _ _ 𝔠 R _ X
  have hd := X.dim
  haveI : Smooth X.A.hom := hd.smooth
  refine finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie X.rm) (Module.finrank ℚ F) fun p => ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := exists_chart_lieBasis X.A _ hd p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X.rm
    (isGrpPullback_pullback X.A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away X.A X.rm r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end GlobalTheory.LieProj
