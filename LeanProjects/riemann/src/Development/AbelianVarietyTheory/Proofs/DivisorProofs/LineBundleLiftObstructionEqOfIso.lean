import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesCohomologous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfCohomologousStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObsUniq

theorem obAt_eq_of_iso : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (C : Type) [Category.{0} C] (G : C ⥤ AffOp X₀) (d d' : GlobalTheory.CatCoh.H2 (ext R₁ (G ⋙ OAff s₀))), L.IsLB → L'.IsLB → LBIso L L' → ObAt S α L G d → ObAt S α L' G d' → d = d' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' C _ G d d' hL hL' e hd hd'
  obtain ⟨u, hu, hobs⟩ := hd
  obtain ⟨u', hu', hobs'⟩ := hd'
  obtain ⟨t, ht⟩ := GlobalTheory.FrameCob.frames_cohomologous X₀ C (opOf G) (opOf_le G) L L' u u' hL hL' e hu hu'
  refine GlobalTheory.T.lineBundleLiftObstruction_eq_of_cohomologous R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u u' t d d'
    ((ofSys_isFun S).restrict G) (fun T T' a ↦ ?_) hobs hobs'
  have := congrArg (fun w : Γ(X₀, opOf G T')ˣ ↦ (w : Γ(X₀, opOf G T'))) (ht T T' a)
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LBObsUniq
