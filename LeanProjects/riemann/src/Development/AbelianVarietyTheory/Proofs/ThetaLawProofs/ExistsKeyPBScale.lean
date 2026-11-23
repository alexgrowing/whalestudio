import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyScaleLift

theorem exists_keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (x : KeyIn R') (a : Rˣ) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), KeyPB x y f → IsUnit M.det → ∃ y₁ : KeyIn R, ∀ (t : x.P.L.Sec) (ht : _) (v : Fin x.P.g → (epsR R' ⟶ x.P.A)) (hv : _), (∀ i, t.f i = constFn x.P.A.hom _ (f a) * x.th.f i) → (∀ i, IsLieComb (fun k => f (M i k)) x.v (v i)) → KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v, hv⟩ y₁ f := by
  intro R R' _ _ f y x a M h hM
  obtain ⟨e⟩ : Nonempty (x.P.g = y.P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := h
    exact ⟨hg⟩
  haveI := y.P.isAb.comm
  let N : Matrix (Fin y.P.g) (Fin y.P.g) R := Matrix.reindex (finCongr e) (finCongr e) M
  have hN : IsUnit N.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra R y.P.A y.P.g y.v y.basis.1
  choose v₁ hv₁ using fun i => (ex (N i)).exists
  obtain ⟨s, hs, -, hle⟩ := exists_sec_div y.P.A.hom a.inv_mul y.th
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, s, fun p => (y.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁,
    (bas N v₁ y.basis hv₁).2 hN⟩, fun t ht v hv h₁ h₂ => ?_⟩
  exact KeyPBScale.keyPB_scale R R' f y.P y.g_pos y.rig y.rig_gen y.th y.th_ne y.v y.basis s _ v₁ _ a N x.P e
    x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis t ht v hv hs hv₁ h₁ h₂ h

end GlobalTheory.KeyScaleLift
end
