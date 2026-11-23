import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegUniq

theorem eq_of_siegPB : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0})
    (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' →
    SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  intro g n _ _ _ F S s' c f f' hf hf' h₁ h₂
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  haveI : IsLocalRing (S.presheaf.stalk x) := inferInstance
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (Sp (S.presheaf.stalk x)) s'
    (S.fromSpecStalk x ≫ s') (S.fromSpecStalk x) c rfl).1
  have e : (S.fromSpecStalk x ≫ f) ≫ F.s = (S.fromSpecStalk x ≫ f') ≫ F.s := by
    simp only [Category.assoc, hf, hf']
  exact @SFam.inj g n _ _ _ F (S.presheaf.stalk x) _ this (S.fromSpecStalk x ≫ f) (S.fromSpecStalk x ≫ f') (S.fromSpecStalk x ≫ s') c' e
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

end GlobalTheory.SiegUniq
end
