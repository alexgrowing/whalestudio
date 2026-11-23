import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

lemma res_res_pull {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem triv_pull_of_isPullGen : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ), IsPullGen p M e → Triv (M.pull p) := by
  intro X Y p M e he
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit) (e (j PUnit.unit))⟩, fun i j => ?_⟩
  have gg : (M.pull p).g i j = res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
      (pullU p _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
    (Fintype.prod_unique (fun k : PUnit => (res (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i k))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j k)))
      (pullU p _ (M.g (i k) (j k)))) ^ (1 : ℤ))).trans (zpow_one _)
  rw [gg]
  have h := he (i PUnit.unit) (j PUnit.unit) (LB.wchart M (fun _ : PUnit => p) i ⊓ LB.wchart M (fun _ : PUnit => p) j)
    (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
    (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit))
    (le_inf (inf_le_left.trans (LB.wchart_le M (fun _ : PUnit => p) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le M (fun _ : PUnit => p) j PUnit.unit)))
  refine (res_res_pull _ _ _).trans (h.trans ?_)
  exact congrArg _ (res_res_pull _ _ _).symm

end GlobalTheory.CharKer
