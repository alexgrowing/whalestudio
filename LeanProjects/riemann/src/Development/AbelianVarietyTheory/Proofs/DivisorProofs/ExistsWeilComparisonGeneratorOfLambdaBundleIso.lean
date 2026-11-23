import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpL

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem exists_cmpGen_of_lbIso (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A)
    (H : LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)
      (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)) :
    ∃ u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂), u.IsGen := by
  obtain ⟨w, hw⟩ := H
  have h₁ := isPart_inl P₁.L P₂.L
  have h₂ := isPart_inr P₁.L P₂.L
  have le : ∀ j : KK → (join P₁.L P₂.L).ι, LB.wchart (join P₁.L P₂.L) (cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂) j ≤
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)).U
        (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => (h₂.mem _ _).1 (Set.mem_iInter.1 hy (.inl k)),
      Set.mem_iInter.2 fun k => (h₁.mem _ _).1 (Set.mem_iInter.1 hy (.inr k))⟩
  let c : ChartPull (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)
      (LB.div (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L)
        (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L)) (𝟙 _) :=
    { idx := fun j => (fun k => (j (.inl k)).2, fun k => (j (.inr k)).1)
      le := le
      g := fun y j j' hj hj' => by
        refine (gm_linComb (join P₁.L P₂.L) _ _ (𝟙 _) y j j' hj hj').trans ?_
        refine Eq.trans ?_ (gm_div _ _ (𝟙 _) y _ _ ⟨le j hj, le j' hj'⟩).symm
        refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹)
          (gm_linComb P₂.L _ _ (𝟙 _) y _ _ (le j hj).1 (le j' hj').1)
          (gm_linComb P₁.L _ _ (𝟙 _) y _ _ (le j hj).2 (le j' hj').2)).symm
        rw [Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
        refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ _) ?_)
          (Finset.prod_congr rfl fun k _ => (zpow_neg _ _).trans (congrArg (fun u => (u ^ _)⁻¹) ?_))
        · refine Eq.trans ?_ (h₂.g _ (𝟙 _ ≫ (psum P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] k.down).left) y _ _
            ((h₂.mem _ _).1 (Set.mem_iInter.1 hj (.inl k))) ((h₂.mem _ _).1 (Set.mem_iInter.1 hj' (.inl k))))
          simp only [cmpφ, Sum.elim_inl, Category.assoc]
        · refine Eq.trans ?_ (h₁.g _ (𝟙 _ ≫ (psum P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] k.down).left) y _ _
            ((h₁.mem _ _).1 (Set.mem_iInter.1 hj (.inr k))) ((h₁.mem _ _).1 (Set.mem_iInter.1 hj' (.inr k))))
          simp only [cmpφ, Sum.elim_inr, Category.assoc] }
  exact ⟨cGen c w, cGen_isGen c hw⟩

end GlobalTheory.Mum.Two.WeilCmp
