import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHomIffLinEnd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTransport

section Nest

variable {X X' Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (X' ⟶ X)} {ε : K → ℤ} {p : Y ⟶ X'}

theorem trF_nest (r : Z ⟶ Y) (z : Z) (j j' : PUnit.{1} → K → L.ι)
    (hj : (r ≫ p) z ∈ LB.wchart L φ (j PUnit.unit)) (hj' : (r ≫ p) z ∈ LB.wchart L φ (j' PUnit.unit)) :
    trF (L := LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1) r z j j' =
      trF (fun k => p ≫ φ k) (fun k => - ε k) r z (j PUnit.unit) (j' PUnit.unit) := by
  unfold trF
  refine (Fintype.prod_unique _).trans ?_
  refine (zpow_neg_one _).trans ?_
  refine (congrArg (·⁻¹) (gm_linComb L φ ε (r ≫ p) z _ _ hj hj')).trans ?_
  simp only [← Finset.prod_inv_distrib, zpow_neg, Category.assoc]

theorem mem_nest {y : Y} {j : PUnit.{1} → K → L.ι} :
    y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) j ↔
      y ∈ LB.wchart L (fun k => p ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h PUnit.unit) k,
    fun h => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩

theorem exists_nest (t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k))) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) =
          gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) := by
  refine ⟨⟨fun j => res (fun _ hy => mem_nest.1 hy) (t.s (j PUnit.unit))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ (mem_nest.2 hj) _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ht (𝟙 Y) y (mem_nest.1 hj) (mem_nest.1 hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y j j' (Set.mem_iInter.1 hj PUnit.unit)
      (Set.mem_iInter.1 hj' PUnit.unit)).symm (gm_res _ y _ hj' _).symm))

theorem exists_unnest (a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)))
    (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) =
          gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) := by
  have mk : ∀ {y : Y} {j : K → L.ι}, y ∈ LB.wchart L (fun k => p ≫ φ k) j →
      y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j) := fun h => mem_nest.2 h
  refine ⟨⟨fun j => res (fun _ hy => mk hy) (a.s fun _ => j)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ha (𝟙 Y) y (mk hj) (mk hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y (fun _ => j) (fun _ => j') (Set.mem_iInter.1 (mk hj) PUnit.unit)
      (Set.mem_iInter.1 (mk hj') PUnit.unit)) (gm_res _ y _ hj' _).symm))

end Nest

open GlobalTheory.PrimCocycle in

theorem prod_neg_lam {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B)
    {U : Type} [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ I, k ((lift x y).left ≫ lamφ B I) ^ (- lamε I) = ∏ i, k (lamPts x y i) ^ negε i := by
  have a := prod_lam x y (fun q => (k q)⁻¹)
  have b := Wit.prod_neg_lamPts x y (fun q => (k q)⁻¹)
  simp only [inv_inv, Category.id_comp] at a b
  rw [b, ← a]
  simp only [zpow_neg, inv_zpow]

open GlobalTheory.PrimCocycle in

theorem gen_transport : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  intro SB SC B _ _ C _ _ M N hM hN m w hw T T₀ x y x₀ y₀ h hm t₀ ht₀
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen hN (φ' := fun I => (lift x₀ y₀).left ≫ lamφ C I) (ε' := fun I => - lamε I)
    (fun U _ k => (prod_neg_lam x₀ y₀ k).symm) t₀ ht₀
  obtain ⟨t₂, h₂, v₂⟩ := exists_nest t₁ h₁
  obtain ⟨t₃, h₃, v₃⟩ := DegPull.exists_pmaps (L := abelian₂ C N) (L' := abelian₂ B M) ((isGen_iff w).1 hw) lN lM
    (φ' := fun _ : PUnit.{1} => (lift x y).left) h (fun _ => hm) t₂ h₂
  obtain ⟨t₄, h₄, v₄⟩ := exists_unnest (L := M) (φ := lamφ B) (ε := lamε) t₃ h₃
  obtain ⟨u, hu, vu⟩ := exists_gen hM (fun U _ k => prod_neg_lam x y k) t₄ h₄
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  have e : ∀ I, (r ≫ h) ≫ (lift x₀ y₀).left ≫ lamφ C I = (r ≫ (lift x y).left) ≫ m ≫ lamφ C I := fun I => by
    rw [Category.assoc, Category.assoc, ← Category.assoc h, ← hm, Category.assoc]
  have E := v₃ Z r z (fun _ I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (fun _ => Set.mem_iInter.2 fun I => hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ => Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [Fintype.prod_unique, zpow_neg_one] at E
  have a := v₂ Z (r ≫ h) z (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (Set.mem_iInter.2 fun I => by
    have := hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)
    have e' := congrArg (fun q : Z ⟶ C.left => q z) (e I)
    exact (congrArg (· ∈ N.U _) e').mpr this)
  have b := v₄ Z r z (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [vu Z r z J' hJ', ← v₁ Z (r ≫ h) z J hJ,
    val_of t₄ r z J' (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I)) (fun I => by rw [Category.assoc]),
    val_of t₁ (r ≫ h) z J (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (fun I => by rw [e]), b, ← a]
  exact (mul_inv_cancel_left _ _).symm.trans (congrArg (_ * ·) E.symm)

end GlobalTheory.GenTransport

end
