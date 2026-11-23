import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSection

theorem res_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (a : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : U' ≤ U)
    (e : W ≤ f ⁻¹ᵁ U') (e' : W ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U' W e).hom ((X.presheaf.map (homOfLE h).op).hom a) = (f.appLE U W e').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

noncomputable def prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (t : K → L.Sec) : (LB.LinComb L φ (fun _ => 1)).Sec where
  f jj := ∏ i, ((φ i).appLE _ (LB.wchart L φ jj) (LB.wchart_le L φ jj i)).hom ((t i).f (jj i))
  compat jj jj' := by
    have hg : @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') =
        ∏ i, ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom (L.g (jj i) (jj' i) : Γ(X, _)) := by
      simp only [LB.LinComb, zpow_one, Units.coe_prod]
      rfl
    change (Y.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj)).op).hom (∏ i, _) =
      @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') *
      (Y.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj')).op).hom (∏ i, _)
    rw [hg, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e := congrArg ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom ((t i).compat (jj i) (jj' i))
    rw [map_mul] at e
    refine (res_appLE _ _ _ _).trans (((appLE_res _ _ _ _ _).symm.trans e).trans ?_)
    congr 1
    exact (appLE_res _ _ _ _ _).trans (res_appLE _ _ _ _).symm

theorem mem_basicOpen_prod {Y : Scheme.{0}} {K : Type} [Fintype K] {W : Y.Opens} (a : K → Γ(Y, W))
    {y : Y} (hy : y ∈ W) (h : ∀ i, y ∈ Y.basicOpen (a i)) : y ∈ Y.basicOpen (∏ i, a i) := by
  rw [Scheme.mem_basicOpen _ _ y hy, map_prod]
  exact IsUnit.prod_univ_iff.2 fun i => (Scheme.mem_basicOpen _ _ y hy).1 (h i)

theorem mem_nonzeroLocus_prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (t : K → L.Sec) (y : Y) (h : ∀ i, φ i y ∈ Out.nonzeroLocus (t i)) :
    y ∈ Out.nonzeroLocus (prodSec L φ t) := by
  choose k hk using fun i => TopologicalSpace.Opens.mem_iSup.1 (h i)
  have hy : y ∈ LB.wchart L φ k := Set.mem_iInter.2 fun i => X.basicOpen_le _ (hk i)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_basicOpen_prod _ hy fun i => ?_⟩
  exact (Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ k i) _).ge ⟨hy, hk i⟩

theorem exists_point_powObj {S : Scheme.{0}} (G : Over S) (s : S) :
    ∀ (n : ℕ) (x : Fin n → G.left), (∀ i, G.hom (x i) = s) →
      ∃ y : (Out.powObj G n).left, (Out.powObj G n).hom y = s ∧
        ∀ i, (Out.powPr G i).left y = x i
  | 0, _, _ => ⟨s, rfl, fun i => i.elim0⟩
  | n + 1, x, hx => by
    obtain ⟨z, hz, hz'⟩ := exists_point_powObj G s n (fun i => x i.succ) (fun i => hx _)
    obtain ⟨y, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom)
      (g := (Out.powObj G n).hom) (x 0) z ((hx 0).trans hz.symm)
    refine ⟨y, ?_, fun i => Fin.cases ?_ (fun i => ?_) i⟩
    · change G.hom (pullback.fst G.hom (Out.powObj G n).hom y) = s
      rw [h1, hx]
    · exact h1
    · change (Out.powPr G i).left (pullback.snd G.hom (Out.powObj G n).hom y) = _
      rw [h2, hz']

theorem exists_point {S : Scheme.{0}} {G' G : Over S} {n : ℕ} (pr : Fin n → (G' ⟶ G))
    (lim : IsLimit (Fan.mk G' pr)) (s : S) (x : Fin n → G.left) (hx : ∀ i, G.hom (x i) = s) :
    ∃ y : G'.left, G'.hom y = s ∧ ∀ i, (pr i).left y = x i := by
  obtain ⟨z, hz, hz'⟩ := exists_point_powObj G s n x hx
  let m : Out.powObj G n ⟶ G' := lim.lift (Fan.mk (Out.powObj G n) (Out.powPr G (n := n)))
  have hm : ∀ i, m ≫ pr i = Out.powPr G i := fun i => lim.fac _ ⟨i⟩
  refine ⟨m.left z, ?_, fun i => ?_⟩
  · rw [← Scheme.Hom.comp_apply, Over.w m, hz]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hm, hz']

theorem exists_boxSec : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : Out.IsPowGrp G' G j) (L : LB G.left) (t : Fin j → L.Sec), L.IsLB → ∃ t' : (Out.boxLB L p.pr).Sec, (∀ (jj : Fin j → L.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)), t'.f jj = ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom ((t i).f (jj i))) ∧ ∀ s : S, (∀ i, ∃ x : G.left, G.hom x = s ∧ x ∈ Out.nonzeroLocus (t i)) → ∃ y : G'.left, G'.hom y = s ∧ y ∈ Out.nonzeroLocus t' := by
  intro S G' G _ _ j p L t _
  refine ⟨prodSec L (fun i => (p.pr i).left) t, fun _ _ => rfl, fun s hs => ?_⟩
  choose x hx hx' using hs
  obtain ⟨y, hy, hy'⟩ := exists_point p.pr p.lim s x hx
  exact ⟨y, hy, mem_nonzeroLocus_prodSec L _ t y fun i => (hy' i).symm ▸ hx' i⟩

end GlobalTheory.BoxSection
