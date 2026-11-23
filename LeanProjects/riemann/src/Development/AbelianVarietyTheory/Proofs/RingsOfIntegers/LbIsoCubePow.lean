import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowAdj

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem psum_comp_hom (q : G' ⟶ G) [IsMonHom q] {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : T' ⟶ T) (e : ∀ k, x k ≫ q = h ≫ y k) (I : Finset (Fin n)) :
    psum G' x I ≫ q = h ≫ psum G y I :=
  (Geo.Tor.psum_hom (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b q) x I).trans
    ((congrArg (fun z => psum G z I) (funext e)).trans (Geo.Tor.psum_hom (Geo.Tor.preHom h) y I).symm)

theorem cls_cube_box {j : ℕ} (p : IsPowGrp G' G j) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hb : Geo.Tor.LBIso L' (boxLB L p.pr)) {T' T : Over S} {n : ℕ} (x : Fin n → (T' ⟶ G'))
    (y : Fin n → (T ⟶ G)) (h : Fin j → (T' ⟶ T)) (e : ∀ i k, x k ≫ p.pr i = h i ≫ y k)
    (h₁ : (cubeLB G' x L').IsLB) (h₂ : (cubeLB G y L).IsLB) :
    cls _ h₁ = ∑ i, pull (h i).left (cls _ h₂) := by
  have a := cls_linComb hL' _ _ h₁
  have b := cls_linComb hL _ _ h₂
  have c : cls L' hL' = ∑ i, pull (p.pr i).left (cls L hL) := by
    rw [(cls_eq_iff hL' (LB.isLB_linComb hL _ _)).2 hb, cls_linComb hL]
    simp only [one_smul]
  refine a.trans (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg (pull (h i).left) b.symm))
  simp only [c, map_sum, map_zsmul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun I _ => ?_
  have := p.hom i
  rw [← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, psum_comp_hom (p.pr i) x y (h i) (e i)]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f g : G ⟶ G) (f' g' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → (∀ i, g' ≫ p.pr i = p.pr i ≫ g) → Geo.Tor.LBIso (cubeLB G ![fst G G ≫ f, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ g] L) → Geo.Tor.LBIso (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hb f g f' g' hf hg H
  have i₁ : (cubeLB G ![fst G G ≫ f, snd G G] L).IsLB := LB.isLB_linComb hL _ _
  have i₂ : (cubeLB G ![fst G G, snd G G ≫ g] L).IsLB := LB.isLB_linComb hL _ _
  have i₃ : (cubeLB G' ![fst G' G' ≫ f', snd G' G'] L').IsLB := LB.isLB_linComb hL' _ _
  have i₄ : (cubeLB G' ![fst G' G', snd G' G' ≫ g'] L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff i₃ i₄).1 ?_
  rw [cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hf]) i₃ i₁,
    cls_cube_box p hL hL' hb _ _ (fun i => p.pr i ⊗ₘ p.pr i) (fun i k => by fin_cases k <;> simp [hg]) i₄ i₂,
    (cls_eq_iff i₁ i₂).2 H]

end GlobalTheory.PowAdj
