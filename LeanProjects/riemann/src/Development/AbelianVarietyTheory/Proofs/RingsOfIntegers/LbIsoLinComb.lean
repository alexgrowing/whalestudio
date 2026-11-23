import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PowPrimitive

open Geo.Tor

def chartPullSwap {X X' : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X))
    (φ : K → (X ⟶ X)) (ψ : K → (X' ⟶ X')) (ε : K → ℤ) (hc : ∀ k i, ψ k ≫ F i = F i ≫ φ k) :
    ChartPull (LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε) (LB.LinComb (LB.LinComb L φ ε) F (fun _ => 1)) (𝟙 X') :=
  have le : ∀ j : K → J → L.ι, LB.wchart (LB.LinComb L F (fun _ => 1)) ψ j ≤
      (𝟙 X') ⁻¹ᵁ LB.wchart (LB.LinComb L φ ε) F (fun i k => j k i) :=
    fun j y hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => by
      have h : (ψ k ≫ F i) y ∈ L.U (j k i) := Set.mem_iInter.1 (Set.mem_iInter.1 hy k) i
      rw [hc] at h
      exact h
  { idx := fun j i k => j k i
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 X') y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L φ ε) F (fun _ => 1) (𝟙 X') y _ _ (le j hj) (le j' hj')).symm)
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k)
        (gm_linComb L F (fun _ => 1) (𝟙 X' ≫ ψ k) y (j k) (j' k)
          (Set.mem_iInter.1 hj k) (Set.mem_iInter.1 hj' k))).trans ?_
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ (1 : ℤ))
        (gm_linComb L φ ε (𝟙 X' ≫ F i) y (fun k => j k i) (fun k => j' k i)
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      simp only [zpow_one, Category.id_comp, hc, ← Finset.prod_zpow]
      exact Finset.prod_comm }

theorem lbIso_linComb {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : LBIso (LB.LinComb L φ ε) (LB.LinComb M φ ε) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨LB.linCombIso u φ ε, linCombIso_isGen u hu φ ε⟩

private lemma foldr_padd_comp_eq_comp_foldr_padd {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (h : G' ⟶ G) [IsMonHom h]
    {n : ℕ} (x' : Fin n → (G' ⟶ G')) (x : Fin n → (G ⟶ G)) (hx : ∀ k, x' k ≫ h = h ≫ x k) (l : List (Fin n)) :
    List.foldr (fun k acc => padd G' (x' k) acc) (pzero G' G') l ≫ h =
      h ≫ List.foldr (fun k acc => padd G (x k) acc) (pzero G G) l := by
  induction l with
  | nil =>
    rw [List.foldr_nil, List.foldr_nil, show pzero G' G' = 1 from Over.OverMorphism.ext rfl,
      show pzero G G = 1 from Over.OverMorphism.ext rfl, one_comp, comp_one]
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, show ∀ a b : G' ⟶ G', padd G' a b = a * b from fun _ _ => Over.OverMorphism.ext rfl,
      show ∀ a b : G ⟶ G, padd G a b = a * b from fun _ _ => Over.OverMorphism.ext rfl, mul_comp, comp_mul, hx k, ih]

theorem lbIso_cube_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → Geo.Tor.LBIso L' (boxLB L p.pr) → ∀ (f : G ⟶ G) (f' : G' ⟶ G'), (∀ i, f' ≫ p.pr i = p.pr i ≫ f) → Geo.Tor.LBIso L (cubeLB G ![𝟙 G, f] L) → Geo.Tor.LBIso L' (cubeLB G' ![𝟙 G', f'] L') := by
  intro S G' G _ _ _ _ j p L L' hL hL' hbox f f' hc hprim
  unfold cubeLB boxLB at *
  have hcomm : ∀ (I : ULift.{0} (Finset (Fin 2))) (i : Fin j),
      (psum G' ![𝟙 G', f'] I.down).left ≫ (p.pr i).left = (p.pr i).left ≫ (psum G ![𝟙 G, f] I.down).left := by
    intro I i
    have := p.hom i
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold psum
    refine foldr_padd_comp_eq_comp_foldr_padd (p.pr i) _ _ (fun k => ?_) _
    fin_cases k
    · simp
    · simpa using hc i
  have hP := linComb_isLB _ hL (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hQ := linComb_isLB _ (linComb_isLB _ hL (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have hR := linComb_isLB _ hP (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h1 := lbIso_linComb hbox (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))
  have h3 := lbIso_linComb hprim (fun i => (p.pr i).left) (fun _ => (1 : ℤ))
  have cp := chartPullSwap L (fun i => (p.pr i).left) (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
    (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
    (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)) hcomm
  have h2 : LBIso (LB.LinComb (LB.LinComb L (fun i => (p.pr i).left) (fun _ => (1 : ℤ)))
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum G' ![𝟙 G', f'] I.down).left)
      (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card)))
      (LB.LinComb (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![𝟙 G, f] I.down).left)
        (fun I => (-1 : ℤ) ^ ((Nat.succ 0).succ - I.down.card))) (fun i => (p.pr i).left) (fun _ => (1 : ℤ))) := by
    have hQQ := LBIso.trans hQ hP hQ (LBIso.symm h3) h3
    exact LBIso.chartPull (h := 𝟙 G'.left) cp (chartPullId _) hQQ
  exact LBIso.trans hL' hQ (linComb_isLB _ hL' _ _) (LBIso.trans hL' hP hQ hbox h3)
    (LBIso.trans hQ hR (linComb_isLB _ hL' _ _) (LBIso.symm h2) (LBIso.symm h1))

end GlobalTheory.PowPrimitive
