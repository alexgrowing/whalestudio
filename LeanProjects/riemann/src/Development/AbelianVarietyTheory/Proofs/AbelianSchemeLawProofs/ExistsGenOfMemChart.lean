import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbSquare

theorem exists_gen_of_mem_chart {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i : K → L.ι) (hi : ∀ k (y : Y), φ k y ∈ L.U (i k)) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have hm : ∀ y : Y, y ∈ LB.wchart L φ i := fun y => Set.mem_iInter.2 fun k => hi k y
  have le : ∀ j : K → L.ι, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ i :=
    fun j y hy => ⟨hy, hm y⟩
  have v : ∀ (j : K → L.ι) (y : Y), y ∈ LB.wchart L φ j →
      gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j i)) = trF φ ε (𝟙 Y) y j i :=
    fun j y hy => (gm_res (𝟙 Y) y (le j) hy _).trans (gm_linComb L φ ε (𝟙 Y) y j i hy (hm y))
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j i)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j y hy.1)).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2)
      ((gm_res (𝟙 Y) y _ hy _).trans (v j' y hy.2))).trans ?_)))
  exact trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hm y)

theorem exists_gen_square {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S} (a b c : T ⟶ G) (i : Fin 4 → L.ι)
    (hi : ∀ k (y : T.left), (![(a * b).left, a.left, b.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 4) ![(a * b * c).left, c.left, (a * c).left, (b * c).left]
      ![1, 1, -1, -1]), u.IsGen := by
  obtain ⟨w, hw⟩ := exists_gen_of_mem_chart hL _ ![1, -1, -1, 1] i hi
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := ![(a * b * c).left, c.left, (a * c).left, (b * c).left])
    (ε' := ![1, 1, -1, -1]) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub a b c h))).trans ?_
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ w (LB.pullGen L (thφ G (x3 G)) thε t (lift a (lift b c)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ ht _))
  exact ⟨u, hu⟩

theorem square_local {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) (T : Over S) (x y : T ⟶ G) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb L (K := Fin 4)
      ![(translPt G (x * y)).left, (snd T G).left, (translPt G x).left, (translPt G y).left]
      ![1, 1, -1, -1]).pull ((fst T G).left ⁻¹ᵁ V).ι), c.IsGen := by
  let χ : Fin 4 → (T.left ⟶ G.left) := ![(x * y).left, x.left, y.left, (1 : T ⟶ G).left]
  choose i hi using fun k => exists_chart hL (χ k p)
  refine ⟨LB.wchart L χ i, Set.mem_iInter.2 hi, ?_⟩
  let W := (fst T G).left ⁻¹ᵁ LB.wchart L χ i
  let ρ : overRes (T := T ⊗ G) W ⟶ T ⊗ G := overResι W
  have e : ∀ k, (![((ρ ≫ fst T G ≫ x) * (ρ ≫ fst T G ≫ y)).left, (ρ ≫ fst T G ≫ x).left,
      (ρ ≫ fst T G ≫ y).left, (1 : overRes (T := T ⊗ G) W ⟶ G).left] k) = W.ι ≫ (fst T G).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (ρ ≫ fst T G ≫ (x * y)).left
      rw [MonObj.comp_mul, MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (ρ ≫ fst T G ≫ (1 : T ⟶ G)).left
      rw [MonObj.comp_one, MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := exists_gen_square hL t ht (ρ ≫ fst T G ≫ x) (ρ ≫ fst T G ≫ y) (ρ ≫ snd T G) i
    (fun k z => by
      rw [e k]
      exact Set.mem_iInter.1 z.2 k)
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) u hu
  have tr : ∀ w : T ⟶ G, (ρ ≫ fst T G ≫ w) * (ρ ≫ snd T G) = ρ ≫ translPt G w := fun w =>
    (MonObj.comp_mul ρ (fst T G ≫ w) (snd T G)).symm
  fin_cases k
  · show _ = (ρ ≫ translPt G (x * y)).left
    rw [← tr, MonObj.comp_mul, MonObj.comp_mul]; rfl
  · rfl
  · exact congrArg (fun q => q.left) (tr x)
  · exact congrArg (fun q => q.left) (tr y)

theorem square_of_cube :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left),
      ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4)
        ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left]
        ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ∧ SquareSt := by
  intro h
  have key : ∀ (S : Scheme.{0}) (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) (p : T.left),
      ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 4)
        ![(translPt P.A (x * y)).left, (snd T P.A).left, (translPt P.A x).left, (translPt P.A y).left]
        ![1, 1, -1, -1]).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen := by
    intro S P T x y p
    obtain ⟨t, ht⟩ := h S P P.L P.isLB
    exact square_local P.isLB t ht T x y p
  exact ⟨key, fun S _ P T x y p => key S P T x y p⟩

end GlobalTheory.AbSquare
