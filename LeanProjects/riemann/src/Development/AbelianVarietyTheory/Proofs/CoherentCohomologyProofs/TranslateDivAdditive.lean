import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.TranslateAdditive

noncomputable def chartPullTw {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ε : K → ℤ)
    {φ₀ φ₁ φ₂ : K → (Y ⟶ X)} {A₀ A₁ A₂ : LB Y} (a₀ : ChartPull A₀ (LB.LinComb L φ₀ ε) (𝟙 Y))
    (a₁ : ChartPull A₁ (LB.LinComb L φ₁ ε) (𝟙 Y)) (a₂ : ChartPull A₂ (LB.LinComb L φ₂ ε) (𝟙 Y)) :
    ChartPull (LB.div (tw A₁ A₂ 1) A₀)
      (LB.LinComb L (Sum.elim φ₁ (Sum.elim φ₂ φ₀)) (Sum.elim ε (Sum.elim ε fun k => - ε k))) (𝟙 Y) :=
  have le : ∀ p : (A₁.ι × A₂.ι) × A₀.ι, (LB.div (tw A₁ A₂ 1) A₀).U p ≤
      LB.wchart L (Sum.elim φ₁ (Sum.elim φ₂ φ₀))
        (Sum.elim (a₁.idx p.1.1) (Sum.elim (a₂.idx p.1.2) (a₀.idx p.2))) := fun p y hy =>
    Set.mem_iInter.2 (by
      rintro (k | k | k)
      · exact Set.mem_iInter.1 (a₁.le _ hy.1.1) k
      · exact Set.mem_iInter.1 (a₂.le _ hy.1.2) k
      · exact Set.mem_iInter.1 (a₀.le _ hy.2) k)
  { idx := fun p => Sum.elim (a₁.idx p.1.1) (Sum.elim (a₂.idx p.1.2) (a₀.idx p.2))
    le := le
    g := fun y p q hp hq => by
      refine Eq.trans ?_ (gm_linComb L _ _ (𝟙 Y) y _ _ (le p hp) (le q hq)).symm
      have e₀ := (a₀.g y p.2 q.2 hp.2 hq.2).trans (gm_linComb L φ₀ ε (𝟙 Y) y _ _ (a₀.le _ hp.2) (a₀.le _ hq.2))
      have e₁ := (a₁.g y p.1.1 q.1.1 hp.1.1 hq.1.1).trans
        (gm_linComb L φ₁ ε (𝟙 Y) y _ _ (a₁.le _ hp.1.1) (a₁.le _ hq.1.1))
      have e₂ := (a₂.g y p.1.2 q.1.2 hp.1.2 hq.1.2).trans
        (gm_linComb L φ₂ ε (𝟙 Y) y _ _ (a₂.le _ hp.1.2) (a₂.le _ hq.1.2))
      have e₃ : gm (𝟙 Y) y _ ((pw A₂ (-1)).g p.1.2 q.1.2) = (gm (𝟙 Y) y _ (A₂.g p.1.2 q.1.2)) ^ (-1 : ℤ) :=
        map_zpow _ _ _
      have e₄ := (gm_div (pw A₂ (-1)) A₁ (𝟙 Y) y p.1 q.1 ⟨hp.1, hq.1⟩).trans
        (congrArg₂ (fun a b => a * b⁻¹) e₁ (e₃.trans (congrArg (· ^ (-1 : ℤ)) e₂)))
      refine ((gm_div A₀ (tw A₁ A₂ 1) (𝟙 Y) y p q ⟨hp, hq⟩).trans
        (congrArg₂ (fun a b => a * b⁻¹) e₄ e₀)).trans ?_
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      refine (_root_.mul_assoc _ _ _).trans (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) ?_ ?_))
      · rw [zpow_neg_one, inv_inv]; rfl
      · rw [← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun k _ => (zpow_neg _ _).symm }

theorem exists_gen_additive {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) {T : Over S} (a b c : T ⟶ G) (i : Fin 2 → L.ι)
    (hi : ∀ k (y : T.left), (![a.left, (1 : T ⟶ G).left] k) y ∈ L.U (i k)) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (Sum.elim ![(a * b).left, b.left] (Sum.elim ![(a * c).left, c.left] ![(a * b * c).left, (b * c).left]))
      (Sum.elim ![1, -1] (Sum.elim ![1, -1] fun k => - (![1, -1] : Fin 2 → ℤ) k))), u.IsGen := by
  obtain ⟨w, hw⟩ := GlobalTheory.AbSquare.exists_gen_of_mem_chart hL _ ![-1, 1] i hi
  obtain ⟨u, hu, -⟩ := exists_gen hL
    (φ' := Sum.elim ![(a * b).left, b.left] (Sum.elim ![(a * c).left, c.left] ![(a * b * c).left, (b * c).left]))
    (ε' := fun k => - Sum.elim ![1, -1] (Sum.elim ![1, -1] fun k => - (![1, -1] : Fin 2 → ℤ) k) k) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (prod_cub a b c h))).trans ?_
      apply Additive.ofMul.injective
      simp [Fintype.prod_sum_type, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ w (LB.pullGen L (thφ G (x3 G)) thε t (lift a (lift b c)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hw (DVR.pullGen_isGen _ _ _ _ ht _))
  obtain ⟨v, hv, -⟩ := exists_gen hL (φ' := _) (ε' := _) (fun U _ h => Finset.prod_congr rfl fun k _ => by
    rw [neg_neg]) (LB.invGen L _ _ u) (DVR.invGen_isGen _ _ _ _ hu)
  exact ⟨v, hv⟩

theorem exists_iso_of_cube {S : Scheme.{0}} [Unique S] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    (hL : L.IsLB) (t : LB.Gen (Theta G L)) (ht : t.IsGen) (x : 𝟙_ (Over S) ⟶ G) :
    ∃ w : LB.Iso
      ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull μ[G].left)
      (tw ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull
          (fst G G).left)
        ((LB.LinComb L (K := Fin 2) ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] ![1, -1]).pull
          (snd G G).left) 1), w.IsGen := by
  let χ : Fin 2 → ((𝟙_ (Over S)).left ⟶ G.left) := ![x.left, (1 : 𝟙_ (Over S) ⟶ G).left]
  choose i hi using fun k => exists_chart hL (χ k (default : S))
  have e : ∀ k, (![(toUnit (G ⊗ G) ≫ x).left, (1 : G ⊗ G ⟶ G).left] k) = (toUnit (G ⊗ G)).left ≫ χ k := by
    intro k
    fin_cases k
    · rfl
    · show _ = (toUnit (G ⊗ G) ≫ (1 : 𝟙_ (Over S) ⟶ G)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := exists_gen_additive hL t ht (toUnit (G ⊗ G) ≫ x) (fst G G) (snd G G) i (fun k z => by
    rw [e k]
    have h : (toUnit (G ⊗ G)).left z = (default : S) := Subsingleton.elim (α := S) _ _
    exact (congrArg (fun s => χ k s ∈ L.U (i k)) h).mpr (hi k))
  have key : ∀ b : G ⊗ G ⟶ G, ∀ k, (![((toUnit (G ⊗ G) ≫ x) * b).left, b.left] k) =
      b.left ≫ ![(lift (toUnit G ≫ x) (𝟙 G) ≫ μ[G]).left, 𝟙 G.left] k := by
    intro b k
    fin_cases k
    · show _ = (b ≫ ((toUnit G ≫ x) * 𝟙 G)).left
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]; rfl
    · exact (Category.comp_id _).symm
  have hμ : fst G G * snd G G = μ[G] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  refine gen_chartPull (chartPullTw L _ (chartPullOut L _ _ _ _ fun k => ?_) (chartPullOut L _ _ _ _ (key _))
    (chartPullOut L _ _ _ _ (key _))) u hu
  rw [_root_.mul_assoc, hμ]
  exact key _ k

theorem translate_div_additive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A), ∃ w : LB.Iso ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull μ[P.A].left) (tw ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull (fst P.A P.A).left) ((LB.LinComb P.L (K := Fin 2) ![(lift (toUnit P.A ≫ x) (𝟙 P.A) ≫ μ[P.A]).left, 𝟙 P.A.left] ![1, -1]).pull (snd P.A P.A).left) 1), w.IsGen := by
  intro K _ _ P x
  obtain ⟨t, ht⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_gen _ P P.L P.isLB
  letI : Unique (Spec (CommRingCat.of K)) := inferInstanceAs (Unique (PrimeSpectrum K))
  exact exists_iso_of_cube P.isLB t ht x

end GlobalTheory.TranslateAdditive
