import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondColumnsMulBlockDiagonal

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

theorem map_two {γ δ : Type} [MeasurableSpace γ] [MeasurableSpace δ] (c : Measure γ) (e : Measure δ)
    [SFinite c] [SFinite e] (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (c.prod e).map (Prod.map f h) = (r * s) • c.prod e := by
  rw [← Measure.map_prod_map c e hf hh, h1, h2]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul, smul_eq_mul]
  rw [mul_comm]

theorem map_id_prod {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ] (b : Measure β) (X : Measure γ)
    [SFinite b] [SFinite X] (F : γ → γ) (hF : Measurable F) (k : ℝ≥0) (h : X.map F = k • X) :
    (b.prod X).map (Prod.map id F) = k • b.prod X := by
  rw [← Measure.map_prod_map b X measurable_id hF, h, Measure.map_id]
  simp only [ENNReal.smul_def, Measure.prod_smul_right]

theorem map_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (a.prod (b.prod (c.prod e))).map (Prod.map id (Prod.map id (Prod.map f h))) =
      (r * s) • a.prod (b.prod (c.prod e)) := by
  have hm : Measurable (Prod.map f h) := hf.prodMap hh
  exact map_id_prod a _ _ (measurable_id.prodMap hm) _
    (map_id_prod b _ _ hm _ (map_two c e f h hf hh r s h1 h2))

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem zp_tau (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (g : Mx D t t) (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    zp d hn x₀ (h, mm U (bl hn 1 0 0 g), mm y g) =
      ((zp d hn x₀ (h, U, y)).1, mm (zp d hn x₀ (h, U, y)).2 g) := by
  simp only [zp, first_columns_mul_block_diagonal, second_columns_mul_block_diagonal, mm, Matrix.add_mul, Matrix.mul_assoc]

theorem ac_tau (a b : ℕ) (k : GA D B) (z : Mx D B.rank a × Mx D B.rank b) (g : Mx D b b) :
    ac B k (z.1, mm z.2 g) = ((ac B k z).1, mm (ac B k z).2 g) := by
  simp only [ac, mm, Matrix.mul_assoc]

theorem measurable_right (a b : ℕ) (g : Mx D b b) : Measurable (fun y : Mx D a b => mm y g) := by
  obtain ⟨-, -, -, -, h5⟩ := top_mx (D := D) a b
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_id.matrix_mul continuous_const).measurable

theorem nuT_cov : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ g
  obtain ⟨G, hG⟩ := GlobalTheory.CompanionTheory.WzLevi.exists_lv hn g
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBW : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have s1 := hf.1
  have s2 := I.haar
  have s3 := I.probK
  have s4 := hμ
  have hdet := GlobalTheory.CompanionTheory.WzLevi.det_lv hn g G hG
  have hsc1 := map_right t n I.μ₁ hf.1 G
  rw [hdet] at hsc1
  have hsc2 := map_right W.rank t μ hμ g
  have hm1 := measurable_right (D := D) t n G.1
  have hm2 := measurable_right (D := D) W.rank t g.1
  have hτ := map_four I.νK I.m I.μ₁ μ _ _ hm1 hm2 _ _ hsc1 hsc2
  have hτm : Measurable (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
      (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) :=
    measurable_id.prodMap (measurable_id.prodMap (hm1.prodMap hm2))
  have hπ := measurable_pi hn I x₀
  have hT : Measurable (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) :=
    measurable_fst.prodMk ((measurable_right (D := D) B.rank t g.1).comp measurable_snd)
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
          (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) := by
    funext ⟨k, h, U, y⟩
    simp only [Function.comp, Prod.map, id]
    rw [hG, zp_tau, ac_tau]
  unfold nuT
  rw [Measure.map_map hT hπ, hcomp, ← Measure.map_map hπ hτm]
  unfold Q0
  rw [hτ, Measure.map_smul, ← pow_add, add_comm t]

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
