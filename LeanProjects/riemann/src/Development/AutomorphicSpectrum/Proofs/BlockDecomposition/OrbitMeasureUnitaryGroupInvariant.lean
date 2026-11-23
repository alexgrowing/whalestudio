import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.InvU

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem ac_mul (V : HSp D) {a b : ℕ} (g h : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V (g * h) z = ac V g (ac V h z) := by
  simp only [ac, mm, mt_mul, Matrix.mul_assoc]

theorem measurable_ac (V : HSp D) {a b : ℕ} (g : GA D V) :
    Measurable (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) V.rank a b
  have o1 : OpensMeasurableSpace (Mx D V.rank a × Mx D V.rank b) := g1.opensMeasurable
  have hc : Continuous (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) :=
    (continuous_ac V).comp (continuous_const.prodMk continuous_id)
  exact hc.measurable

theorem rho_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    rho hn I μ x₀ A = Q0 I μ (zp d hn x₀ ⁻¹' A) :=
  Measure.map_apply (measurable_zp d hn x₀) hA

def sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (A : Set (Mx D B.rank W.rank × Mx D B.rank t)) (x : GA D B) : ℝ≥0∞ :=
  rho hn I μ x₀ {z | ac B x⁻¹ z ∈ A}

theorem measurable_sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) : Measurable (sA hn I μ x₀ A) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oB : OpensMeasurableSpace (GA D B) := hB.opensMeasurable
  have e1 : SecondCountableTopologyEither (GA D B) (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (GA D B × Par D n t W) := Prod.opensMeasurableSpace
  have := sigmaFinite_parameter_product_measure I μ hμ
  have hc : Continuous fun p : GA D B × Par D n t W => ac B p.1⁻¹ (zp d hn x₀ p.2) :=
    (continuous_ac B).comp ((continuous_fst.inv).prodMk ((continuous_zp d hn x₀).comp continuous_snd))
  have hS : MeasurableSet {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A} := hc.measurable hA
  have key := measurable_measure_prodMk_left (ν := Q0 I μ) hS
  have e : sA hn I μ x₀ A = fun x => Q0 I μ (Prod.mk x ⁻¹' {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A}) := by
    funext x
    exact rho_apply hn I μ x₀ (measurable_ac B x⁻¹ hA)
  rw [e]
  exact key

theorem sA_stab (hL : Law) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) (q : GlobalTheory.RegSW.stab d) (x : GA D B) :
    sA hn I μ x₀ A (q * x) = ((GlobalTheory.RegSW.absDet d q ^ (W.rank + t) : ℝ≥0) : ℝ≥0∞) * sA hn I μ x₀ A x := by
  have hA' : MeasurableSet {z | ac B x⁻¹ z ∈ A} := measurable_ac B x⁻¹ hA
  have h1 := congrArg (fun ν : Measure _ => ν {z | ac B x⁻¹ z ∈ A}) (hL D n t B W d hn I μ hμ x₀ q⁻¹)
  beta_reduce at h1
  rw [Measure.map_apply (measurable_ac B _) hA'] at h1
  have e : sA hn I μ x₀ A (q * x) = rho hn I μ x₀ (ac B ((q⁻¹ : GlobalTheory.RegSW.stab d) : GA D B) ⁻¹' {z | ac B x⁻¹ z ∈ A}) := by
    unfold sA
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, Subgroup.coe_inv]
  rw [e, h1, map_inv, inv_inv]
  rfl

theorem nuT_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    nuT hn I μ x₀ A = ∫⁻ k : I.l.K, sA hn I μ x₀ A (k : GA D B) ∂I.νK := by
  have := sigmaFinite_parameter_product_measure I μ hμ
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hA, Measure.prod_apply (measurable_pi hn I x₀ hA)]
  refine lintegral_congr fun k => ?_
  exact (rho_apply hn I μ x₀ (measurable_ac B (k : GA D B)⁻¹ hA)).symm

theorem nuT_map_ac (hQ : QK) (hL : Law) (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) (x₀) (h : GA D B) :
    (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  change (nuT hn I μ x₀).map (ac B h) = nuT hn I μ x₀
  refine Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (ac B h ⁻¹' A) := measurable_ac B h hA
  rw [Measure.map_apply (measurable_ac B h) hA, nuT_apply hn I μ hμ x₀ hA', nuT_apply hn I μ hμ x₀ hA]
  have key := hQ D t B W d I.l I.good I.νK I.haarK (sA hn I μ x₀ A) (measurable_sA hn I μ hμ x₀ hA)
    (fun q x => sA_stab hL hn I μ hμ x₀ hA q x) h⁻¹
  rw [← key]
  refine lintegral_congr fun k => ?_
  unfold sA
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, inv_inv]

end GlobalTheory.CompanionTheory.ColumnSplitting.InvU

end
