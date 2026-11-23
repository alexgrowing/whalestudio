import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSA

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem adj_smul (e : AE D) (x : Mx D a b) : adj (e • x) = cA D e • adj x := by
  ext i j
  show cA D (e * x j i) = cA D e * cA D (x j i)
  exact map_mul _ _ _

theorem ip_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem yv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem qv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, yv_smul he, ip_smul he, pr_smul he, smul_sub]

theorem continuous_ip (V : HSp D) : Continuous fun p : Mx D V.rank a × Mx D V.rank b => ip V p.1 p.2 := by
  show Continuous fun p : Mx D V.rank a × Mx D V.rank b => adj p.1 * (gA V * p.2)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd)

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) :
    Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => rat b₀.1⁻¹ * ip V z.1 z.2
  exact continuous_const.matrix_mul (continuous_ip V)

theorem isClosed_qv (V : HSp D) (b₀ : HermE D r) :
    IsClosed {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} := by
  have hy := continuous_yv (t := t) V b₀
  have h1 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.2 * (gA V * z.2)
    exact (continuous_adj.comp continuous_snd).matrix_mul (continuous_const.matrix_mul continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj (yv V b₀ z) * ((b₀.1.map (incA D)) * yv V b₀ z)
    exact (continuous_adj.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have e : {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} =
      {z | ip V z.2 z.2 = pr b₀ (yv V b₀ z) (yv V b₀ z)} := Set.ext fun z => sub_eq_zero
  rw [e]
  exact isClosed_eq h1 h2

theorem map_transport {X : Type*} [MeasurableSpace X] {ν : Measure X} {A : Set X} (hA : MeasurableSet A)
    {f φ ψ : X → X} (hf : Measurable f) (hφ : Measurable φ) (hψ : Measurable ψ) (hA' : φ ⁻¹' A = A)
    (hc : ∀ z, ψ (f z) = f (φ z)) {κ : ℝ≥0} (hν : ν.map φ = κ • ν) :
    ((ν.restrict A).map f).map ψ = κ • (ν.restrict A).map f := by
  have h1 : (ν.restrict A).map φ = κ • ν.restrict A := by
    conv_lhs => rw [← hA']
    rw [← Measure.restrict_map hφ hA, hν, Measure.restrict_smul]
  rw [Measure.map_map hψ hf, show ψ ∘ f = f ∘ φ from funext hc, ← Measure.map_map hf hφ, h1, Measure.map_smul]

end PositivityTheory.Rg.Rsw.L.LToS

end
