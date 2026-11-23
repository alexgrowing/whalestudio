import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProductTheta

variable {D : D7} {r s p : ℕ}

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.castAdd s i))

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.natAdd r i))

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [rowT, rowB, rowJ]

theorem continuous_rowJ :
    Continuous fun z : Mx D r p × Mx D s p => rowJ z.1 z.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply a).comp continuous_fst)
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply b).comp continuous_snd)

def rowHomeo : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := by simp [rowT_rowJ, rowB_rowJ]
  right_inv y := rowJ_rowT_rowB y
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem rowT_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowT (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowT y) a : Mx D r p) := rfl

theorem rowB_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowB (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowB y) a : Mx D s p) := rfl

theorem pr_split {b : HermE D (r + s)} {br : HermE D r} {bs : HermE D s} (h : IsBlockSL2Embedding b br bs)
    (x y : Mx D (r + s) p) :
    pr b x y = pr br (rowT x) (rowT y) + pr bs (rowB x) (rowB y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext i j
  simp only [pr, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Fin.sum_univ_add, h1, h2, h3, h4,
    map_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rfl

theorem halfTr_add (u v : AE D) : halfTr (u + v) = halfTr u + halfTr v := by
  simp only [halfTr, trA, map_add, mul_add]

theorem npow_half_mul (x : ℝ≥0) (hx : x ≠ 0) :
    npow x ((r : ℂ) / 2) * npow x ((s : ℂ) / 2) = npow x (((r + s : ℕ) : ℂ) / 2) := by
  have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [npow]
  rw [← Complex.cpow_add _ _ hx']
  congr 1
  push_cast
  ring

theorem absA_ne_zero (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem prodTh_of_schwTensor : SchwTensor → ProdTh := by
  intro hT D r s p μr 𝓕r μs 𝓕s hμr hμs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hr hs
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  refine ⟨fun h => hT D θ hθ r s p _ (hr.mem h) _ (hs.mem h), ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowT u.2) : G D p × Mx D r p) :=
      continuous_fst.prodMk (continuous_rowT.comp continuous_snd)
    have c2 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowB u.2) : G D p × Mx D s p) :=
      continuous_fst.prodMk (continuous_rowB.comp continuous_snd)
    exact (hr.cont.comp c1).mul (hs.cont.comp c2)
  · intro C hC
    obtain ⟨Mr, hMr, h1⟩ := hr.maj C hC
    obtain ⟨Ms, hMs, h2⟩ := hs.maj C hC
    refine ⟨_, hT D θ hθ r s p _ hMr _ hMs, fun h hh y => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (h1 h hh _) (h2 h hh _) (norm_nonneg _) (norm_nonneg _)
  · intro g a hg h y
    have e := npow_half_mul (r := r) (s := s) (absA D (Matrix.GeneralLinearGroup.det a)) (absA_ne_zero _)
    rw [hr.levi g a hg h, hs.levi g a hg h, rowT_mul, rowB_mul, ← e]
    simp only [MonoidHom.mul_apply, Circle.coe_mul]
    ring
  · intro g c hg h y
    rw [hr.unip g c hg h, hs.unip g c hg h, pr_split hb, mul_add, Matrix.trace_add, halfTr_add,
      AddChar.map_add_eq_mul]
    ring
  · intro g hg h x
    haveI := hμr.1
    haveI := hμs.1
    haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
    haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
    have hemb : MeasurableEmbedding (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) :=
      (rowHomeo (D := D) (r := r) (s := s) (p := p)).measurableEmbedding
    rw [hemb.integral_map, hr.weyl g hg h, hs.weyl g hg h, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rowT_rowJ, rowB_rowJ, pr_split hb, Matrix.trace_add, map_add, AddChar.map_add_eq_mul]
    ring

end GlobalTheory.CompanionTheory.ThTot.ProductTheta

end
