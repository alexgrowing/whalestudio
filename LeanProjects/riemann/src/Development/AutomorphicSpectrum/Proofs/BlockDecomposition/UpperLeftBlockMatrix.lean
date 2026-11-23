import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalThetaIntegralSiegelRuleDoubledWeil
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
namespace GlobalTheory.CompanionTheory.IwaAd
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
variable {D : D7} {n : ℕ}

theorem npow_mul' {r h : ℝ≥0} (t : ℂ) : npow (r * h) t = npow r t * npow h t := by
  simp only [npow, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg r.2 h.2 t

theorem npow_inv' {r : ℝ≥0} (hr : 0 < r) (t : ℂ) : npow r⁻¹ t = npow r (-t) := by
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  rw [npow_eq_exp hr', npow_eq_exp hr]
  congr 1
  rw [NNReal.coe_inv, Real.log_inv]
  push_cast
  ring

theorem npow_add' {r : ℝ≥0} (hr : 0 < r) (s t : ℂ) : npow r (s + t) = npow r s * npow r t := by
  rw [npow_eq_exp hr, npow_eq_exp hr, npow_eq_exp hr, ← Complex.exp_add]
  congr 1
  ring

theorem npow_zero' (r : ℝ≥0) (hr : 0 < r) : npow r 0 = 1 := by
  rw [npow_eq_exp hr]; simp

theorem upperLeft_blockMatrix {R : Type} (x y z t : Matrix (Fin n) (Fin n) R) : blkA (blk4 x y z t) = x := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem det_ad (a : GL (Fin n) (AE D)) :
    (Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) =
      conjUnit (R := AF D.host.F) D.sp.cm.sig (Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) := by
  apply Units.ext
  have h1 : ((Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) : AE D) = (adj (a⁻¹).1 : Mx D n n).det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  have h2 : (adj (a⁻¹).1 : Mx D n n).det = cA D ((a⁻¹).1.det) := by
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (cA D) _).symm
  have h3 : ((Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det :=
    Matrix.GeneralLinearGroup.val_det_apply _
  rw [h1, h2, ← h3]
  rfl
theorem absA_ad (a : GL (Fin n) (AE D)) : absA D (Matrix.GeneralLinearGroup.det (ad a)) =
    (absA D (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rw [det_ad, GlobalTheory.DiagThetaRule.absA_conj, map_inv, map_inv]

theorem exists_ad (a : GL (Fin n) (AE D)) : ∃ m' ∈ P D n, mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
  obtain ⟨m', hm'⟩ := exists_levi (ad a)
  obtain ⟨m'', hm''⟩ := exists_levi (ad a)⁻¹
  have e1 : mat m' = blk4 (adj (a⁻¹).1) 0 0 a.1 := by
    rw [hm']
    have : (adj ((ad a)⁻¹).1 : Mx D n n) = a.1 := adj_adj _
    rw [this]
    rfl
  have h1 : m'' * m' = 1 := mat_inj (by
    rw [mat_mul, mat_one, hm', hm'']
    have := levi_mul_inv (D := D) (ad a)⁻¹
    rwa [inv_inv] at this)
  exact ⟨m', levi_mem_P hm' hm'' h1, e1⟩

theorem gram_pt (V : HSp D) (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    StdUnn.inner V (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n)
      (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (ξ.map (incA D)) : Mx D V.rank n) = (gramQ V ξ).map (incA D) := by
  have h0 : gramQ V ξ = ξᴴ * (HSpace.gram V * ξ) := rfl
  have e : ((gramQ V ξ).map (incA D) : Mx D n n) =
      HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (gA V) (ξ.map (incA D)) : Mx D V.rank n) := by
    change rat (gramQ V ξ) = HMul.hMul (adj (rat ξ)) (HMul.hMul (gA V) (rat ξ) : Mx D V.rank n)
    rw [h0, rat_mul, rat_mul, rat_conjTranspose]
    rfl
  rw [e]
  unfold GlobalTheory.StdUnn.inner
  have u := GlobalTheory.MixModel.mt_unitary V h⁻¹
  calc _ = HMul.hMul (adj (ξ.map (incA D))) (HMul.hMul (HMul.hMul (adj (Formalism.L2.Theta.mt V h⁻¹))
        (HMul.hMul (gA V) (Formalism.L2.Theta.mt V h⁻¹) : Mx D V.rank V.rank) : Mx D V.rank V.rank) (ξ.map (incA D)) : Mx D V.rank n) := by
        rw [adj_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [u]

theorem ifrB_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (ν : Measure (GA D V)) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : Mx D n n} (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (β : HermE D n) :
    IfrB V ν (ω (m * u) φ).1 β = ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1))))) *
      IfrB V ν (fun x => φ.1 (HMul.hMul x a.1)) β := by
  set K : ℂ := (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
        ψ (halfTr (Matrix.trace (b1 * (adj a.1 * β.1.map (incA D) * a.1)))) with hK
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
      (ω (m * u) φ).1 (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      fun h => K * ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = n ∧ gramQ V x = β.1},
        φ.1 (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)) : Mx D V.rank n) a.1) := by
    funext h
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    rw [weil_pt hω a hm hu, inner_mul_right, gram_pt, x.2.2, hK]
    ring
  unfold IfrB
  rw [key]
  show ⨍ q, K * _ ∂_ = _
  simp only [average_eq, integral_const_mul, mul_smul_comm]
  rfl

end GlobalTheory.CompanionTheory.IwaAd
