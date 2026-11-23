import Mathlib
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
theorem integral_mul_right (m : ℕ) (μ : Measure (Mx D m n)) (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D))
    (f : Mx D m n → ℂ) :
    ∫ y, f (HMul.hMul y a.1 : Mx D m n) ∂μ = npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(m : ℂ)) * ∫ y, f y ∂μ := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D m n
  haveI : IsTopologicalAddGroup (Mx D m n) := i1
  haveI : LocallyCompactSpace (Mx D m n) := i2
  haveI : SecondCountableTopology (Mx D m n) := i3
  haveI : T2Space (Mx D m n) := i4
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin m) (AE D)) a
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ m := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) m n
      (1 : GL (Fin m) (AE D)) a
    simpa using this
  have hA : 0 < absA D (Matrix.GeneralLinearGroup.det a) := absA_pos _
  have e : ∀ y : Mx D m n, (HMul.hMul y a.1 : Mx D m n) = φ y := fun y => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  have key : ∫ y, f (φ y) ∂μ = ((((addEquivAddHaarChar φ)⁻¹ : ℝ≥0) : ℝ) : ℂ) * ∫ y, f y ∂μ :=
    integral_comp_char μ φ f
  rw [hc, npow_neg_nat hA] at key
  simp only [e]
  exact key

theorem integral_shift {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (f : A → ℂ) (g : A) :
    ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ :=
  integral_sub_right_eq_self f g

theorem integral_shift_herm (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure) (f : hermA D n → ℂ) (g : hermA D n) :
    ∫ x, f (x - g) ∂lam = ∫ x, f x ∂lam := by
  obtain ⟨i1, -, -, -, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  exact integral_shift lam f g

theorem halfTr_add (x y : AE D) : halfTr (x + y) = halfTr x + halfTr y := by
  simp [halfTr, mul_add]

theorem halfTr_neg (x : AE D) : halfTr (-x) = -halfTr x := by
  simp [halfTr]

theorem inner_mul_right (V : HSp D) {r : ℕ} (x : Mx D V.rank r) (s : Mx D r r) :
    StdUnn.inner V (HMul.hMul x s : Mx D V.rank r) (HMul.hMul x s : Mx D V.rank r) =
      adj s * StdUnn.inner V x x * s := by
  unfold StdUnn.inner
  rw [adj_mul]
  simp only [Matrix.mul_assoc]

theorem trace_cg (a : GL (Fin n) (AE D)) (c Q : Mx D n n) :
    Matrix.trace (a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1)) = Matrix.trace (c * Q) := by
  have h1 : a.1 * c * adj a.1 * (adj (a⁻¹).1 * Q * (a⁻¹).1) = a.1 * (c * Q * (a⁻¹).1) := by
    calc _ = a.1 * c * (adj a.1 * adj (a⁻¹).1) * Q * (a⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [adj_mul_adj_inv]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem trace_beta (a : GL (Fin n) (AE D)) (B c : Mx D n n) :
    Matrix.trace (B * (a.1 * c * adj a.1)) = Matrix.trace (adj a.1 * B * a.1 * c) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem weil_pt {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1)) {b1 : Mx D n n}
    (hu : mat u = blk4 1 b1 0 1) (φ : schwartzA θ V.rank n) (y : Mx D V.rank n) :
    (ω (m * u) φ).1 y = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (ψ (halfTr (Matrix.trace (b1 * StdUnn.inner V (HMul.hMul y a.1 : Mx D V.rank n) (HMul.hMul y a.1 : Mx D V.rank n)))) *
        φ.1 (HMul.hMul y a.1 : Mx D V.rank n)) := by
  rw [map_mul, Module.End.mul_apply, hω.levi m a hm, hω.unip u b1 hu]

theorem jt_step {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {V : HSp D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (hμ : μ.IsAddHaarMeasure) (a : GL (Fin n) (AE D)) {m u : G D n} (hm : mat m = blk4 a.1 0 0 (adj (a⁻¹).1))
    {b1 : hermA D n} (hu : mat u = blk4 1 b1.1 0 1) (φ : schwartzA θ V.rank n) (c : hermA D n) :
    Jt ψ V μ (ω (m * u) φ).1 (cg a c) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2) *
      (npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) * Jt ψ V μ φ.1 (c + b1)) := by
  set F : Mx D V.rank n → ℂ := fun y => φ.1 y * ψ (halfTr (Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V y y) : Mx D n n))) with hF
  have hpt : ∀ y : Mx D V.rank n, (ω (m * u) φ).1 y *
      ψ (halfTr (Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n))) =
      ((χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) ((V.rank : ℂ) / 2)) *
        F (HMul.hMul y a.1 : Mx D V.rank n) := by
    intro y
    have hy : y = (HMul.hMul (HMul.hMul y a.1 : Mx D V.rank n) (a⁻¹).1 : Mx D V.rank n) := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    set Y : Mx D V.rank n := HMul.hMul y a.1 with hY
    have e1 : Matrix.trace (HMul.hMul (cg a c).1 (StdUnn.inner V y y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) := by
      rw [hy, inner_mul_right]
      exact trace_cg a c.1 _
    rw [weil_pt hω a hm hu, e1]
    simp only [hF]
    have e2 : Matrix.trace (HMul.hMul (c + b1).1 (StdUnn.inner V Y Y) : Mx D n n) =
        Matrix.trace (c.1 * StdUnn.inner V Y Y) + Matrix.trace (b1.1 * StdUnn.inner V Y Y) := by
      rw [← Matrix.trace_add, ← Matrix.add_mul]
      rfl
    rw [e2, halfTr_add, AddChar.map_add_eq_mul]
    ring
  unfold Jt
  simp only [hpt]
  rw [integral_const_mul, integral_mul_right V.rank μ hμ a F]

end GlobalTheory.CompanionTheory.IwaAd
