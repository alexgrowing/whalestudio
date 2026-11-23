import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FoldrHolDEqIteratedFDeriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsOfThetaDatumInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockJetOrigin

open scoped ComplexConjugate ComplexOrder
open GlobalTheory.VacUnique (hAt omAt omO omO_apply)

variable {D : D7}

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) := by
  have him := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hre := GlobalTheory.FockInj.xi_re (D := D) τ
  have hn := GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq D (tauE D τ)
  apply Complex.ext
  · simp [hre]
  · rw [← hn]
    have : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im := by
      rw [Complex.norm_def, Complex.normSq_apply, hre]
      simp only [zero_mul, zero_add]
      exact Real.sqrt_mul_self him.le
    simp [this]

theorem cartan_eq_one {n : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) (hs : IsCartanInv G s) : s = 1 := by
  obtain ⟨h1, -, h3⟩ := hs
  have hBi : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 hB
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hBi)
  set P := Bᴴ * G * s * B with hP
  have hPd : P.PosDef := by
    have := h3.conjTranspose_mul_mul_same (B := B) (Matrix.mulVec_injective_of_isUnit hu)
    simpa [hP, Matrix.mul_assoc] using this
  have hC : (Bᴴ * G) * B = 1 := hB
  have hPP : P * P = 1 := by
    have : P * P = Bᴴ * G * s * (B * (Bᴴ * G)) * s * B := by simp only [hP, Matrix.mul_assoc]
    rw [this, hBi, Matrix.mul_one, Matrix.mul_assoc (Bᴴ * G), h1, Matrix.mul_one]
    exact hB
  have h1P : (P + 1).PosDef := hPd.add_posSemidef Matrix.PosSemidef.one
  have hP1 : IsUnit (P + 1) := h1P.isUnit
  have hz : (P - 1) * (P + 1) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_add, hPP]; simp only [Matrix.mul_one, Matrix.one_mul]; abel
  have hP0 : P - 1 = 0 := by
    have := congrArg (· * ((P + 1)⁻¹)) hz
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP1)] using this
  have hPe : P = 1 := sub_eq_zero.1 hP0

  have : s = B * P * (Bᴴ * G) := by
    have e : B * P * (Bᴴ * G) = (B * (Bᴴ * G)) * s * (B * (Bᴴ * G)) := by simp only [hP, Matrix.mul_assoc]
    rw [e, hBi]; simp
  rw [this, hPe, Matrix.mul_one, hBi]

section Coord

variable (θ : InfFam D) {S T : HSp D} (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
  (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)

noncomputable def zc (w : WO S T) : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank :=
  fun τ => (BT τ)⁻¹ * compAt θ τ w * BS τ

noncomputable def nrm {N N' : ℕ} (z : Formalism.MainNotions.TaylorLogMetric.VC D N N') : ℂ :=
  ∑ τ, ∑ a, ∑ b, ((‖z τ a b‖ ^ 2 : ℝ) : ℂ)

theorem compAt_add {m n : ℕ} (τ : D.what₂.Tau) (x y : Mx D m n) : compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j
  show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
  rw [RingHom.map_add, RingHom.map_add]

theorem zc_add (w w' : WO S T) : zc θ BS BT (w + w') = zc θ BS BT w + zc θ BS BT w' := by
  funext τ
  show (BT τ)⁻¹ * compAt θ τ (w + w') * BS τ = (BT τ)⁻¹ * compAt θ τ w * BS τ + (BT τ)⁻¹ * compAt θ τ w' * BS τ
  rw [compAt_add, Matrix.mul_add, Matrix.add_mul]

theorem zc_zero : zc θ BS BT (0 : WO S T) = 0 := by
  have := zc_add θ BS BT (0 : WO S T) 0
  rw [add_zero] at this
  exact left_eq_add.mp this

variable {BS BT}

theorem trace_smul_single {m n : ℕ} (c : ℂ) (a : Fin m) (b : Fin n) (X : Matrix (Fin m) (Fin n) ℂ) :
    ((c • Matrix.single a b (1 : ℂ))ᴴ * X).trace = starRingEnd ℂ c * X a b := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, Matrix.smul_mul, Matrix.trace_smul]
  have : (Matrix.single b a (star (1 : ℂ)) * X).trace = X a b := by
    unfold Matrix.trace
    rw [Finset.sum_eq_single b]
    · simp [Matrix.diag, Matrix.single_mul_apply_same]
    · intro x _ h
      simp [Matrix.diag, Matrix.mul_apply, Matrix.single_apply, Ne.symm h]
    · simp
  rw [this]; rfl

theorem hAt_coord {τ : D.what₂.Tau} (hS : (BS τ)ᴴ * gramAt D S τ * BS τ = 1) (hT : (BT τ)ᴴ * gramAt D T τ * BT τ = 1)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    hAt S T τ x y = (((BT τ)⁻¹ * y * BS τ)ᴴ * ((BT τ)⁻¹ * x * BS τ)).trace := by
  set P := BS τ
  set Q := BT τ
  set GS := gramAt D S τ
  set GT := gramAt D T τ
  have hP1 : (Pᴴ * GS) * P = 1 := hS
  have hP2 : P * (Pᴴ * GS) = 1 := mul_eq_one_comm.1 hP1
  have hP3 : GS * P * Pᴴ = 1 := mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc]; exact hS)
  have hGS : GS⁻¹ = P * Pᴴ := Matrix.inv_eq_right_inv (by rw [← Matrix.mul_assoc]; exact hP3)
  have hQ1 : (Qᴴ * GT) * Q = 1 := hT
  have hQ2 : Q⁻¹ = Qᴴ * GT := Matrix.inv_eq_left_inv hQ1
  have hQ3 : Q * Q⁻¹ = 1 := by rw [hQ2]; exact mul_eq_one_comm.1 hQ1
  have hQ4 : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ3, Matrix.conjTranspose_one]
  have hGT : (Q⁻¹)ᴴ * Q⁻¹ = GT := by
    calc (Q⁻¹)ᴴ * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * GT) := by rw [← hQ2]
      _ = GT := by rw [← Matrix.mul_assoc, hQ4, Matrix.one_mul]
  show (GS⁻¹ * yᴴ * GT * x).trace = _
  rw [hGS]
  simp only [Matrix.conjTranspose_mul]
  rw [← hGT]
  have e : Pᴴ * (yᴴ * (Q⁻¹)ᴴ) * (Q⁻¹ * x * P) = (Pᴴ * yᴴ * ((Q⁻¹)ᴴ * Q⁻¹) * x) * P := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm (Pᴴ * yᴴ * ((Q⁻¹)ᴴ * Q⁻¹) * x) P]
  simp only [Matrix.mul_assoc]

theorem entry_deriv (x c : ℂ) :
    HasDerivAt (fun t : ℝ => ((‖x + (t : ℂ) * c‖ ^ 2 : ℝ) : ℂ)) (((2 * (starRingEnd ℂ c * x).re : ℝ)) : ℂ) 0 := by
  have e : (fun t : ℝ => ‖x + (t : ℂ) * c‖ ^ 2) = fun t : ℝ => (x.re + t * c.re) ^ 2 + (x.im + t * c.im) ^ 2 := by
    funext t
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    ring
  have h1 : HasDerivAt (fun t : ℝ => (x.re + t * c.re) ^ 2 + (x.im + t * c.im) ^ 2) (2 * (starRingEnd ℂ c * x).re) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => x.re + t * c.re) c.re 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c.re).const_add x.re
    have a2 : HasDerivAt (fun t : ℝ => x.im + t * c.im) c.im 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c.im).const_add x.im
    refine ((a1.fun_pow 2).fun_add (a2.fun_pow 2)).congr_deriv ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    norm_num
    ring
  rw [← e] at h1
  exact h1.ofReal_comp

theorem sum_placeRowColumn_eq_single {N N' : ℕ} (g : D.what₂.Tau → Fin N' → Fin N → ℂ) (v : D.what₂.Tau × Fin N' × Fin N)
    (h : ∀ τ a b, ¬ (τ = v.1 ∧ a = v.2.1 ∧ b = v.2.2) → g τ a b = 0) :
    ∑ τ, ∑ a, ∑ b, g τ a b = g v.1 v.2.1 v.2.2 := by
  obtain ⟨τ, a, b⟩ := v
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · intro b' _ hb; exact h _ _ _ fun e => hb e.2.2
  · simp
  · intro a' _ ha; exact Finset.sum_eq_zero fun b' _ => h _ _ _ fun e => ha e.2.1
  · simp
  · intro τ' _ hτ; exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => h _ _ _ fun e => hτ e.1
  · simp

theorem nrm_deriv {N N' : ℕ} (z : Formalism.MainNotions.TaylorLogMetric.VC D N N') (v : D.what₂.Tau × Fin N' × Fin N) (α : ℂ) :
    HasDerivAt (fun t : ℝ => nrm (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v))
      (((2 * (starRingEnd ℂ α * z v.1 v.2.1 v.2.2).re : ℝ)) : ℂ) 0 := by
  have h : HasDerivAt (fun t : ℝ => nrm (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v))
      (∑ τ, ∑ a, ∑ b, (((2 * (starRingEnd ℂ (α * Formalism.MainNotions.TaylorLogMetric.coordV D v τ a b) * z τ a b).re : ℝ)) : ℂ)) 0 := by
    unfold nrm
    refine HasDerivAt.fun_sum fun τ _ => HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
    have := entry_deriv (z τ a b) (α * Formalism.MainNotions.TaylorLogMetric.coordV D v τ a b)
    have e : (fun t : ℝ => ((‖(z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v) τ a b‖ ^ 2 : ℝ) : ℂ)) =
        fun t : ℝ => ((‖z τ a b + (t : ℂ) * (α * Formalism.MainNotions.TaylorLogMetric.coordV D v τ a b)‖ ^ 2 : ℝ) : ℂ) := by
      funext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [e]
    exact this
  rw [sum_placeRowColumn_eq_single _ v] at h
  · simpa [Formalism.MainNotions.TaylorLogMetric.coordV] using h
  · intro τ a b hn
    simp [Formalism.MainNotions.TaylorLogMetric.coordV, hn]

theorem inv_mul_of_frame {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : B⁻¹ * B = 1 := by
  rw [Matrix.inv_eq_left_inv hB]; exact hB

theorem coord_unit {τ : D.what₂.Tau} (hS : (BS τ)ᴴ * gramAt D S τ * BS τ = 1) (hT : (BT τ)ᴴ * gramAt D T τ * BT τ = 1)
    (a : Fin T.rank) (b : Fin S.rank) :
    (BT τ)⁻¹ * unitMap (BS τ) (BT τ) a b * BS τ = Matrix.single a b 1 := by
  rw [unitMap]
  have h1 := inv_mul_of_frame hS
  have h2 := inv_mul_of_frame hT
  calc (BT τ)⁻¹ * (BT τ * Matrix.single a b (1 : ℂ) * (BS τ)⁻¹) * BS τ
      = ((BT τ)⁻¹ * BT τ) * Matrix.single a b (1 : ℂ) * ((BS τ)⁻¹ * BS τ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

variable (hS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) (hT : ∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = 1)
include hS hT

theorem zc_line (hθ : IsInfFam θ) (v : FVar D T.rank S.rank) (α : ℂ) (t : ℝ) :
    zc θ BS BT (lineAt θ v.1 (α • unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) t) =
      ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v := by
  obtain ⟨τ, a, b⟩ := v
  funext τ' i j
  have hL := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (α • unitMap (BS τ) (BT τ) a b)).2.2 t τ'
  show ((BT τ')⁻¹ * compAt θ τ' _ * BS τ' : Matrix (Fin T.rank) (Fin S.rank) ℂ) i j =
    ((t : ℂ) * α) * Formalism.MainNotions.TaylorLogMetric.coordV D (τ, a, b) τ' i j
  rw [hL]
  by_cases h : τ' = τ
  · subst h
    have key : (BT τ')⁻¹ * ((t : ℂ) • α • unitMap (BS τ') (BT τ') a b) * BS τ' =
        ((t : ℂ) * α) • Matrix.single a b (1 : ℂ) := by
      rw [← coord_unit (hS τ') (hT τ') a b]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [if_pos rfl, key]
    show ((t : ℂ) * α) * (Matrix.single a b (1 : ℂ)) i j = ((t : ℂ) * α) * Formalism.MainNotions.TaylorLogMetric.coordV D (τ', a, b) τ' i j
    congr 1
    have hiff : (a = i ∧ b = j) ↔ (i = a ∧ j = b) := by
      constructor <;> rintro ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩
    simp only [Formalism.MainNotions.TaylorLogMetric.coordV, Matrix.single_apply, hiff, true_and]
  · rw [if_neg h, Matrix.mul_zero, Matrix.zero_mul]
    simp [Formalism.MainNotions.TaylorLogMetric.coordV, h]

theorem omO_line (hθ : IsInfFam θ) (v : FVar D T.rank S.rank) (α : ℂ) (t : ℝ) (w : WO S T) :
    omO S T (GlobalTheory.FockCompare.piW θ T S w)
        (GlobalTheory.FockCompare.piW θ T S (lineAt θ v.1 (α • unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) t)) =
      t * (2 * (tauE D v.1 D.host.xi0 * (starRingEnd ℂ α * zc θ BS BT w v.1 v.2.1 v.2.2)).re) := by
  obtain ⟨τ, a, b⟩ := v
  have hL := fun τ' => (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (α • unitMap (BS τ) (BT τ) a b)).2.2 t τ'
  rw [omO_apply, Finset.sum_eq_single τ]
  · have e : GlobalTheory.FockCompare.piW θ T S (lineAt θ τ (α • unitMap (BS τ) (BT τ) a b) t) τ = (t : ℂ) • α • unitMap (BS τ) (BT τ) a b := by
      have := hL τ
      rw [if_pos rfl] at this
      exact this
    have e2 : GlobalTheory.FockCompare.piW θ T S w τ = compAt θ τ w := rfl
    rw [e, e2, omAt, hAt_coord (hS τ) (hT τ)]
    have key : (BT τ)⁻¹ * ((t : ℂ) • α • unitMap (BS τ) (BT τ) a b) * BS τ =
        ((t : ℂ) * α) • Matrix.single a b (1 : ℂ) := by
      rw [← coord_unit (hS τ) (hT τ) a b]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [key]
    rw [trace_smul_single, map_mul, Complex.conj_ofReal]
    show 2 * (tauE D τ D.host.xi0 * ((t : ℂ) * starRingEnd ℂ α * ((BT τ)⁻¹ * compAt θ τ w * BS τ) a b)).re =
      t * (2 * (tauE D τ D.host.xi0 * (starRingEnd ℂ α * ((BT τ)⁻¹ * compAt θ τ w * BS τ) a b)).re)
    have e3 : tauE D τ D.host.xi0 * ((t : ℂ) * starRingEnd ℂ α * ((BT τ)⁻¹ * compAt θ τ w * BS τ) a b) =
        (t : ℂ) * (tauE D τ D.host.xi0 * (starRingEnd ℂ α * ((BT τ)⁻¹ * compAt θ τ w * BS τ) a b)) := by ring
    rw [e3, Complex.re_ofReal_mul]
    ring
  · intro τ' _ h
    have e : GlobalTheory.FockCompare.piW θ T S (lineAt θ τ (α • unitMap (BS τ) (BT τ) a b) t) τ' = 0 := by
      have := hL τ'
      rw [if_neg h] at this
      exact this
    rw [e]
    have z0 : ∀ x : Matrix (Fin T.rank) (Fin S.rank) ℂ, omAt S T τ' x 0 = 0 := fun x => by simp [omAt, hAt]
    exact z0 _
  · simp

noncomputable def gs {N N' : ℕ} (z : Formalism.MainNotions.TaylorLogMetric.VC D N N') : ℂ :=
  Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * nrm z)

theorem dRho_dir {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {G : WO S T → ℂ} {Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ} (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w : WO S T, w.map (finPart D) = 0 → G w = gs (zc θ BS BT w) * Φ (zc θ BS BT w))
    (v : FVar D T.rank S.rank) (α : ℂ) (w : WO S T) (hw : w.map (finPart D) = 0) :
    dRho (heisO ψ S T) θ v.1 (α • unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) G w =
      gs (zc θ BS BT w) *
        ((-(Real.pi * Complex.I) *
              ((2 * (tauE D v.1 D.host.xi0 * (starRingEnd ℂ α * zc θ BS BT w v.1 v.2.1 v.2.2)).re : ℝ) : ℂ) +
            -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
              ((2 * (starRingEnd ℂ α * zc θ BS BT w v.1 v.2.1 v.2.2).re : ℝ) : ℂ)) * Φ (zc θ BS BT w) +
          fderiv ℝ Φ (zc θ BS BT w) (α • Formalism.MainNotions.TaylorLogMetric.coordV D v)) := by
  set z := zc θ BS BT w with hz
  set L := lineAt θ v.1 (α • unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) with hL
  set om : ℝ := 2 * (tauE D v.1 D.host.xi0 * (starRingEnd ℂ α * z v.1 v.2.1 v.2.2)).re with hom
  have hfin : ∀ t, (L t).map (finPart D) = 0 := (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ _ _).2.1
  have hreal : ∀ t, (w + L t).map (finPart D) = 0 := by
    intro t
    ext i j
    have a1 := congrFun (congrFun hw i) j
    have a2 := congrFun (congrFun (hfin t) i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [Matrix.add_apply, (finPart D).map_add, a1, a2, add_zero]
  have hfun : (fun t : ℝ => heisO ψ S T (L t) G w) = fun t : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((t * om : ℝ) : ℂ)) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * nrm (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v)) *
          Φ (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v)) := by
    funext t
    have hzl : zc θ BS BT (w + L t) = z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v := by
      rw [zc_add, hL, zc_line θ hS hT hθ]
    rw [heisO, GlobalTheory.OrientedChar.char_symplOH D θ ψ hθ hψ S T w (L t) (Or.inl hw), hG _ (hreal t), hzl,
      omO_line θ hS hT hθ v α t w]
    rfl
  have hA : HasDerivAt (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((t * om : ℝ) : ℂ)))
      (Complex.exp (-(Real.pi * Complex.I) * (((0 : ℝ) * om : ℝ) : ℂ)) * (-(Real.pi * Complex.I) * (om : ℂ))) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => ((t * om : ℝ) : ℂ)) (om : ℂ) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).mul_const om).ofReal_comp
      simpa using this
    exact (h0.const_mul _).cexp
  have hB : HasDerivAt (fun t : ℝ => Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
        nrm (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v)))
      (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * nrm (z + (((0 : ℝ) : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v)) *
        (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((2 * (starRingEnd ℂ α * z v.1 v.2.1 v.2.2).re : ℝ) : ℂ))) 0 :=
    ((nrm_deriv z v α).const_mul _).cexp
  have hC : HasDerivAt (fun t : ℝ => Φ (z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v))
      (fderiv ℝ Φ z (α • Formalism.MainNotions.TaylorLogMetric.coordV D v)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v) (α • Formalism.MainNotions.TaylorLogMetric.coordV D v) 0 := by
      have h2 : HasDerivAt (fun t : ℝ => t • (α • Formalism.MainNotions.TaylorLogMetric.coordV D v)) (α • Formalism.MainNotions.TaylorLogMetric.coordV D v) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (α • Formalism.MainNotions.TaylorLogMetric.coordV D v)
      have e : (fun t : ℝ => z + ((t : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v) =
          fun t : ℝ => z + t • (α • Formalism.MainNotions.TaylorLogMetric.coordV D v) := by
        funext t
        rw [mul_smul, Complex.coe_smul]
      rw [e]
      exact h2.const_add z
    have hz0 : z + (((0 : ℝ) : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v = z := by simp
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hΦ z).hasFDerivAt h1 hz0.symm
  have hall := (hA.fun_mul (hB.fun_mul hC)).deriv
  have hz0 : z + (((0 : ℝ) : ℂ) * α) • Formalism.MainNotions.TaylorLogMetric.coordV D v = z := by simp
  rw [Formalism.IndefR.Datum.dRho]
  show deriv (fun t : ℝ => heisO ψ S T (L t) G w) 0 = _
  rw [hfun, hall, hz0, gs]
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, one_mul]
  ring

noncomputable def lam (v : FVar D T.rank S.rank) (z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) : ℂ :=
  -(2 * Real.pi * Formalism.L2.Pj.xiR D) * starRingEnd ℂ (z v.1 v.2.1 v.2.2)

theorem crea_dir {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {G : WO S T → ℂ} {Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ} (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w : WO S T, w.map (finPart D) = 0 → G w = gs (zc θ BS BT w) * Φ (zc θ BS BT w))
    (v : FVar D T.rank S.rank) (w : WO S T) (hw : w.map (finPart D) = 0) :
    crea (heisO ψ S T) θ v.1 (cplxO 1 1) (unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) G w =
      gs (zc θ BS BT w) * (2 * (lam v (zc θ BS BT w) * Φ (zc θ BS BT w) + (1 / 2 : ℂ) *
        (fderiv ℝ Φ (zc θ BS BT w) (Formalism.MainNotions.TaylorLogMetric.coordV D v) -
          Complex.I * fderiv ℝ Φ (zc θ BS BT w) (Complex.I • Formalism.MainNotions.TaylorLogMetric.coordV D v)))) := by
  have h1 := dRho_dir θ hS hT hψ hθ hΦ hG v 1 w hw
  have h2 := dRho_dir θ hS hT hψ hθ hΦ hG v Complex.I w hw
  rw [one_smul, one_smul] at h1
  have hJ : cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (unitMap (BS v.1) (BT v.1) v.2.1 v.2.2) = Complex.I • unitMap (BS v.1) (BT v.1) v.2.1 v.2.2 := by
    simp [cplxO]
  rw [crea, hJ, Pi.sub_apply, Pi.smul_apply, h1, h2, smul_eq_mul, lam, realPlace_cmTrace_zero_element_eq_I_mul_abs]
  set x := zc θ BS BT w v.1 v.2.1 v.2.2 with hx
  have hc : starRingEnd ℂ x = (x.re : ℂ) - (x.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have r1 : (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ 1 * x)).re = -(Formalism.L2.Pj.xiR D * x.im) := by
    simp
  have r2 : (starRingEnd ℂ 1 * x).re = x.re := by simp
  have r3 : (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (starRingEnd ℂ Complex.I * x)).re = Formalism.L2.Pj.xiR D * x.re := by
    simp
  have r4 : (starRingEnd ℂ Complex.I * x).re = x.im := by simp
  rw [r1, r2, r3, r4, hc]
  push_cast
  linear_combination (gs (zc θ BS BT w) * Φ (zc θ BS BT w) * 2 * (Real.pi : ℂ) * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * (x.re : ℂ)) * Complex.I_mul_I

theorem fock_monomial_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (F : WO S T → ℂ) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) (hΘ : Differentiable ℂ Θ)
    (hF : ∀ w : WO S T, w.map (finPart D) = 0 → F w = gs (zc θ BS BT w) * Θ (zc θ BS BT w))
    (k : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT F (MvPolynomial.monomial k 1) 0 =
      (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) *
        Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  set c₀ : ℂ := ((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹ with hc₀
  let u : FVar D T.rank S.rank → Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun v => Formalism.MainNotions.TaylorLogMetric.coordV D v
  let Dl : FVar D T.rank S.rank → (Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) → Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ :=
    fun l Φ z => lam l z * Φ z + (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - Complex.I * fderiv ℝ Φ z (Complex.I • u l))
  have hlam : ∀ l : FVar D T.rank S.rank, (∀ a b : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) (a : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), lam l (t • a) = starRingEnd ℂ t * lam l a := by
    intro l
    refine ⟨fun a b => ?_, fun t a => ?_⟩
    · simp only [lam, Pi.add_apply, map_add]
      ring
    · simp only [lam, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
  have hops := GlobalTheory.Ker.CreOp.foldr_creation_zero _ _ u (lam (S := S) (T := T)) Θ hlam hΘ Dl (fun _ _ _ => rfl)
  let A := aPlusAll (heisO ψ S T) θ (fun _ => cplxO 1 1) BS BT
  have key : ∀ L : List (FVar D T.rank S.rank), ∀ w : WO S T, w.map (finPart D) = 0 →
      L.foldr (fun i g => A i g) F w = gs (zc θ BS BT w) * (c₀ ^ L.length * L.foldr Dl Θ (zc θ BS BT w)) := by
    intro L
    induction L with
    | nil =>
      intro w hw
      simp [hF w hw]
    | cons a L ih =>
      intro w hw
      have hdf : Differentiable ℝ (L.foldr Dl Θ) := (hops L).1.differentiable (by simp)
      have h := crea_dir θ hS hT hψ hθ (Φ := fun z => c₀ ^ L.length * L.foldr Dl Θ z) (hdf.const_mul _) ih a w hw
      rw [List.foldr_cons]
      change ((fockScale D a.1 : ℂ)⁻¹) * crea (heisO ψ S T) θ a.1 (cplxO 1 1)
        (unitMap (BS a.1) (BT a.1) a.2.1 a.2.2) (L.foldr (fun i g => A i g) F) w = _
      have hf : (fockScale D a.1 : ℂ)⁻¹ = c₀ / 2 := by
        rw [fockScale, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, hc₀, Complex.ofReal_mul, _root_.mul_inv_rev]
        norm_num [div_eq_mul_inv]
      rw [h, fderiv_const_mul (hdf _), hf]
      simp only [List.foldr_cons, List.length_cons, _root_.smul_apply, smul_eq_mul]
      simp only [Dl, u, pow_succ]
      ring
  have h0 : zc θ BS BT (0 : WO S T) = 0 := zc_zero θ BS BT
  have hr0 : (0 : WO S T).map (finPart D) = 0 := by
    ext i j
    simp
  have hg0 : gs (0 : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) = 1 := by
    simp [gs, nrm]
  have h2 : pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT F (MvPolynomial.monomial k (1 : ℂ)) = opPow A k F := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow A k F) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  have hlen : (Finsupp.toMultiset k).toList.length = k.sum fun _ n => n := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    rfl
  have hprod : (k.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hgen : ∀ (L : List (FVar D T.rank S.rank)) (n : ℕ) (h : n = L.length),
      iteratedFDeriv ℂ n Θ 0 (fun i => u (L.get ⟨i, h ▸ i.2⟩)) = iteratedFDeriv ℂ L.length Θ 0 fun i => u (L.get i) := by
    rintro L _ rfl
    rfl
  have hap : Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ =
      iteratedFDeriv ℂ (Finsupp.toMultiset k).toList.length Θ 0 fun i => u ((Finsupp.toMultiset k).toList.get i) := by
    classical
    unfold Formalism.MainNotions.GL3Theta.applyAt0
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
      one_mul, Formalism.MainNotions.TaylorLogMetric.taylor, mul_div_cancel₀ _ hprod]
    exact hgen _ _ (Multiset.length_toList _).symm
  rw [h2, opPow, key _ 0 hr0, h0, hg0, one_mul, (hops _).2, hap, ← hlen]

end Coord

theorem frame_map (τ : D.what₂.Tau) {n : ℕ} {M Gm : Matrix (Fin n) (Fin n) D.host.E}
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * Gm * M = 1) :
    (M.map (tauE D τ))ᴴ * Gm.map (tauE D τ) * M.map (tauE D τ) = 1 := by
  have hc : (M.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (tauE D τ) := by
    ext i j
    exact (GlobalTheory.FockCompare.tauE_star τ (M j i)).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

end GlobalTheory.FockJetOrigin

theorem GlobalTheory.FockJetOrigin.fockIn_gauss_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ (F : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS (.top t j)).rank (G.pT (.top t j)).rank → ℂ), Differentiable ℂ Θ → (∀ w : WO (G.pS (.top t j)) (G.pT (.top t j)), w.map (finPart D) = 0 → F w = Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖((N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ) a b‖ ^ 2 : ℝ) : ℂ)) * Θ (fun τ => (N.frC (.top (j + 1)) τ)⁻¹ * compAt W.θ τ w * N.frC (.top j) τ)) → ∀ k : FVar D (G.pT (.top t j)).rank (G.pS (.top t j)).rank →₀ ℕ, GlobalTheory.FunObj.fockIn W N.frC (.top t j) F (MvPolynomial.monomial k 1) 0 = (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D T L sc G W U N t j hj F Θ hΘ hF k
  have hS : ∀ τ, (N.frC (.top j) τ)ᴴ * gramAt D (G.V (.top j)) τ * N.frC (.top j) τ = 1 := fun τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on (.top j) (by show j ≤ D.R.m; omega))
  have hT : ∀ τ, (N.frC (.top (j + 1)) τ)ᴴ * gramAt D (G.V (.top (j + 1))) τ * N.frC (.top (j + 1)) τ = 1 := fun τ =>
    GlobalTheory.FockJetOrigin.frame_map τ (N.fr_on (.top (j + 1)) hj)
  have hc1 : ∀ τ, IsCartanInv (gramAt D (G.V (.top j)) τ) (W.cart (.top j) τ) := W.cart_is (.top j) (by show j ≤ D.R.m; omega)
  have hc2 : ∀ τ, IsCartanInv (gramAt D (G.V (.top (j + 1))) τ) (W.cart (.top (j + 1)) τ) := W.cart_is (.top (j + 1)) hj
  have c1' : ∀ τ, W.cart (.top j) τ = 1 := fun τ => GlobalTheory.FockJetOrigin.cartan_eq_one (hS τ) (hc1 τ)
  have c2' : ∀ τ, W.cart (.top (j + 1)) τ = 1 := fun τ => GlobalTheory.FockJetOrigin.cartan_eq_one (hT τ) (hc2 τ)
  have c1 : W.cart (.top j) = fun (_ : D.what₂.Tau) => (1 : Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ) :=
    funext c1'
  have c2 : W.cart (.top (j + 1)) =
      fun (_ : D.what₂.Tau) => (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ) :=
    funext c2'
  have main := GlobalTheory.FockJetOrigin.fock_monomial_zero W.θ (S := G.V (.top j)) (T := G.V (.top (j + 1))) hS hT W.ψ_std W.θ_is F Θ hΘ hF k
  show pureTensorO W.ψ W.θ (G.V (.top j)) (G.V (.top (j + 1))) (W.cart (.top j)) (W.cart (.top (j + 1))) (N.frC (.top j))
    (N.frC (.top (j + 1))) F (MvPolynomial.monomial k 1) 0 = _
  rw [c1, c2]
  exact main
