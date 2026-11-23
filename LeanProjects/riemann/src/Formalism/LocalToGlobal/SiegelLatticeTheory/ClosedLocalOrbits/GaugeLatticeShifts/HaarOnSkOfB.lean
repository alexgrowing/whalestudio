import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; split_ifs <;> norm_num

theorem ujOf_left {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε * g = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc (Formalism.REAL.Jm ε * gᴴ), Matrix.mul_assoc (Formalism.REAL.Jm ε), ← Matrix.mul_assoc gᴴ, h, jm_mul_jm]

def ujOf {n : ℕ} {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.mp (ujOf_left hg), ujOf_left hg⟩, hg⟩

theorem uMat_ujOf {n : ℕ} {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) :
    uMat (ujOf g hg) = g := rfl

theorem inUJ_conj {n : ℕ} {ε : Fin n → Bool} {H : Matrix (Fin n) (Fin n) ℂ} {P B : Matrix (Fin n) (Fin n) ℂ}
    (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = H) (hP : IsUnit P.det) (hB : Bᴴ * H * B = H) :
    Formalism.REAL.inUJ ε (P * B * P⁻¹) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (P * B * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * B * P⁻¹) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul]
  calc (P⁻¹)ᴴ * (Bᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * B * P⁻¹)
      = (P⁻¹)ᴴ * (Bᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * B) * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * Pᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by rw [hPJ, hB, ← hPJ]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

def qOf (r : ℕ) (sc : ℝ) (c : Fin (r + 1) → ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((sc : ℂ) ^ (r - a.1)) ^ 2 * c (Fin.castSucc a), c (Fin.last r))

theorem coordSc_qOf (r : ℕ) {sc : ℝ} (hsc : 0 < sc) (c : Fin (r + 1) → ℂ) : coordSc r sc (qOf r sc c) = c := by
  have hs : ∀ m : ℕ, ((sc : ℂ) ^ m) ≠ 0 := fun m => pow_ne_zero _ (by exact_mod_cast hsc.ne')
  conv_rhs => rw [← Fin.snoc_init_self c]
  unfold coordSc qOf
  congr 1
  funext a
  simp only [Fin.init]
  rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (hs _)), one_mul]

theorem qOf_coordSc (r : ℕ) {sc : ℝ} (hsc : 0 < sc) (q : (Fin r → ℂ) × ℂ) : qOf r sc (coordSc r sc q) = q := by
  have hs : ∀ m : ℕ, ((sc : ℂ) ^ m) ≠ 0 := fun m => pow_ne_zero _ (by exact_mod_cast hsc.ne')
  unfold coordSc qOf
  ext a
  · simp only [Fin.snoc_castSucc]
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (hs _)), one_mul]
  · simp only [Fin.snoc_last]

theorem bcWeight_zero {k r : ℕ} (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) (a : Fin r) (ha : q.1 a = 0) :
    Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
  unfold Formalism.QuantumDeterminants.bcWeight
  split_ifs
  · rw [Finset.prod_eq_zero (Finset.mem_univ a)]
    · ring
    · rw [ha, norm_zero]
      apply zero_pow
      unfold Formalism.QuantumDeterminants.Mdim
      have := a.2
      omega
  · rfl

theorem haarOn_sk_of_b {k r : ℕ} {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩

theorem gv_diag_eq {r : ℕ} (T T' : ℝ) (c : Fin (r + 1) → ℂ) :
    Gv T T' (Matrix.diagonal c) =
      ‖∏ a : Fin r, c (Fin.castSucc a)‖ ^ 2 * (Complex.normSq (c (Fin.last r)) - T * T') := by
  unfold Gv
  rw [dl_diagonal c (r + 1) le_rfl, dl_diagonal c r (by omega), Fin.prod_univ_castSucc]
  have e1 : ∀ i : Fin (r + 1), Fin.castLE (le_refl (r + 1)) i = i := fun i => Fin.ext rfl
  have e2 : ∀ i : Fin r, Fin.castLE (show r ≤ r + 1 by omega) i = Fin.castSucc i := fun i => Fin.ext rfl
  simp only [e1, e2, norm_mul, Complex.normSq_eq_norm_sq]
  ring

theorem psiP_mul_B {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsUnit P.det) (u u' : Formalism.REAL.UJ ε) (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Formalism.REAL.UJ ε) (hw : uMat w = P * B * P⁻¹) :
    (fun i j => (Matrix.of (psiP P u) * B * (Matrix.of (psiP P u'))⁻¹) i j) = psiP P (u * w * u'⁻¹) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hu' : uMat u'⁻¹ * uMat u' = 1 := by simp [uMat]
  have hinv : (Matrix.of (psiP P u'))⁻¹ = P⁻¹ * uMat u'⁻¹ * P := by
    apply Matrix.inv_eq_left_inv
    show P⁻¹ * uMat u'⁻¹ * P * (P⁻¹ * uMat u' * P) = 1
    calc P⁻¹ * uMat u'⁻¹ * P * (P⁻¹ * uMat u' * P) = P⁻¹ * uMat u'⁻¹ * (P * P⁻¹) * uMat u' * P := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (uMat u'⁻¹ * uMat u') * P := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu', Matrix.mul_one, h2]
  have hm : uMat (u * w * u'⁻¹) = uMat u * uMat w * uMat u'⁻¹ := by simp [uMat]
  have key : Matrix.of (psiP P u) * B * (Matrix.of (psiP P u'))⁻¹ = P⁻¹ * uMat (u * w * u'⁻¹) * P := by
    rw [hinv, hm, hw]
    show P⁻¹ * uMat u * P * B * (P⁻¹ * uMat u'⁻¹ * P) = P⁻¹ * (uMat u * (P * B * P⁻¹) * uMat u'⁻¹) * P
    simp only [Matrix.mul_assoc]
  funext i j
  exact congrFun (congrFun key i) j

theorem jacExGoodN_of_hpkEx_of_pFrame_of_haarCorr (hH : HpkEx) (hP : PFrame) (hHC : HaarCorr) (hZB : ZBig) (hBM : BigMem) (hW : CoordW)
    (hSec : SecWb) : JacExGoodN := by
  intro r k ε e z z' T T' sc hF hG hsc
  obtain ⟨P, hPJ, hPdet, hPe, zH, zH', hzH, hzH', hPz, hPz', hTz, hTz'⟩ := hP r k ε e z z' T T' hF hG
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r zH := by rw [hTz]; exact hF.T_pos
  have hT' : 0 < Formalism.QuantumDeterminants.Tz k r zH' := by rw [hTz']; exact hF.T'_pos
  obtain ⟨μsec, hμ⟩ := hSec k r zH zH' hF.k_pos hzH hzH' hT hT'
  let μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun ζ =>
    if Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq ζ then μsec ζ else 1
  have hμs : Formalism.QuantumDeterminants.IsSection k r zH zH' μs := by
    refine ⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
    · have hζ' : Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq ζ := hζ
      simp only [μs, if_pos hζ']
    · simp only [μs, if_pos hζ]
      exact hμ.2 ζ hζ
  have hU : ∀ ζ, (μs ζ)ᴴ * Formalism.QuantumDeterminants.Hb k * μs ζ = Formalism.QuantumDeterminants.Hb k := by
    intro ζ
    by_cases hζ : Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq ζ
    · simp only [μs, if_pos hζ]; exact (hμ.2 ζ hζ).1
    · simp only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      Formalism.REAL.inUJ ε (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μs q.2) * P⁻¹) := fun q hq =>
    inUJ_conj hPJ hPdet (hBM k r q.1 (μs q.2) hq (hU q.2))
  let h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε := fun c =>
    if hc : ∀ a, (qOf r sc c).1 a ≠ 0 then ujOf _ (hMuj (qOf r sc c) hc) else 1
  have hsc' : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hh0 : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      uMat (h0 (coordSc r sc q)) = P * Formalism.QuantumDeterminants.bigCell k r q.1 (μs q.2) * P⁻¹ := by
    intro q hq
    have hq' : ∀ a, (qOf r sc (coordSc r sc q)).1 a ≠ 0 := by rw [qOf_coordSc r hsc]; exact hq
    simp only [h0, dif_pos hq', uMat_ujOf, qOf_coordSc r hsc]
  refine ⟨h0, ?_, ?_⟩
  ·
    intro c hc
    have hq1 : ∀ a, (qOf r sc c).1 a ≠ 0 := fun a =>
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hsc')) (hc.1 _)
    have hζ : Formalism.QuantumDeterminants.Tz k r zH * Formalism.QuantumDeterminants.Tz k r zH' < Complex.normSq (qOf r sc c).2 := by
      have h2 := hc.2
      rw [gv_diag_eq] at h2
      rw [hTz, hTz']
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · show T * T' < Complex.normSq (c (Fin.last r)); linarith
      · exact absurd h3 (not_lt.2 (sq_nonneg _))
    have he0 := hh0 (qOf r sc c) hq1
    rw [coordSc_qOf r hsc] at he0
    show Zhat ε (famSc sc e z) (famSc sc e z') (uMat (h0 c)) = Matrix.diagonal c
    rw [he0, (hZB r k ε e z z' zH zH' P sc hPJ hPdet hPe hzH hzH' hPz hPz' hsc μs hμs (qOf r sc c) hq1 hζ).2,
      coordSc_qOf r hsc]
  · intro μS μS' hS hS'
    obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zH hzH hT
    obtain ⟨μW0', hW0'⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zH' hzH' hT'
    obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
    have hWs := haarOn_sk_of_b hW0
    have hWs' := haarOn_sk_of_b hW0'
    have hN := haarOn_sk_of_b hN0
    obtain ⟨hGm, hC1⟩ := hHC r k ε e z zH P hPJ hPdet hPe hzH hPz hT hF.k_pos
    obtain ⟨-, hC2⟩ := hHC r k ε e z' zH' P hPJ hPdet hPe hzH' hPz' hT' hF.k_pos
    obtain ⟨c1, hc1, hm1⟩ := hC1 μW0 μN0 hWs hN μS hS
    obtain ⟨c2, hc2, hm2⟩ := hC2 μW0' μN0 hWs' hN μS' hS'
    obtain ⟨K, hK, hForm⟩ := hH k r zH zH' hF.k_pos hzH hzH' hT hT' _ μW0 μW0' μN0 hGm hWs hWs' hN μs hμs
    obtain ⟨κ, hκ, hCW⟩ := hW r k T T' sc hF.k_pos hF.T_pos hF.T'_pos hsc
    refine ⟨K * κ / (c1 * c2), by positivity, fun φ hφ => ?_⟩
    have hme : MeasurableEmbedding (psiP (ε := ε) P) :=
      (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hPdet).measurableEmbedding
    let φh : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := Function.extend (psiP (ε := ε) P) φ 0
    have hφh : Measurable φh := hme.measurable_extend hφ measurable_const
    have hext : ∀ u, φh (psiP P u) = φ u := fun u => hme.injective.extend_apply φ 0 u
    have hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ∫⁻ x, φh x ∂((Formalism.REAL.muG ε).map (psiP P)) := by
      rw [hme.lintegral_map]; simp only [hext]
    have hne1 : ENNReal.ofReal c1 ≠ 0 := (ENNReal.ofReal_pos.2 hc1).ne'
    have hne2 : ENNReal.ofReal c2 ≠ 0 := (ENNReal.ofReal_pos.2 hc2).ne'
    have hmu1 : Formalism.MainNotions.S.muS μW0 μN0 = (ENNReal.ofReal c1)⁻¹ • μS.map (psiP P) := by
      rw [hm1, smul_smul, ENNReal.inv_mul_cancel hne1 ENNReal.ofReal_ne_top, one_smul]
    have hmu2 : Formalism.MainNotions.S.muS μW0' μN0 = (ENNReal.ofReal c2)⁻¹ • μS'.map (psiP P) := by
      rw [hm2, smul_smul, ENNReal.inv_mul_cancel hne2 ENNReal.ofReal_ne_top, one_smul]
    rw [hL, hForm φh hφh, hTz, hTz', hmu1, hmu2]
    let F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂μS' ∂μS
    have hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) *
        ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * Formalism.QuantumDeterminants.bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j)
          ∂((ENNReal.ofReal c2)⁻¹ • μS'.map (psiP P)) ∂((ENNReal.ofReal c1)⁻¹ • μS.map (psiP P)) =
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) *
          ((ENNReal.ofReal c1)⁻¹ * ((ENNReal.ofReal c2)⁻¹ * F (coordSc r sc q))) := by
      intro q
      by_cases hq : ∀ a, q.1 a ≠ 0
      · congr 1
        simp_rw [lintegral_smul_measure, hme.lintegral_map]
        rw [smul_eq_mul]
        congr 1
        simp_rw [smul_eq_mul]
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hne2)]
        congr 1
        refine lintegral_congr fun u => lintegral_congr fun u' => ?_
        rw [psiP_mul_B hPdet u u' _ (h0 (coordSc r sc q)) (hh0 q hq), hext]
      · push_neg at hq
        obtain ⟨a, ha⟩ := hq
        rw [bcWeight_zero T T' q a ha, ENNReal.ofReal_zero, zero_mul, zero_mul]
    rw [lintegral_congr hpt]
    have hrearr : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) *
        ((ENNReal.ofReal c1)⁻¹ * ((ENNReal.ofReal c2)⁻¹ * F (coordSc r sc q))) =
        ((ENNReal.ofReal c1)⁻¹ * (ENNReal.ofReal c2)⁻¹) *
          (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := fun q => by ring
    rw [lintegral_congr hrearr, lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hne1)
      (ENNReal.inv_ne_top.2 hne2)), hCW F]
    have hC0 : 0 ≤ K * κ / (c1 * c2) := by positivity
    simp only [F]
    have hpt2 : ∀ c, ENNReal.ofReal (K * κ / (c1 * c2) * wtLoc k T T' c) *
        ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂μS' ∂μS =
        ENNReal.ofReal (K * κ / (c1 * c2)) *
          (ENNReal.ofReal (wtLoc k T T' c) * ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂μS' ∂μS) := fun c => by
      rw [ENNReal.ofReal_mul hC0, mul_assoc]
    rw [lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul hc1.le,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hne1) (Or.inl ENNReal.ofReal_ne_top)]
    ring

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
