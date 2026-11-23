import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.IsoRightInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PointwiseBoundHolds

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt PI.PolynomialProperness PI.PolynomialProperness.CoreW
open scoped ComplexConjugate

noncomputable section

def cIso (N A R0 : ℝ) : ℝ := 2 * (N * A) ^ 2 * R0 ^ 2 + 2 * (1 + N * A) * (1 + N * A * R0 * R0) ^ 2

section iso

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isoExpl (H : Matrix (Fin n) (Fin n) ℂ) (m : ι → Fin n → ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (hG : gramOf H m * Γi = 1)
    (hpsd : ∀ x, (∀ i, herm H x (m i) = 0) → 0 ≤ (herm H x x).re)
    (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (K : ℝ) (hK : 0 ≤ K)
    (hsm : ∀ i, nsq (s *ᵥ m i) ≤ K) (x : Fin n → ℂ) :
    nsq (s *ᵥ x) ≤ cIso (Fintype.card ι) (∑ j, ∑ k, ‖Γi j k‖) (∑ i, eN (m i)) * (1 + K) ^ 2 * nsq x := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, ∑ k, ‖Γi j k‖ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (Fintype.card ι : ℝ) := ⟨_, rfl⟩
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = ∑ i, eN (m i) := ⟨_, rfl⟩
  rw [← hA, ← hN, ← hR0]
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hN0 : 0 ≤ N := hN ▸ Nat.cast_nonneg _
  have hR00 : 0 ≤ R0 := hR0 ▸ Finset.sum_nonneg fun i _ => eN_nonneg _
  have hD0 : 0 ≤ N * A := mul_nonneg hN0 hA0
  have hmR0 : ∀ k, eN (m k) ≤ R0 := fun k => hR0 ▸
    Finset.single_le_sum (f := fun i => eN (m i)) (fun i _ => eN_nonneg _) (Finset.mem_univ k)
  have hGs : gramOf H (fun i => s *ᵥ m i) * Γi = 1 := by rw [gram_image H s hs m]; exact hG
  have hRR : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK
  have hsmR : ∀ k, eN (s *ᵥ m k) ≤ Real.sqrt K := fun k => by
    have h := Real.abs_le_sqrt ((eN_sq _).trans_le (hsm k) : eN (s *ᵥ m k) ^ 2 ≤ K)
    rwa [abs_of_nonneg (eN_nonneg _)] at h
  have hu_orth : ∀ j, herm H (x - proj H Γi m x) (m j) = 0 := proj_orth H Γi m hG x
  have hub : eN (x - proj H Γi m x) ≤ (1 + N * A * R0 * R0) * eN x := by
    have h1 := proj_bound H hH hHH Γi m R0 hR00 hmR0 x
    rw [← hA, ← hN] at h1
    calc eN (x - proj H Γi m x) ≤ eN x + eN (proj H Γi m x) := eN_sub _ _
      _ ≤ eN x + N * (A * (eN x * R0)) * R0 := by linarith
      _ = (1 + N * A * R0 * R0) * eN x := by ring
  have hsp : eN (s *ᵥ proj H Γi m x) ≤ N * A * R0 * Real.sqrt K * eN x := by
    have h1 : s *ᵥ proj H Γi m x = ∑ i, coef H Γi m x i • (s *ᵥ m i) := by
      unfold proj
      rw [mulVec_sum]
      simp_rw [mulVec_smul]
    rw [h1]
    have h2 := lincomb_bound (coef H Γi m x) (fun i => s *ᵥ m i) (A * (eN x * R0)) (Real.sqrt K)
      (Real.sqrt_nonneg _) (fun i => hA ▸ coef_bound H hH hHH Γi m R0 hmR0 x i) hsmR
    rw [← hN] at h2
    calc _ ≤ N * (A * (eN x * R0)) * Real.sqrt K := h2
      _ = N * A * R0 * Real.sqrt K * eN x := by ring
  have hv_orth : ∀ j, herm H (s *ᵥ (x - proj H Γi m x)) (s *ᵥ m j) = 0 := fun j => by
    rw [herm_iso H s hs]
    exact hu_orth j
  have hv := orth_bound H hH hHH Γi (fun i => s *ᵥ m i) hGs (Real.sqrt K) (Real.sqrt_nonneg _) hsmR
    (psd_image H s hHH hs m hpsd) _ hv_orth
  rw [← hA, ← hN, hRR, herm_iso H s hs] at hv
  have hvv : (herm H (x - proj H Γi m x) (x - proj H Γi m x)).re ≤
      (1 + N * A * R0 * R0) ^ 2 * nsq x := by
    calc (herm H (x - proj H Γi m x) (x - proj H Γi m x)).re
        ≤ ‖herm H (x - proj H Γi m x) (x - proj H Γi m x)‖ := Complex.re_le_norm _
      _ ≤ eN (x - proj H Γi m x) * eN (x - proj H Γi m x) := herm_le H hH hHH _ _
      _ ≤ ((1 + N * A * R0 * R0) * eN x) * ((1 + N * A * R0 * R0) * eN x) :=
          mul_le_mul hub hub (eN_nonneg _) ((eN_nonneg _).trans hub)
      _ = (1 + N * A * R0 * R0) ^ 2 * nsq x := by rw [← eN_sq]; ring
  have hc1 : 0 ≤ 1 + N * A * K := by have := mul_nonneg hD0 hK; linarith
  have hnv : nsq (s *ᵥ (x - proj H Γi m x)) ≤ (1 + N * A * K) * ((1 + N * A * R0 * R0) ^ 2 * nsq x) :=
    hv.trans (mul_le_mul_of_nonneg_left hvv hc1)
  have hX : 0 ≤ nsq x := by rw [← eN_sq]; positivity
  have hsx : eN (s *ᵥ x) ≤ eN (s *ᵥ proj H Γi m x) + eN (s *ᵥ (x - proj H Γi m x)) := by
    have hx : x = proj H Γi m x + (x - proj H Γi m x) := by abel
    calc eN (s *ᵥ x) = eN (s *ᵥ (proj H Γi m x + (x - proj H Γi m x))) := by rw [← hx]
      _ = eN (s *ᵥ proj H Γi m x + s *ᵥ (x - proj H Γi m x)) := by rw [mulVec_add]
      _ ≤ _ := eN_add _ _
  have ha2 : eN (s *ᵥ proj H Γi m x) ^ 2 ≤ (N * A) ^ 2 * R0 ^ 2 * K * nsq x := by
    have h1 := pow_le_pow_left₀ (eN_nonneg _) hsp 2
    calc eN (s *ᵥ proj H Γi m x) ^ 2 ≤ (N * A * R0 * Real.sqrt K * eN x) ^ 2 := h1
      _ = (N * A) ^ 2 * R0 ^ 2 * (Real.sqrt K * Real.sqrt K) * eN x ^ 2 := by ring
      _ = (N * A) ^ 2 * R0 ^ 2 * K * nsq x := by rw [hRR, eN_sq]
  have hsum : nsq (s *ᵥ x) ≤ 2 * eN (s *ᵥ proj H Γi m x) ^ 2 +
      2 * nsq (s *ᵥ (x - proj H Γi m x)) := by
    rw [← eN_sq, ← eN_sq (s *ᵥ (x - proj H Γi m x))]
    have h1 := pow_le_pow_left₀ (eN_nonneg _) hsx 2
    nlinarith [sq_nonneg (eN (s *ᵥ proj H Γi m x) - eN (s *ᵥ (x - proj H Γi m x)))]
  unfold cIso
  exact hsum.trans (final_alg (N * A) R0 (1 + N * A * R0 * R0) K (1 + N * A * K) (nsq x) _ _
    hD0 hK hX rfl ha2 hnv)

theorem nsq_cont : Continuous fun x : Fin n → ℂ => nsq x := by
  show Continuous fun x : Fin n → ℂ => ∑ i, Complex.normSq (x i)
  exact continuous_finset_sum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

theorem eN_eq_sqrt (x : Fin n → ℂ) : eN x = Real.sqrt (nsq x) := by
  rw [eN, EuclideanSpace.norm_eq]
  simp [nsq, Complex.normSq_eq_norm_sq]

theorem eN_cont : Continuous fun x : Fin n → ℂ => eN x := by
  have e : (fun x : Fin n → ℂ => eN x) = fun x => Real.sqrt (nsq x) := funext eN_eq_sqrt
  rw [e]
  exact Real.continuous_sqrt.comp nsq_cont

theorem gramOf_cont {X : Type*} [TopologicalSpace X] (H : Matrix (Fin n) (Fin n) ℂ) (m : X → ι → Fin n → ℂ)
    (Kx : Set X) (hm : ContinuousOn m Kx) : ContinuousOn (fun x => gramOf H (m x)) Kx := by
  have hmi : ∀ i l, ContinuousOn (fun x => m x i l) Kx := fun i l =>
    continuousOn_pi.1 (continuousOn_pi.1 hm i) l
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [gramOf, Matrix.of_apply, herm, dotProduct, Matrix.mulVec, Pi.star_apply]
  refine continuousOn_finset_sum _ fun l _ => ?_
  refine ((hmi i l).star).mul ?_
  exact continuousOn_finset_sum _ fun q _ => continuousOn_const.mul (hmi j q)

theorem isoUnif {X : Type*} [TopologicalSpace X] (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H)
    (hHH : H * H = 1) (m : X → ι → Fin n → ℂ) (Kx : Set X) (hK : IsCompact Kx) (hm : ContinuousOn m Kx)
    (hdet : ∀ x ∈ Kx, IsUnit (gramOf H (m x)).det)
    (hpsd : ∀ x ∈ Kx, ∀ v, (∀ i, herm H v (m x i) = 0) → 0 ≤ (herm H v v).re) :
    ∃ C : ℝ, ∀ x ∈ Kx, ∀ s : Matrix (Fin n) (Fin n) ℂ, sᴴ * H * s = H → ∀ K : ℝ, 0 ≤ K →
      (∀ i, nsq (s *ᵥ m x i) ≤ K) → ∀ v, nsq (s *ᵥ v) ≤ C * (1 + K) ^ 2 * nsq v := by
  classical
  have hG := gramOf_cont H m Kx hm
  have e : ∀ x, (gramOf H (m x))⁻¹ = (gramOf H (m x)).det⁻¹ • (gramOf H (m x)).adjugate := fun x => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hinv : ContinuousOn (fun x => (gramOf H (m x))⁻¹) Kx := by
    have h1 : ContinuousOn (fun x => ((gramOf H (m x)).det)⁻¹) Kx :=
      ((continuous_id.matrix_det).comp_continuousOn hG).inv₀ fun x hx => (hdet x hx).ne_zero
    have h2 : ContinuousOn (fun x => (gramOf H (m x)).adjugate) Kx :=
      (continuous_id.matrix_adjugate).comp_continuousOn hG
    have h3 : ContinuousOn (fun x => ((gramOf H (m x)).det)⁻¹ • (gramOf H (m x)).adjugate) Kx := h1.smul h2
    exact h3.congr fun x _ => e x
  have hA : ContinuousOn (fun x => ∑ j, ∑ k, ‖(gramOf H (m x))⁻¹ j k‖) Kx :=
    continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun k _ =>
      continuous_norm.comp_continuousOn (continuousOn_pi.1 (continuousOn_pi.1 hinv j) k)
  have hR : ContinuousOn (fun x => ∑ i, eN (m x i)) Kx :=
    continuousOn_finset_sum _ fun i _ => eN_cont.comp_continuousOn (continuousOn_pi.1 hm i)
  have hc : ContinuousOn (fun x => cIso (Fintype.card ι) (∑ j, ∑ k, ‖(gramOf H (m x))⁻¹ j k‖)
      (∑ i, eN (m x i))) Kx := by
    simp only [cIso]
    fun_prop
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  refine ⟨C, fun x hx s hs K' hK' hsm v => ?_⟩
  have h1 := isoExpl H (m x) hH hHH (gramOf H (m x))⁻¹ (Matrix.mul_nonsing_inv _ (hdet x hx)) (hpsd x hx)
    s hs K' hK' hsm v
  have hn : 0 ≤ nsq v := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hcC := hC ⟨x, hx, rfl⟩
  exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC (sq_nonneg _)) hn)

end iso

section fibre

variable {k r : ℕ}

theorem fix_of_S (z : Fin (2 * r + k + 1) → ℂ) (hz : C2.StdZ k r z) {s : B.Mat k r} (hs : s ∈ Sset k r z)
    (hu : C2.uMap k r z s = 1) (b : Fin (r + 1)) : s *ᵥ fvec k r z b = fvec k r z b := by
  rw [((unipotent_map_frame k r z hz).1 s hs).1 b, hu]
  simp [Matrix.one_apply]

theorem uw_fix (z : Fin (2 * r + k + 1) → ℂ) (hz : C2.StdZ k r z) {h : B.Mat k r} (hh : h ∈ UWset k r z)
    (b : Fin (r + 1)) : h *ᵥ fvec k r z b = fvec k r z b := by
  obtain ⟨-, h1, h2⟩ := hh
  unfold fvec
  split_ifs with hb
  · exact (h1 ⟨b.val, hb⟩).1
  · exact h2

theorem flagStabilizer_fixes_frame (z : Fin (2 * r + k + 1) → ℂ) (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ C2.N0set k r z)
    (b : Fin (r + 1)) : n *ᵥ fvec k r z b = fvec k r z b := by
  obtain ⟨hN, hU⟩ := hn
  have h1 : (1 : B.Mat k r) ∈ UWset k r z := by
    refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
    show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  exact fix_of_S z hz ⟨1, h1, n, hN, (one_mul n).symm⟩ hU b

theorem inv_fix {s : B.Mat k r} (hs : s ∈ B.GV k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : s *ᵥ v = v) :
    s⁻¹ *ᵥ v = v := by
  have h1 : s⁻¹ * s = 1 := ((gvGroup k r).2 s hs).2.2.2
  calc s⁻¹ *ᵥ v = s⁻¹ *ᵥ (s *ᵥ v) := by rw [hv]
    _ = (s⁻¹ * s) *ᵥ v := by rw [Matrix.mulVec_mulVec]
    _ = v := by rw [h1, Matrix.one_mulVec]

theorem gramVec_cont (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => gramVec k r z z' g := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl a => exact continuous_const
  | inr b => exact continuous_id.matrix_mulVec continuous_const

theorem gram_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    gramOf (Hpk k r) (gramVec k r z z' g) = gramM k r z z' g := by
  ext i j
  rfl

theorem fam_det (z z' : Fin (2 * r + k + 1) → ℂ) (hstd : C2.Std k r z z') {g : B.Mat k r}
    (hpos : C2.PosPt k r z z' g) : IsUnit (gramOf (Hpk k r) (gramVec k r z z' g)).det := by
  obtain ⟨-, ⟨hz, -⟩, ⟨hz', -⟩⟩ := hstd
  have h := gGram k r z z' hz hz' g hpos.1
  rw [gram_eq]
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  have h2 : Gf k r z z' g = 0 := by exact_mod_cast h
  linarith [hpos.2]

theorem fam_psd (z z' : Fin (2 * r + k + 1) → ℂ) (hstd : C2.Std k r z z') {g : B.Mat k r}
    (hpos : C2.PosPt k r z z' g) (x : Fin (2 * r + k + 1) → ℂ)
    (hx : ∀ i, herm (Hpk k r) x (gramVec k r z z' g i) = 0) : 0 ≤ (herm (Hpk k r) x x).re := by
  by_cases h0 : x = 0
  · subst h0
    simp [herm]
  · have hmem : x ∈ C2.Uperp k r z z' g := by
      rw [C2.Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
      funext i
      have h1 := hx i
      simp only [herm] at h1
      simpa [Matrix.mulVec, dotProduct, Pi.star_apply] using h1
    exact ((gram_independent_signature' k r z z' g hstd hpos).2.2.1 x hmem h0).le

theorem fibreProper (z z' : Fin (2 * r + k + 1) → ℂ) (hstd : C2.Std k r z z') (Kg : Set (B.Mat k r))
    (hK : IsCompact Kg) (hKpos : ∀ g ∈ Kg, C2.PosPt k r z z' g) (R : ℝ) :
    ∃ Rp : ℝ, ∀ g ∈ Kg, ∀ h ∈ UWset k r z, ∀ n ∈ C2.N0set k r z, ∀ h' ∈ UWset k r z',
      ∀ n' ∈ C2.N0set k r z', B.gN (h⁻¹ * n⁻¹ * g * n' * h') ≤ R →
        B.gN h ≤ Rp ∧ B.gN n ≤ Rp ∧ B.gN h' ≤ Rp ∧ B.gN n' ≤ Rp := by
  have hz : C2.StdZ k r z := hstd.2.1
  have hz' : C2.StdZ k r z' := hstd.2.2
  have hH : (Hpk k r)ᴴ = Hpk k r := GN.hpk_herm k r
  have hHH : Hpk k r * Hpk k r = 1 := GN.hpk_sq k r
  obtain ⟨Cu, hCu⟩ := (PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact k r z hz.1 hz.2).exists_bound_of_continuousOn
    (PI.UnitaryGroupMassFormula.DLm.gN_cont k r).continuousOn
  obtain ⟨Cu', hCu'⟩ := (PI.QuotSetU.UnitaryGroupMassFormula.unitary_weyl_compact k r z' hz'.1 hz'.2).exists_bound_of_continuousOn
    (PI.UnitaryGroupMassFormula.DLm.gN_cont k r).continuousOn
  have hUb : ∀ h ∈ UWset k r z, B.gN h ≤ Cu := fun h hh =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hCu h hh)
  have hUb' : ∀ h ∈ UWset k r z', B.gN h ≤ Cu' := fun h hh =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hCu' h hh)
  obtain ⟨C1, hC1⟩ := isoUnif (Hpk k r) hH hHH (fun g => gramVec k r z z' g) Kg hK
    (gramVec_cont z z').continuousOn (fun g hg => fam_det z z' hstd (hKpos g hg))
    (fun g hg => fam_psd z z' hstd (hKpos g hg))
  have hc2 : Continuous fun g : B.Mat k r => fun i => (Hpk k r * gᴴ * Hpk k r) *ᵥ gramVec k r z z' g i :=
    continuous_pi fun i => ((continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const).matrix_mulVec
      ((continuous_apply i).comp (gramVec_cont z z'))
  have hinvG : ∀ g ∈ Kg, (Hpk k r * gᴴ * Hpk k r) = g⁻¹ := fun g hg => (GN.inv_eq (hKpos g hg).1).symm
  obtain ⟨C2, hC2⟩ := isoUnif (Hpk k r) hH hHH
    (fun g i => (Hpk k r * gᴴ * Hpk k r) *ᵥ gramVec k r z z' g i) Kg hK hc2.continuousOn
    (fun g hg => by
      rw [hinvG g hg, gram_image (Hpk k r) g⁻¹ (GN.inv_mem (hKpos g hg).1)]
      exact fam_det z z' hstd (hKpos g hg))
    (fun g hg => by
      rw [hinvG g hg]
      exact psd_image (Hpk k r) g⁻¹ hHH (GN.inv_mem (hKpos g hg).1) _ (fam_psd z z' hstd (hKpos g hg)))
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℝ, Kf = ∑ a, nsq (fvec k r z a) + ∑ b, nsq (fvec k r z' b) := ⟨_, rfl⟩
  have hKf0 : 0 ≤ Kf := hKf ▸ add_nonneg (Finset.sum_nonneg fun a _ => by rw [← eN_sq]; positivity)
    (Finset.sum_nonneg fun a _ => by rw [← eN_sq]; positivity)
  have hfa : ∀ a, nsq (fvec k r z a) ≤ Kf := fun a => by
    have h1 := Finset.single_le_sum (f := fun a => nsq (fvec k r z a))
      (fun a _ => by rw [← eN_sq]; positivity) (Finset.mem_univ a)
    have h2 : 0 ≤ ∑ b, nsq (fvec k r z' b) := Finset.sum_nonneg fun a _ => by rw [← eN_sq]; positivity
    rw [hKf]; linarith
  have hfb : ∀ b, nsq (fvec k r z' b) ≤ Kf := fun b => by
    have h1 := Finset.single_le_sum (f := fun b => nsq (fvec k r z' b))
      (fun a _ => by rw [← eN_sq]; positivity) (Finset.mem_univ b)
    have h2 : 0 ≤ ∑ a, nsq (fvec k r z a) := Finset.sum_nonneg fun a _ => by rw [← eN_sq]; positivity
    rw [hKf]; linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Kf + R ^ 2 * Kf := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hKdef ▸ add_nonneg hKf0 (mul_nonneg (sq_nonneg _) hKf0)
  obtain ⟨Bv, hBv⟩ : ∃ Bv : ℝ, Bv = ∑ j, nsq (bvec j : Fin (2 * r + k + 1) → ℂ) := ⟨_, rfl⟩
  have hBv0 : 0 ≤ Bv := hBv ▸ Finset.sum_nonneg fun a _ => by rw [← eN_sq]; positivity

  have hcols : ∀ (C : ℝ) (t : B.Mat k r), (∀ v, nsq (t *ᵥ v) ≤ C * (1 + K) ^ 2 * nsq v) →
      B.gN t ≤ Real.sqrt (C * (1 + K) ^ 2 * Bv) := fun C t ht => by
    apply Real.le_sqrt_of_sq_le
    rw [gN_sq_cols, hBv, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => ht _
  refine ⟨max (max Cu Cu') (max (Cu * Real.sqrt (C1 * (1 + K) ^ 2 * Bv))
    (Cu' * Real.sqrt (C2 * (1 + K) ^ 2 * Bv))), ?_⟩
  intro g hg h hh n hn h' hh' n' hn' hy
  have hhG : h ∈ B.GV k r := hh.1
  have hnG : n ∈ B.GV k r := hn.1.1
  have hh'G : h' ∈ B.GV k r := hh'.1
  have hn'G : n' ∈ B.GV k r := hn'.1.1
  have hgG : g ∈ B.GV k r := (hKpos g hg).1
  obtain ⟨y, hydef⟩ : ∃ y, y = h⁻¹ * n⁻¹ * g * n' * h' := ⟨_, rfl⟩
  rw [← hydef] at hy
  have hyG : y ∈ B.GV k r := by
    rw [hydef]
    exact GN.mul_mem (GN.mul_mem (GN.mul_mem (GN.mul_mem (GN.inv_mem hhG) (GN.inv_mem hnG))
    hgG) hn'G) hh'G
  have hy0 : 0 ≤ B.gN y := GN.gN_nonneg y
  have hy2 : B.gN y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have hCu0 : 0 ≤ Cu := (GN.gN_nonneg h).trans (hUb h hh)
  have hCu0' : 0 ≤ Cu' := (GN.gN_nonneg h').trans (hUb' h' hh')

  obtain ⟨t, htdef⟩ : ∃ t, t = h⁻¹ * n⁻¹ := ⟨_, rfl⟩
  have htG : t ∈ B.GV k r := by
    rw [htdef]
    exact GN.mul_mem (GN.inv_mem hhG) (GN.inv_mem hnG)
  have htf : ∀ a, t *ᵥ fvec k r z a = fvec k r z a := fun a => by
    rw [htdef, ← mulVec_mulVec, inv_fix hnG (flagStabilizer_fixes_frame z hz hn a), inv_fix hhG (uw_fix z hz hh a)]
  have hty : ∀ b, t *ᵥ (g *ᵥ fvec k r z' b) = y *ᵥ fvec k r z' b := fun b => by
    rw [hydef, htdef]
    conv_rhs => rw [← mulVec_mulVec, uw_fix z' hz' hh' b, ← mulVec_mulVec, flagStabilizer_fixes_frame z' hz' hn' b]
    rw [mulVec_mulVec]
  have ht := hC1 g hg t htG K hK0 (fun i => by
    rcases i with a | b
    · show nsq (t *ᵥ fvec k r z a) ≤ K
      rw [htf a]
      have := hfa a
      rw [hKdef]; linarith [mul_nonneg (sq_nonneg R) hKf0]
    · show nsq (t *ᵥ (g *ᵥ fvec k r z' b)) ≤ K
      rw [hty b]
      calc nsq (y *ᵥ fvec k r z' b) ≤ B.gN y ^ 2 * nsq (fvec k r z' b) := nsq_mulVec_le _ _
        _ ≤ R ^ 2 * Kf := mul_le_mul hy2 (hfb b) (by rw [← eN_sq]; positivity) (sq_nonneg _)
        _ ≤ K := by rw [hKdef]; linarith)
  have htb := hcols C1 t ht

  obtain ⟨t', ht'def⟩ : ∃ t', t' = h'⁻¹ * n'⁻¹ := ⟨_, rfl⟩
  have ht'G : t' ∈ B.GV k r := by
    rw [ht'def]
    exact GN.mul_mem (GN.inv_mem hh'G) (GN.inv_mem hn'G)
  have ht'f : ∀ b, t' *ᵥ fvec k r z' b = fvec k r z' b := fun b => by
    rw [ht'def, ← mulVec_mulVec, inv_fix hn'G (flagStabilizer_fixes_frame z' hz' hn' b), inv_fix hh'G (uw_fix z' hz' hh' b)]
  have hyinv : y⁻¹ = h'⁻¹ * n'⁻¹ * g⁻¹ * n * h := by
    rw [hydef]
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (GN.det_isUnit hnG),
      Matrix.nonsing_inv_nonsing_inv _ (GN.det_isUnit hhG), Matrix.mul_assoc]
  have ht'y : ∀ a, t' *ᵥ (g⁻¹ *ᵥ fvec k r z a) = y⁻¹ *ᵥ fvec k r z a := fun a => by
    rw [hyinv, ht'def]
    conv_rhs => rw [← mulVec_mulVec, uw_fix z hz hh a, ← mulVec_mulVec, flagStabilizer_fixes_frame z hz hn a]
    rw [mulVec_mulVec]
  have ht' := hC2 g hg t' ht'G K hK0 (fun i => by
    rcases i with a | b
    · show nsq (t' *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z a)) ≤ K
      rw [hinvG g hg, ht'y a]
      calc nsq (y⁻¹ *ᵥ fvec k r z a) ≤ B.gN y⁻¹ ^ 2 * nsq (fvec k r z a) := nsq_mulVec_le _ _
        _ = B.gN y ^ 2 * nsq (fvec k r z a) := by rw [GN.gN_inv hyG]
        _ ≤ R ^ 2 * Kf := mul_le_mul hy2 (hfa a) (by rw [← eN_sq]; positivity) (sq_nonneg _)
        _ ≤ K := by rw [hKdef]; linarith
    · show nsq (t' *ᵥ ((Hpk k r * gᴴ * Hpk k r) *ᵥ (g *ᵥ fvec k r z' b))) ≤ K
      rw [hinvG g hg, mulVec_mulVec (fvec k r z' b) g⁻¹ g, GN.inv_mul hgG, one_mulVec, ht'f b]
      have := hfb b
      rw [hKdef]; linarith [mul_nonneg (sq_nonneg R) hKf0])
  have ht'b := hcols C2 t' ht'

  have hnt : n⁻¹ = h * t := by
    rw [htdef, ← Matrix.mul_assoc, GN.mul_inv hhG, Matrix.one_mul]
  have hnt' : n'⁻¹ = h' * t' := by
    rw [ht'def, ← Matrix.mul_assoc, GN.mul_inv hh'G, Matrix.one_mul]
  have hnb : B.gN n ≤ Cu * Real.sqrt (C1 * (1 + K) ^ 2 * Bv) := by
    rw [← GN.gN_inv hnG, hnt]
    exact (GN.gN_mul_le _ _).trans (mul_le_mul (hUb h hh) htb (GN.gN_nonneg _) hCu0)
  have hnb' : B.gN n' ≤ Cu' * Real.sqrt (C2 * (1 + K) ^ 2 * Bv) := by
    rw [← GN.gN_inv hn'G, hnt']
    exact (GN.gN_mul_le _ _).trans (mul_le_mul (hUb' h' hh') ht'b (GN.gN_nonneg _) hCu0')
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hUb h hh).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact hnb.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hUb' h' hh').trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact hnb'.trans ((le_max_right _ _).trans (le_max_right _ _))

end fibre

end

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
