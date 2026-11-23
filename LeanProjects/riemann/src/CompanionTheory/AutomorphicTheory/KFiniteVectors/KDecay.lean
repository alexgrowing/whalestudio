import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup

namespace MainStatements.BetaInf

open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.Main
open scoped InnerProductSpace

noncomputable section

def sN {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖

theorem sN_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ sN g := by
  unfold sN; positivity

theorem gap_step {n : ℕ} {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (s : Fin n) : PI.ZuckTensor.GapAtLeast ε (μ + Pi.single s 1) (h - 1) := by
  intro a b hab
  have h1 := hg a b hab
  have h2 : |(Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b| ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have e : μ a - μ b = ((μ + Pi.single s 1 : Fin n → ℝ) a - (μ + Pi.single s 1 : Fin n → ℝ) b) -
      ((Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b) := by
    simp only [Pi.add_apply]; ring
  rw [e] at h1
  linarith [abs_sub ((μ + Pi.single s 1 : Fin n → ℝ) a - (μ + Pi.single s 1 : Fin n → ℝ) b)
    ((Pi.single s 1 : Fin n → ℝ) a - (Pi.single s 1 : Fin n → ℝ) b)]

theorem decay_J {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) {n : ℕ} (ε : Fin n → Bool) :
    ∀ (m : ℕ) (h : ℝ) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam μ → IsDS ε μ σ → PI.ZuckTensor.GapAtLeast ε μ h →
      t n ε + m < h → ∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      ∃ C : ℝ, ∀ g ∈ UJset ε, sN g ^ m * ‖⟪w, σ g v⟫_ℂ‖ ≤ C := by
  intro m
  induction m with
  | zero =>
    intro h μ H _ _ _ σ _ hσ _ _ v w _ _
    refine ⟨‖w‖ * ‖v‖, fun g hg => ?_⟩
    rw [pow_zero, one_mul, ← hσ.2.2.1.2.1 g hg v]
    exact norm_inner_le_norm _ _
  | succ m ih =>
    intro h μ H _ _ _ σ hμ hσ hgap hlt v w hv hw
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hlt
    obtain ⟨X⟩ := hZ n ε μ H σ hμ hσ h hgap (by linarith)
    have key : ∀ i j : Fin n, ∃ C : ℝ, ∀ g ∈ UJset ε, sN g ^ m * (‖⟪w, σ g v⟫_ℂ‖ * ‖g i j‖) ≤ C := by
      intro i j
      obtain ⟨ι, _, sI, vI, wI, hI, hsum⟩ := X.toSum v w (Pi.single j 1) (Pi.single i 1) hv hw
      choose C hC using fun a : ι => ih (h - 1) _ (X.Hs (sI a)) (X.σs (sI a)) (X.ds _ (hI a).1).1
        (X.ds _ (hI a).1).2 (gap_step hgap _) (by linarith) (vI a) (wI a) (hI a).2.1 (hI a).2.2
      refine ⟨∑ a, C a, fun g hg => ?_⟩
      have e : star (Pi.single i 1 : Fin n → ℂ) ⬝ᵥ (g *ᵥ Pi.single j 1) = g i j := by
        have : star (Pi.single i 1 : Fin n → ℂ) = Pi.single i 1 := by
          funext a
          simp only [Pi.star_apply, Pi.single_apply]
          split_ifs <;> simp
        rw [this, single_one_dotProduct, Matrix.mulVec_single_one]
        rfl
      have h1 := hsum g hg
      rw [e] at h1
      rw [← norm_mul, h1]
      calc sN g ^ m * ‖∑ a, ⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖
          ≤ sN g ^ m * ∑ a, ‖⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (sN_nonneg g) _)
        _ = ∑ a, sN g ^ m * ‖⟪wI a, X.σs (sI a) g (vI a)⟫_ℂ‖ := Finset.mul_sum _ _ _
        _ ≤ ∑ a, C a := Finset.sum_le_sum fun a _ => hC a g hg
    choose C hC using key
    refine ⟨∑ i, ∑ j, C i j, fun g hg => ?_⟩
    have e : sN g ^ (m + 1) * ‖⟪w, σ g v⟫_ℂ‖ = ∑ i, ∑ j, sN g ^ m * (‖⟪w, σ g v⟫_ℂ‖ * ‖g i j‖) := by
      simp only [← Finset.mul_sum]
      rw [pow_succ]
      unfold sN
      ring
    rw [e]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hC i j g hg

theorem gN_le_sN {k r : ℕ} (g : B.Mat k r) : B.gN g ≤ sN g := by
  unfold B.gN
  rw [Real.sqrt_le_left (sN_nonneg g)]
  unfold sN
  simp only [Complex.normSq_eq_norm_sq]
  calc ∑ i, ∑ j, ‖g i j‖ ^ 2 ≤ ∑ i, (∑ j, ‖g i j‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _
    _ ≤ (∑ i, ∑ j, ‖g i j‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _

theorem conj_back {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P g : B.Mat k r} (hP : IsCayleyU k r ε P)
    (hg : g ∈ Kset ε) :
    P⁻¹ * g * P ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hsg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
  rw [hinv]
  refine ⟨?_, ?_⟩
  · show (star P * g * P)ᴴ * Hpk k r * (star P * g * P) = Hpk k r
    rw [← hP.1.2]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    calc star P * (star g * P) * (star P * Jm ε * P) * (star P * g * P)
        = star P * (star g * ((P * star P) * Jm ε * (P * star P) * g)) * P := by simp only [Matrix.mul_assoc]
      _ = star P * (star g * (g * Jm ε)) * P := by rw [hPs, Matrix.one_mul, Matrix.mul_one, hg.2]
      _ = star P * Jm ε * P := by rw [← Matrix.mul_assoc (star g), hsg, Matrix.one_mul]
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hPu) hg.1) hPu

theorem kDecay_of_zuckT {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (m : ℕ) (A h : ℝ) (hA : A ≤ m) (hlt : t _ ε + m < h) : KDecay k r ε A h := by
  intro μ H _ _ _ σ hμ hσ hgap v w hv hw
  obtain ⟨Q, hQ, hDS⟩ := hσ
  have tr : ∀ x : H, IsKFinHpk (k := k) (r := r) σ x → IsKFin ε (fun g => σ (Q⁻¹ * g * Q)) x := by
    rintro x ⟨S, hS, hx, hst⟩
    exact ⟨S, hS, hx, fun g hg y hy => hst _ (conj_back hQ hg) y hy⟩
  obtain ⟨C, hC⟩ := decay_J hZ ε m h μ H _ hμ hDS hgap hlt v w (tr v hv) (tr w hw)
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  set c : ℝ := B.gN (Q⁻¹ : B.Mat k r) * B.gN (Q : B.Mat k r) with hc
  have hc0 : 0 ≤ c := mul_nonneg (P.B6.gN_nonneg _) (P.B6.gN_nonneg _)
  refine ⟨c ^ m * C, fun g hg => ?_⟩
  have key : Q⁻¹ * (Q * g * Q⁻¹) * Q = g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hdet, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul Q hdet, Matrix.mul_one]
  have h1 := hC _ (P.MatrixMultiplicationContinuity.cayley_maps hQ hg)
  simp only [key] at h1
  have h2 : B.gN g ≤ c * sN (Q * g * Q⁻¹) := by
    have a1 := P.B6.gN_mul_le (Q⁻¹ * (Q * g * Q⁻¹)) Q
    have a2 := P.B6.gN_mul_le Q⁻¹ (Q * g * Q⁻¹)
    have a3 := gN_le_sN (Q * g * Q⁻¹)
    rw [key] at a1
    have q0 := P.B6.gN_nonneg (Q : B.Mat k r)
    have q1 := P.B6.gN_nonneg (Q⁻¹ : B.Mat k r)
    calc B.gN g ≤ B.gN (Q⁻¹ * (Q * g * Q⁻¹)) * B.gN Q := a1
      _ ≤ B.gN Q⁻¹ * sN (Q * g * Q⁻¹) * B.gN Q :=
          mul_le_mul_of_nonneg_right (a2.trans (mul_le_mul_of_nonneg_left a3 q1)) q0
      _ = _ := by rw [hc]; ring
  have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
  calc B.gN g ^ A * ‖⟪w, σ g v⟫_ℂ‖ ≤ B.gN g ^ m * ‖⟪w, σ g v⟫_ℂ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hg1 hA
    _ ≤ (c * sN (Q * g * Q⁻¹)) ^ m * ‖⟪w, σ g v⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h2 m) (norm_nonneg _)
    _ = c ^ m * (sN (Q * g * Q⁻¹) ^ m * ‖⟪w, σ g v⟫_ℂ‖) := by rw [mul_pow, mul_assoc]
    _ ≤ c ^ m * C := mul_le_mul_of_nonneg_left h1 (pow_nonneg hc0 _)

theorem isKFinHpk_of_low {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : B.Mat k r → (H →L[ℂ] H)} {Q : B.Mat k r}
    (hQ : IsCayleyU k r ε Q) {w : H} (hw : w ∈ lowKSub ε lam (fun g => σ (Q⁻¹ * g * Q))) :
    IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Kset ε) (fun g => σ (Q⁻¹ * g * Q))
    (F := {S | IsKTypeOf ε (fun g => σ (Q⁻¹ * g * Q)) (lowK ε lam) S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hw
  refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
  obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hQ hg
  have h := hst _ hK x hx
  simp only at h
  rwa [hback] at h

end

end MainStatements.BetaInf
