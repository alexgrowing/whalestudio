import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA

noncomputable section

open Matrix Filter Topology Set

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcB_path (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)

end PathL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma lcB_hasDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    HasDerivAt (fun s : ℝ => T.op (γ s) * psM T μ (A * NormedSpace.exp ((s : ℂ) • Y))) 0 t := by
  set z := A * NormedSpace.exp ((t : ℂ) • Y) with hz
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • Y) =
      z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) := by
    intro s
    rw [hz, mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    rw [show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  have h1 := lcB_path z Y
  have h2 := hasDerivAt_iff_tendsto_slope.1 h1
  have h3 : HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 :=
    hasDerivAt_iff_tendsto_slope.2 h2
  have h4 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h3)
  have hp : HasDerivAt (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) t := by
    rw [show (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) =
      fun s => z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) from funext hcomm]
    exact h4
  have hF : HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) z) z :=
    (hdiff.differentiableAt (hUo.mem_nhds ht)).hasFDerivAt
  have hF' : HasFDerivAt (psM T μ) ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) z :=
    hF.restrictScalars ℝ
  have hq0 := hF'.comp_hasDerivAt t hp
  have e : ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) (z * Y) = -(T.dτ Y * psM T μ z) := hid z ht
  have hq : HasDerivAt (fun s : ℝ => psM T μ (A * NormedSpace.exp ((s : ℂ) • Y)))
      (-(T.dτ Y * psM T μ z)) t := hq0.congr_deriv e
  have ho1 : HasDerivAt (fun s : ℝ => T.op (γ s)) (T.op (γ t) * T.dτ Y) t := by
    have h5 := (T.hasDeriv Y hY γ hγ).const_mul (T.op (γ t))
    have h6 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h5)
    have he : (fun s : ℝ => T.op (γ s)) =
        fun s => T.op (γ t) * ((T.τ (γ (s - t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext s
      have hs := hmul t (s - t)
      rw [show t + (s - t) = s by ring] at hs
      simp only [KType.op]
      rw [hs, map_mul]
      rfl
    rw [he]
    exact h6
  have hprod := ho1.mul hq
  have hzero : T.op (γ t) * T.dτ Y * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y)) +
      T.op (γ t) * -(T.dτ Y * psM T μ z) = 0 := by
    rw [mul_neg, mul_assoc]
    exact add_neg_cancel _
  exact hzero ▸ hprod

theorem lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc

end ReciprocityTheory.ChartRestriction.DS.S7
