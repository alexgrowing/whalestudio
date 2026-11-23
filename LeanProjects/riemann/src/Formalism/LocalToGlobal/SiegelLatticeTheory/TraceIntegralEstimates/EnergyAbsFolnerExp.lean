import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsFolnerConv

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section General

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

private theorem norm_eq_of_inner_self_eq_inner_self_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : E} (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    have h' := h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    exact_mod_cast h'
  nlinarith [norm_nonneg a, norm_nonneg b]

end General

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def gvec (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x : G) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
  WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w)

def Fk (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (z z' q : G) : ℂ :=
  ⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ

theorem fol_rep_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x : G) (a : HH) : ‖σ x a‖ = ‖a‖ := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  exact norm_eq_of_inner_self_eq_inner_self_lemma (hin x a a)

theorem fol_rep_mul {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ (x * y) a = σ x (σ y a) := by
  obtain ⟨-, hmul, -, -⟩ := id hσ
  calc σ (x * y) a = (σ x * σ y) a := by rw [hmul x y]
    _ = σ x (σ y a) := rfl

theorem W_inner_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x y : G) : ⟪W (s * x), W (s * y)⟫_ℂ = ⟪W x, W y⟫_ℂ := by
  rw [hWeq s hs x, hWeq s hs y, hτu s hs]

theorem W_norm_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x : G) : ‖W (s * x)‖ = ‖W x‖ :=
  norm_eq_of_inner_self_eq_inner_self_lemma (W_inner_trans hWeq hτu hs x x)

theorem gvec_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W) :
    Continuous (gvec σ w W) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hi : ∀ i : Fin (Module.finrank ℂ V),
      Continuous fun x => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w :=
    fun i => (hWc.inner continuous_const).smul (hσc w)
  show Continuous fun x =>
    (WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w) :
      PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hi)

theorem gvec_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) (W : G → V) (x : G) :
    ‖gvec σ w W x‖ = ‖W x‖ := by
  have hn : ‖σ x w‖ = 1 := by rw [(fol_rep_norm hσ), hw]
  have key : ∑ i, ‖⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ‖ ^ 2 = ‖W x‖ ^ 2 := by
    exact (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_left (W x)
  have hs : ‖gvec σ w W x‖ ^ 2 = ‖W x‖ ^ 2 := by
    rw [← key]
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by simp [gvec, norm_smul, hn]
  nlinarith [norm_nonneg (gvec σ w W x), norm_nonneg (W x)]

theorem gvec_inner (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x y : G) :
    ⟪gvec σ w W x, gvec σ w W y⟫_ℂ = ⟪W y, W x⟫_ℂ * ⟪σ x w, σ y w⟫_ℂ := by
  have hb : ∑ i, ⟪W y, stdOrthonormalBasis ℂ V i⟫_ℂ * ⟪stdOrthonormalBasis ℂ V i, W x⟫_ℂ = ⟪W y, W x⟫_ℂ := by
    exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W y) (W x)
  rw [← hb, Finset.sum_mul]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gvec, PiLp.toLp_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem Fk_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    {X : Type} [TopologicalSpace X] {a b c : X → G} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => Fk σ w W (a x) (b x) (c x)) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hcb : Continuous fun x => c x * b x := hc.mul hb
  have h1 : Continuous fun x => W (c x * b x) := hWc.comp hcb
  have h2 : Continuous fun x => W (a x) := hWc.comp ha
  have h3 : Continuous fun x => σ (a x) w := (hσc w).comp ha
  have h4 : Continuous fun x => σ (c x * b x) w := (hσc w).comp hcb
  show Continuous fun x => ⟪W (c x * b x), W (a x)⟫_ℂ * ⟪σ (a x) w, σ (c x * b x) w⟫_ℂ
  exact (h1.inner h2).mul (h3.inner h4)

theorem Fk_bound {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by
  have h1 : ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ := by
    calc ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W (q * z')‖ * ‖W z‖ := norm_inner_le_norm _ _
      _ = ‖W z‖ * ‖W z'‖ := by rw [W_norm_trans hWeq hτu hq z', mul_comm]
  have h2 : ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖σ z w‖ * ‖σ (q * z') w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [(fol_rep_norm hσ), (fol_rep_norm hσ), hw, mul_one]
  show ‖⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖
  rw [norm_mul]
  calc ‖⟪W (q * z'), W z⟫_ℂ‖ * ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ (‖W z‖ * ‖W z'‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖W z‖ * ‖W z'‖ := mul_one _

theorem kF {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hSinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {s t : G} (hs : s ∈ S) :
    ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ * ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = Fk σ w W z z' (s * t⁻¹) := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  have e1 : ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ = ⟪W (s * t⁻¹ * z'), W z⟫_ℂ := by
    rw [← W_inner_trans hWeq hτu hs (t⁻¹ * z') (s⁻¹ * z), mul_assoc, mul_inv_cancel_left]
  have e2 : ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = ⟪σ z w, σ (s * t⁻¹ * z') w⟫_ℂ := by
    rw [← hin s (σ (s⁻¹ * z) w) (σ (t⁻¹ * z') w), ← (fol_rep_mul hσ), ← (fol_rep_mul hσ), mul_inv_cancel_left,
      mul_assoc]
  rw [e1, e2]
  rfl

end Main

end Formalism.L2.S.Pv.EnergyAbs
