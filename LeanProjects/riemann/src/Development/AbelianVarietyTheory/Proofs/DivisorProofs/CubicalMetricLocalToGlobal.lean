import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDeterminedByCurvatureZeroSectionStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.CubicalGlue

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cov_mono {U V : Set E} (h : V ⊆ U) : cov V g ⊆ cov U g :=
  Set.prod_mono h subset_rfl

theorem isOpen_cov {U : Set E} (hU : IsOpen U) : IsOpen (cov U g) :=
  hU.prod isOpen_univ

theorem isMetric_mono {U V : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}
    (hm : IsMetric U τ M j h) (hVU : V ⊆ U) : IsMetric V τ M j h :=
  ⟨hm.1.mono (cov_mono hVU), fun P hP => hm.2.1 P (cov_mono hVU hP),
    fun l hl P hP => hm.2.2 l hl P (cov_mono hVU hP)⟩

theorem ddc_congr {u u' : Pt E g → ℝ} {P : Pt E g} (h : u =ᶠ[nhds P] u') :
    ddc u P = ddc u' P := by
  have h1 : fderiv ℝ u =ᶠ[nhds P] fderiv ℝ u' := h.fderiv
  have h2 : ∀ v : Pt E g, (fun Q => fderiv ℝ u Q (Complex.I • v)) =ᶠ[nhds P]
      (fun Q => fderiv ℝ u' Q (Complex.I • v)) := fun v => h1.mono fun Q hQ => by simp only [hQ]
  funext v w
  unfold ddc
  rw [(h2 v).fderiv_eq, (h2 w).fderiv_eq]

theorem agree_on_inter [FiniteDimensional ℂ E] {B U U' : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {j : Fl g → Pt E g → ℂ}
    {r : E → ℂ} {h h' : Pt E g → ℝ} (hU : IsOpen U) (hUB : U ⊆ B) (hU' : IsOpen U')
    (hh : IsCubicalMetric U τ j r h) (hh' : IsCubicalMetric U' τ j r h') :
    Set.EqOn h h' (cov (U ∩ U') g) := by
  have hp : IsPeriodMap (U ∩ U') τ :=
    ⟨hU.inter hU', fun i k => (hτ.2.1 i k).mono (Set.inter_subset_left.trans hUB),
      fun b hb => hτ.2.2 b (hUB hb.1)⟩
  refine GlobalTheory.T.metric_determined_by_curvature_zero_section hp j h h' (isMetric_mono hh.1 Set.inter_subset_left)
    (isMetric_mono hh'.1 Set.inter_subset_right) ?_ ?_
  · intro P hP v w
    have e1 := hh.2.1 P (cov_mono Set.inter_subset_left hP) v w
    have e2 := hh'.2.1 P (cov_mono Set.inter_subset_right hP) v w
    linarith
  · intro b hb
    have e1 := hh.2.2 b hb.1
    have e2 := hh'.2.2 b hb.2
    have hne : ‖r b‖ ^ 2 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e1
      exact zero_ne_one e1
    exact mul_right_cancel₀ hne (e1.trans e2.symm)

end GlobalTheory.CubicalGlue

open GlobalTheory.CubicalGlue in

theorem GlobalTheory.cubicalMetric_exists_of_local : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), (∀ b₀ ∈ B, ∃ U : Set E, IsOpen U ∧ b₀ ∈ U ∧ U ⊆ B ∧ ∃ h, IsCubicalMetric U τ j r h) → ∃ h, IsCubicalMetric B τ j r h := by
  intro g E _ _ _ B τ hτ j r hloc
  classical
  choose U hUo hbU hUB hh hcub using hloc
  let H : Pt E g → ℝ := fun P => if hP : P.1 ∈ B then hh P.1 hP P else 1
  have key : ∀ b (hb : b ∈ B), ∀ Q ∈ cov (U b hb) g, H Q = hh b hb Q := by
    intro b hb Q hQ
    have hQB : Q.1 ∈ B := hUB b hb hQ.1
    simp only [H, dif_pos hQB]
    exact agree_on_inter hτ (hUo _ hQB) (hUB _ hQB) (hUo b hb) (hcub _ hQB) (hcub b hb)
      ⟨⟨hbU _ hQB, hQ.1⟩, trivial⟩
  have mem : ∀ P : Pt E g, ∀ hb : P.1 ∈ B, P ∈ cov (U P.1 hb) g := fun P hb =>
    ⟨hbU _ hb, trivial⟩
  have hev : ∀ P : Pt E g, ∀ hb : P.1 ∈ B, H =ᶠ[nhds P] hh P.1 hb := fun P hb =>
    Filter.eventually_of_mem ((isOpen_cov (hUo _ hb)).mem_nhds (mem P hb)) (key _ hb)
  refine ⟨H, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun P hP => ⟨cov (U P.1 hP.1) g,
      isOpen_cov (hUo _ hP.1), mem P hP.1, ?_⟩
    exact ((hcub _ hP.1).1.1.congr (fun Q hQ => key _ hP.1 Q hQ)).mono Set.inter_subset_right
  · intro P hP
    rw [key _ hP.1 P (mem P hP.1)]
    exact (hcub _ hP.1).1.2.1 P (mem P hP.1)
  · intro l hl P hP
    have hm : transl τ l P ∈ cov (U P.1 hP.1) g := mem P hP.1
    rw [key _ hP.1 P (mem P hP.1), key _ hP.1 _ hm]
    exact (hcub _ hP.1).1.2.2 l hl P (mem P hP.1)
  · intro P hP v w
    have hl : (fun Q => Real.log (H Q)) =ᶠ[nhds P] fun Q => Real.log (hh P.1 hP.1 Q) :=
      (hev P hP.1).mono fun Q hQ => by simp only [hQ]
    rw [ddc_congr hl]
    exact (hcub _ hP.1).2.1 P (mem P hP.1) v w
  · intro b hb
    rw [key b hb (zeroSec g b) ⟨hbU b hb, trivial⟩]
    exact (hcub b hb).2.2 b (hbU b hb)
