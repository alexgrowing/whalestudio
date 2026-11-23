import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParFamIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Ops

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (k ρ) in

def ParOK (T : (Q.Mx k ρ → E) → Q.Mx k ρ → E) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ →
  ∀ f : Par → Q.Mx k ρ → E, PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) →
    PBI.ParFam k ρ U₀ (fun q => T (f q.1) (Matrix.of q.2)) ∧
    (∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∀ W : Set (Par × Mt k ρ), IsOpen W → q ∈ W →
      (∀ q' ∈ W, Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q'.1 (Matrix.of q'.2) = 0) →
      T (f q.1) (Matrix.of q.2) = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (fi : Q.Mx k ρ → E) (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ y' ∈ V, Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) → fi (Matrix.of y') = ∫ Z, f Z (Matrix.of y') ∂ν) →
      T fi (Matrix.of y) = ∫ Z, T (f Z) (Matrix.of y) ∂ν

variable (k ρ) in

def SmoothG (a : Q.Mx k ρ → ℂ) : Prop :=
  ∀ y₀ : Mt k ρ, Matrix.of y₀ ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Mt k ρ)) (F : Mt k ρ → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ y ∈ U, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → a (Matrix.of y) = F y

theorem smoothG_const (s : ℂ) : SmoothG k ρ (fun _ => s) := fun _ _ =>
  ⟨Set.univ, fun _ => s, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothG_mul {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g * b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y * F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).mul (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) * b (Matrix.of y) = F y * F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem smoothG_sub {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g - b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y - F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).sub (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) - b (Matrix.of y) = F y - F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem parFam_congr {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f)
    (h : ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = g q) (hU₀ : IsOpen U₀) :
    PBI.ParFam k ρ U₀ g := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U ∩ U₀, F, hU.inter hU₀, ⟨hqU, hq⟩, hF.mono Set.inter_subset_left,
    fun q hq' hG' => (h q hq'.2 hG').symm.trans (hfF q hq'.1 hG')⟩

theorem parFam_smulG {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a (Matrix.of q.2) • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', A, hU', hqU', hA, haA⟩ := ha q₀.2 hG
  refine ⟨U ∩ Prod.snd ⁻¹' U', fun q => A q.2 • F q, hU.inter (hU'.preimage continuous_snd), ⟨hqU, hqU'⟩, ?_,
    fun q hq' hG' => ?_⟩
  · exact (hA.comp contDiff_snd.contDiffOn (fun q hq => hq.2)).smul (hF.mono Set.inter_subset_left)
  · show a (Matrix.of q.2) • f q = A q.2 • F q
    rw [haA q.2 hq'.2 hG', hfF q hq'.1 hG']

theorem parOK_id : ParOK k ρ (E := E) (fun f => f) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨hf, fun q _ hG W _ hqW hW => hW q hqW hG, fun ν _ Kp _ _ fi y V _ hyV hyG _ hi => hi y hyV hyG⟩

theorem parOK_zero : ParOK k ρ (E := E) (fun _ _ => 0) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨parFam_zero, fun _ _ _ _ _ _ _ => rfl, fun ν _ Kp _ _ fi y V _ _ _ _ _ => by simp⟩

theorem parOK_congr {T T' : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) (h : ∀ f g, T f g = T' f g) :
    ParOK k ρ T' := by
  have e : T = T' := funext fun f => funext fun g => h f g
  rw [← e]; exact hT

theorem parOK_add {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f g => T₁ f g + T₂ f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  refine ⟨parFam_add a₁ a₂, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show T₁ (f q.1) (Matrix.of q.2) + T₂ (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, b₂ q hq hG W hW hqW hz, add_zero]
  · have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    show T₁ fi (Matrix.of y) + T₂ fi (Matrix.of y) = ∫ Z, (T₁ (f Z) (Matrix.of y) + T₂ (f Z) (Matrix.of y)) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, c₂ ν Kp hKp hν fi y V hV hyV hyG hKV hi,
      integral_add (parFam_integrable a₁ hKp hν hyG hKU) (parFam_integrable a₂ hKp hν hyG hKU)]

theorem parOK_smulG {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (hT : ParOK k ρ T) : ParOK k ρ (fun f g => a g • T f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := hT Par U₀ hU₀ f hf
  refine ⟨parFam_smulG ha a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show a (Matrix.of q.2) • T (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, smul_zero]
  · show a (Matrix.of y) • T fi (Matrix.of y) = ∫ Z, a (Matrix.of y) • T (f Z) (Matrix.of y) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, integral_smul]

theorem parOK_csmul (s : ℂ) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) :
    ParOK k ρ (fun f g => s • T f g) := parOK_smulG (smoothG_const s) hT

theorem parOK_neg {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) : ParOK k ρ (fun f g => -T f g) :=
  parOK_congr (parOK_csmul (-1) hT) (fun f g => by simp)

theorem parOK_comp {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f => T₁ (T₂ f)) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ (fun Z => T₂ (f Z)) a₂
  refine ⟨a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · refine b₁ q hq hG (W ∩ U₀) (hW.inter hU₀) ⟨hqW, hq⟩ (fun q' hq' hG' => ?_)
    exact b₂ q' hq'.2 hG' W hW hq'.1 hz
  · refine c₁ ν Kp hKp hν (T₂ fi) y V hV hyV hyG hKV (fun y' hy' hG' => ?_)
    exact c₂ ν Kp hKp hν fi y' V hV hy' hG' hKV hi

theorem parOK_sum {ι : Type} (s : Finset ι) {T : ι → (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (h : ∀ i ∈ s, ParOK k ρ (T i)) : ParOK k ρ (fun f g => ∑ i ∈ s, T i f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact parOK_congr parOK_zero (fun f g => by simp)
  | insert a s ha ih =>
    have := parOK_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact parOK_congr this (fun f g => by simp [Finset.sum_insert ha])

theorem parOK_foldr (L : List ((Q.Mx k ρ → E) → Q.Mx k ρ → E)) (hL : ∀ T ∈ L, ParOK k ρ T) :
    ParOK k ρ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact parOK_id
  | cons T L ih =>
    exact parOK_comp (hL T List.mem_cons_self) (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))

end Ops

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
