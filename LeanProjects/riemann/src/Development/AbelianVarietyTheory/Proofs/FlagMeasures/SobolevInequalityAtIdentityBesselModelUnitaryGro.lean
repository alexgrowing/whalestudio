import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitaryStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff ENNReal

namespace GlobalTheory.SobAtOne

theorem ofReal_list_sum {α : Type*} (S : List α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ENNReal.ofReal (S.map g).sum = (S.map fun a => ENNReal.ofReal (g a)).sum := by
  induction S with
  | nil => simp
  | cons a S ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ENNReal.ofReal_add (hg a) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact hg b), ih]

theorem sobolev_at_one_G : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ)
    (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧
    ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B),
      SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws =>
        ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  intro k r μG hμ
  obtain ⟨-, -, -, ε, -, P, hPd, hPJ⟩ := hpkFacts k r
  have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 hPd
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  obtain ⟨S, C, Q, hQ, hS, hC, hsob⟩ := GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary (2 * r + k + 1) ε
  obtain ⟨c, hc, hB⟩ := GlobalTheory.T.besselUnitary_haar_transport_diagonal k r μG ε P hμ hPd hPJ
  let cj : Mat k r → Mat k r := fun Y => P⁻¹ * Y * P
  have hcjc : Continuous cj := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let ψ : Formalism.REAL.UJ ε → Mt k r := fun y => Matrix.of.symm (cj (umat y))
  have hψc : Continuous ψ := hcjc.comp (Units.continuous_val.comp continuous_subtype_val)
  have hmemG : ∀ g : Mat k r, Formalism.REAL.inUJ ε g → cj g ∈ GG k r := by
    intro g hg
    show cj g ∈ UH (Hpk k r)
    rw [uHConj _ ε (Hpk k r) P hPd hPJ]
    have e : P * cj g * P⁻¹ = g := by
      simp only [cj, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [e]; exact hg
  have hlie : ∀ X, Formalism.REAL.inG ε X → InLieHpk k r (cj X) := by
    intro X hX
    have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
    have e1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPP, conjTranspose_one]
    show (P⁻¹ * X * P)ᴴ * Hpk k r + Hpk k r * (P⁻¹ * X * P) = 0
    rw [← hPJ]
    calc (P⁻¹ * X * P)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) + Pᴴ * Formalism.REAL.Jm ε * P * (P⁻¹ * X * P)
        = Pᴴ * (Xᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (P * P⁻¹) * X) * P := by
          simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [e1, hPP, Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]
  have hwm : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ Y ∈ l.map cj, InLieHpk k r Y := by
    intro l hl Y hY
    obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
    exact hlie Z (hl Z hZ)
  have hK₀ : IsCompact (ψ '' Q) := hQ.image hψc
  have hK₀G : ∀ x ∈ ψ '' Q, Matrix.of x ∈ GG k r := by
    rintro _ ⟨y, -, rfl⟩
    simpa [ψ] using hmemG _ y.2
  have hfin : IsFiniteMeasureOnCompacts μG := by
    obtain ⟨hG, -⟩ := closedSub_groups k r (bvec (wI k r (Fin.last k))) (fun i hi => by
      simp only [bvec, wI]
      rw [Pi.single_apply, if_neg]
      intro h; rw [h] at hi; simp at hi) (by
      have h : herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) =
          Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) := by
        simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [Tz, h]
      simp [Hpk, wI])
    exact ⟨fun K hK => (haarOn_locFinite_openPos k r (GG k r) μG hG hμ).1 K hK⟩
  refine ⟨C * c.toReal, S.map (List.map cj), ψ '' Q, hK₀, ?_, ?_⟩
  · intro ws hws X hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hws
    exact hwm l (hS l hl) X hX
  intro B _ _ _ f hf
  have hword : ∀ l : List (Mat k r), (∀ Y ∈ l, InLieHpk k r Y) → SmoothOnH (Hpk k r) (rdWord l f) := by
    intro l
    induction l with
    | nil => intro _; exact hf
    | cons X l ih =>
      intro hl
      exact (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) X B (rdWord l f) (hl X List.mem_cons_self)
        (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY))).2.1
  have hcont : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (rdWord (l.map cj) f) (GG k r) := fun l hl =>
    (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) 0 B _ (by simp) (hword _ (hwm l hl))).1
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hI : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) →
      ContinuousOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) := fun l hl =>
    (((hcont l hl).comp hof.continuousOn fun x hx => hK₀G x hx).norm).pow 2
  have hnn : 0 ≤ C * c.toReal * ((S.map (List.map cj)).map fun ws =>
      ∫ x in ψ '' Q, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum :=
    mul_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) (List.sum_nonneg fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact integral_nonneg fun _ => by positivity)
  by_cases h0 : f 1 = 0
  · rw [h0, norm_zero]; simpa using hnn
  haveI : Nontrivial B := ⟨⟨f 1, 0, h0⟩⟩
  obtain ⟨ℓ, hℓ1, hℓ⟩ := exists_dual_vector' ℂ (f 1)
  let F : List (Mat k r) → Mat k r → ℂ := fun l g => ℓ (rdWord (l.map cj) f (cj g))
  have hFc : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε) := fun l hl =>
    ℓ.continuous.comp_continuousOn ((hcont l hl).comp hcjc.continuousOn fun g hg => hmemG g hg)
  have hFd : ∀ l : List (Mat k r), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X →
      ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0 := by
    intro l hl X hX g hg
    have hA := (GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group _ (Hpk k r) (cj X) B (rdWord (l.map cj) f) (hlie X hX) (hword _ (hwm l hl))).2.2
      (cj g) (hmemG g hg)
    have h2 := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA
    have e : ∀ t : ℝ, cj (g * NormedSpace.exp ((t : ℂ) • X)) = cj g * NormedSpace.exp ((t : ℂ) • cj X) := by
      intro t
      have e2 : (t : ℂ) • cj X = P⁻¹ * ((t : ℂ) • X) * P := by
        simp only [cj, Matrix.mul_smul, Matrix.smul_mul]
      rw [e2, Matrix.exp_conj' P _ hPu]
      simp only [cj, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P P⁻¹, hPP, Matrix.one_mul]
    have e3 : (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) = (ℓ.restrictScalars ℝ) ∘
        (fun t : ℝ => rdWord (l.map cj) f (cj g * NormedSpace.exp ((t : ℂ) • cj X))) := by
      funext t; simp only [F, Function.comp_apply, e]; rfl
    rw [e3]; exact h2
  have key := hsob F hFc hFd
  have hF1 : ‖F [] 1‖ = ‖f 1‖ := by
    have : cj 1 = 1 := by simp [cj, hPP']
    simp only [F, List.map_nil, this]
    show ‖ℓ (f 1)‖ = ‖f 1‖
    rw [hℓ]; simp
  rw [hF1] at key
  have hstep : ∀ l ∈ S, ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε) ≤
      c * ENNReal.ofReal (∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG) := by
    intro l hlS
    have hl := hS l hlS
    classical
    set φ : Mt k r → ℝ≥0∞ := (ψ '' Q).indicator
      (fun x => ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) with hφ
    have hφm : Measurable φ := by
      have := ContinuousOn.measurable_piecewise (f := fun x : Mt k r =>
        ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2)) (g := 0)
        (ENNReal.continuous_ofReal.comp_continuousOn (hI l hl)) continuousOn_const hK₀.isClosed.measurableSet
      rwa [Set.piecewise_eq_indicator] at this
    have hint : IntegrableOn (fun x : Mt k r => ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2) (ψ '' Q) μG :=
      (hI l hl).integrableOn_compact hK₀
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => by positivity),
      ← lintegral_indicator hK₀.isClosed.measurableSet, ← hφ, ← hB φ hφm]
    refine le_trans ?_ (setLIntegral_le_lintegral Q _)
    refine setLIntegral_mono (hφm.comp hψc.measurable) fun y hy => ?_
    have hψy : ψ y ∈ ψ '' Q := ⟨y, hy, rfl⟩
    have hφy : φ (ψ y) = ENNReal.ofReal (‖rdWord (l.map cj) f (Matrix.of (ψ y))‖ ^ 2) := by
      rw [hφ]; exact Set.indicator_of_mem hψy _
    show _ ≤ φ (ψ y)
    rw [hφy]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    have : (Matrix.of (ψ y) : Mat k r) = cj (umat y) := by simp [ψ]
    rw [this]
    refine (ℓ.le_opNorm _).trans ?_
    rw [hℓ1, one_mul]
  have hsum := List.sum_le_sum hstep
  rw [List.sum_map_mul_left, ← ofReal_list_sum S _ (fun l => integral_nonneg fun _ => by positivity)] at hsum
  have htot : ENNReal.ofReal (‖f 1‖ ^ 2) ≤ ENNReal.ofReal C * (c * ENNReal.ofReal
      ((S.map fun l => ∫ x in ψ '' Q, ‖rdWord (l.map cj) f (Matrix.of x)‖ ^ 2 ∂μG).sum)) := key.trans (by gcongr)
  conv_rhs at htot => rw [← ENNReal.ofReal_toReal hc]
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hC, ← mul_assoc] at htot
  rw [List.map_map] at hnn ⊢
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 htot

end GlobalTheory.SobAtOne

end
