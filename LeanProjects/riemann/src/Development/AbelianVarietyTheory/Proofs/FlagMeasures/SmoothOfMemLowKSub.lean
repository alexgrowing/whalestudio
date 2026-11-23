import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqrtNsqLeOfAbsLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtension
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeGeneratedByHighest
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumNormSqOfIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepBoundOneRep

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem stepConst_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ stepConst n b P := by
  have h1 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg b)
  have h2 : 0 ≤ 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h3 : 0 ≤ 3 * (P : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg P)
  simp only [stepConst]
  linarith

theorem stepSpace_le {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ Vs) (hE : GlRel E)
    (hd : ∀ X, inG ε X → ∀ u : Vs, HasDerivAt (orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (u : Vs) (hu : (kSpan ε E u).map Vs.subtype = lowKSub ε lam σ) (P : ℕ) :
    stepSpace ε lam σ P ≤ (pfil ε E u P).map Vs.subtype := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, inG ε X) → ∀ w ∈ lowKSub ε lam σ,
      ∃ x : Vs, x ∈ pfil ε E u l.length ∧ (x : H) = dWord σ l w := by
    intro l
    induction l with
    | nil =>
      intro _ w hw
      rw [← hu] at hw
      obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hw
      refine ⟨x, ?_, ?_⟩
      · rw [List.length_nil, poincare_filtration_zero]
        exact hx
      · exact hxw
    | cons X l ih =>
      intro hl w hw
      obtain ⟨x, hx, hxe⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) w hw
      refine ⟨∑ a, ∑ b, X a b • E a b x, ?_, ?_⟩
      · exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
          Submodule.smul_mem _ _ (poincare_filtration_succ ε E u hE _ a b x hx)
      · change _ = dAct σ X (dWord σ l w)
        rw [← hxe, dAct, (hd X (hl X List.mem_cons_self) x).deriv]
  rw [stepSpace, Submodule.span_le]
  rintro v ⟨l, w, hl, hX, hw, rfl⟩
  obtain ⟨x, hx, hxe⟩ := key l hX w hw
  exact Submodule.mem_map.mpr ⟨x, pfil_monotone_in_length ε E u hl hx, hxe⟩

theorem smooth_of_mem_lowKSub {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hU : IsURepOn (UJset ε) σ)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) (v : H) (hv : v ∈ lowKSub ε lam σ) :
    SmoothOnGV ε (fun g => σ g v) := by
  obtain ⟨α, hα, hαc, hfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hU hS
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hcα : Continuous (fun g : UJ ε => α (umat g)) := by
    refine continuous_iff_continuousAt.mpr fun g₀ => ?_
    obtain ⟨U, F, hUo, hgU, hF, hFα⟩ := hα (umat g₀) g₀.2
    have hev : (fun g : UJ ε => F (umat g)) =ᶠ[nhds g₀] (fun g : UJ ε => α (umat g)) := by
      filter_upwards [hcu.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgU)] with g hg
      exact (hFα _ hg g.2).symm
    exact ((hF.continuousOn.continuousAt (hUo.mem_nhds hgU)).comp hcu.continuousAt).congr hev
  have hcσ : Continuous (fun g : UJ ε => σ (umat g) v) :=
    (hU.2.2 v).comp_continuous hcu fun g => g.2
  have hint : Integrable (fun g : UJ ε => α (umat g) • σ (umat g) v) (muG ε) :=
    (hcα.smul hcσ).integrable_of_hasCompactSupport (hαc.smul_right)
  have hv : v = ∫ g : UJ ε, α (umat g) • σ (umat g) v ∂(muG ε) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [← integral_inner hint y, ← hfix v hv y]
    simp only [inner_smul_right]
  have hsm := GlobalTheory.GardingSmooth.garding_smooth n ε H σ hU α hα hαc v
  rw [← hv] at hsm
  exact hsm

theorem stepBound_of_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (b : ℝ), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → (∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ)) → (∀ a, |lam a| ≤ b ^ 2) → (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) ∧ (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖w‖) := by
  intro n ε H _ _ _ σ lam b hU hS heig hb
  obtain ⟨Vs, E, hVs, hGl, hUn, hD, hEq⟩ := SmoothVecMod.smoothVec_unitary_module n ε H σ hU
  have hlow : lowKSub ε lam σ ≤ Vs := fun v hv =>
    (hVs v).mpr (smooth_of_mem_lowKSub ε lam σ hU hS v hv)
  obtain ⟨u, -, hKu, hmap, hfd⟩ := GlobalTheory.KTypeHighest.kType_generated_by_highest n ε H σ Vs E hU
    ⟨hVs, hGl, hUn, hD, hEq⟩ _ (lowKSub ε lam σ) hS hlow
  have huS : (u : H) ∈ lowKSub ε lam σ := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (mem_kSpan_self' ε E u)
  have hCas := GlobalTheory.CasimirEigen.cas_eq_of_isZEigen n ε H σ Vs E lam hU ⟨hVs, hGl, hUn, hD, hEq⟩ u
    (heig _ huS)
  have hKind : KindA ε E lam u := ⟨hKu, hCas, hfd⟩
  have hAlg := GlobalTheory.algebraic_step_bound Vs n ε E lam u b hGl hUn hKind hb
  have hC : ∀ P : ℕ, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P := fun P => stepConst_nonneg n b P
  have hmem : ∀ (P : ℕ) (w : H), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P →
      ∃ x : Vs, x ∈ pfil ε E u P ∧ (x : H) = w := fun P w hw =>
    Submodule.mem_map.mp (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P hw)
  have hact : ∀ X, inG ε X → ∀ x : Vs,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H) = ((∑ a, ∑ c, X a c • E a c x : Vs) : H) := fun X hX x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, (hD X hX x).deriv]
  have hbound : ∀ P : ℕ, ∀ x ∈ pfil ε E u P,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hAlg
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ (pfil ε E u P) := pfil_finite_dimensional ε E u hfd P
    exact Submodule.finiteDimensional_of_le
      (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P)
  · intro w hw
    obtain ⟨x, -, rfl⟩ := hmem P w hw
    exact fun X hX => (hD X hX x).differentiableAt
  · intro F hF w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hON := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).1 F hF
    calc ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) (x : H)‖ ^ 2
        = ∑ i, ‖∑ a, ∑ c, F i a c • E a c x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hact (F i) (hF.1 i) x]
          rfl
      _ = ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hON
      _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hbound P x hx
      _ = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := rfl
  · intro X hX w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hsq := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).2 X
    have hhs : 0 ≤ Formalism.REAL.hs X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hnorm : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ = ‖∑ a, ∑ c, X a c • E a c x‖ := by
      rw [hact X hX x]
      rfl
    have h2 : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ ^ 2 ≤
        (Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖) ^ 2 := by
      rw [hnorm, mul_pow, mul_pow, Real.sq_sqrt hhs]
      calc ‖∑ a, ∑ c, X a c • E a c x‖ ^ 2 ≤ Formalism.REAL.hs X * ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hsq
        _ ≤ Formalism.REAL.hs X * (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound P x hx) hhs
        _ = Formalism.REAL.hs X * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := by
          rw [mul_assoc]
          rfl
    have hr : 0 ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hC P)) (norm_nonneg _)
    nlinarith [norm_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H))]

end GlobalTheory.StepBoundOneRep
