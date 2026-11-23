import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecStr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.IsHilbertSchmidtOfAeEqDual

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem fd_pts {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (a : ℕ) (x : Fin a → Fin a → X), ∀ f ∈ E, (∀ i p, f (x i p) = 0) → ∀ u, f u = 0 := by
  obtain ⟨a, b, φ, ψ, x, y, s, t, -, -, h⟩ := tens E (⊤ : Submodule ℂ (Unit → ℂ))
  refine ⟨a, x, fun f hf h0 u => ?_⟩
  have := h (fun u _ => f u) (fun _ => hf) (fun _ => Submodule.mem_top) u ()
  simpa [h0] using this

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem rep_zero (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) :
    ∃ v ∈ τ, Reps μ v fun _ => 0 := by
  refine ⟨0, τ.zero_mem, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp
    (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
  exact hy

private theorem rep_add (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) {φ ψ : G1 K n → ℂ}
    (h₁ : ∃ v ∈ τ, Reps μ v φ) (h₂ : ∃ v ∈ τ, Reps μ v ψ) : ∃ v ∈ τ, Reps μ v fun y => φ y + ψ y := by
  obtain ⟨v, hv, h₁⟩ := h₁
  obtain ⟨w, hw, h₂⟩ := h₂
  refine ⟨v + w, τ.add_mem hv hw, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp (Lp.coeFn_add v w), h₁, h₂] with y hy a b
  rw [← a, ← b]
  exact hy

private theorem rep_smul (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (c : ℂ) {φ : G1 K n → ℂ}
    (h₁ : ∃ v ∈ τ, Reps μ v φ) : ∃ v ∈ τ, Reps μ v fun y => c * φ y := by
  obtain ⟨v, hv, h₁⟩ := h₁
  refine ⟨c • v, τ.smul_mem c hv, ?_⟩
  filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae_eq_comp (Lp.coeFn_smul c v), h₁] with y hy a
  rw [← a]
  exact hy

private theorem fix_int (D : TypeDat K n) {f : G1 K n → ℂ} (hf : Continuous f) (g : G1 K n) :
    Integrable (fun k => D.e k * f (g * k)) D.ν := by
  haveI := D.prob
  haveI : IsFiniteMeasure D.ν := MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure D.ν
  haveI : IsFiniteMeasureOnCompacts D.ν := ⟨fun _ _ => measure_lt_top _ _⟩
  have hc : Continuous fun k => D.e k * f (g * k) := D.cont.mul (hf.comp (continuous_const.mul continuous_id))
  have hU := (typeFin D).1
  have h1 : IntegrableOn (fun k => D.e k * f (g * k)) (D.U : Set (G1 K n)) D.ν :=
    hc.continuousOn.integrableOn_compact hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at h1

private theorem cosets (D : TypeDat K n) :
    ∃ s : Finset (G1 K n), (∀ k ∈ s, k ∈ KG K n) ∧ ∀ k ∈ KG K n, ∃ j ∈ s, ∃ u ∈ D.U, k = j * u := by
  obtain ⟨O, hO, hU⟩ := D.isOpen
  have hK : IsCompact (KG K n : Set (G1 K n)) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 n).1
  have h1 : ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O := ((hU 1).1 D.U.one_mem).1
  obtain ⟨s, hs, hcov⟩ := hK.elim_nhds_subcover
    (fun j => {g : G1 K n | ((j⁻¹ * g : G1 K n) : AdelicGLn.AdelicGL K n) ∈ O}) (fun j _ => by
      refine IsOpen.mem_nhds (hO.preimage (continuous_subtype_val.comp (continuous_const.mul continuous_id))) ?_
      simpa using h1)
  refine ⟨s, hs, fun k hk => ?_⟩
  obtain ⟨j, hj, hkj⟩ := Set.mem_iUnion₂.1 (hcov hk)
  refine ⟨j, hj, j⁻¹ * k, (hU _).2 ⟨hkj, ?_⟩, by group⟩
  exact (KG K n).mul_mem ((KG K n).inv_mem (hs j hj)) hk

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secFD :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (D : TypeDat K (2 + 2)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ →
      ∃ S : Submodule ℂ (G1 K (2 + 2) → ℂ), FiniteDimensional ℂ S ∧ ∀ f, f ∈ S ↔ IsSec τ₁ τ₂ f ∧ D.Fix f := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ D h₁ h₂
  let S : Submodule ℂ (G1 K (2 + 2) → ℂ) :=
    { carrier := {f | D.Fix f ∧ Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ X g, f (nn X * g) = f g) ∧
        (∀ t g, f (lv 1 1 t * g) = f g) ∧ Slices τ₁ τ₂ f}
      zero_mem' := ⟨fun g => by simp, continuous_const, ⟨0, fun g => by simp⟩, fun _ _ => rfl, fun _ _ => rfl,
        fun g => ⟨fun _ => rep_zero μ₂ τ₁, fun _ => rep_zero μ₂ τ₂⟩⟩
      add_mem' := by
        rintro f f' ⟨a1, a2, ⟨C, a3⟩, a4, a5, a6⟩ ⟨b1, b2, ⟨C', b3⟩, b4, b5, b6⟩
        refine ⟨fun g => ?_, a2.add b2, ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (a3 g) (b3 g))⟩,
          fun X g => by simp only [Pi.add_apply, a4, b4], fun t g => by simp only [Pi.add_apply, a5, b5],
          fun g => ⟨fun m => rep_add μ₂ τ₁ ((a6 g).1 m) ((b6 g).1 m), fun m => rep_add μ₂ τ₂ ((a6 g).2 m) ((b6 g).2 m)⟩⟩
        simp only [Pi.add_apply, mul_add]
        rw [integral_add (fix_int D a2 g) (fix_int D b2 g), a1 g, b1 g]
      smul_mem' := by
        rintro c f ⟨a1, a2, ⟨C, a3⟩, a4, a5, a6⟩
        refine ⟨fun g => ?_, a2.const_smul c, ⟨‖c‖ * C, fun g => ?_⟩,
          fun X g => by simp only [Pi.smul_apply, a4], fun t g => by simp only [Pi.smul_apply, a5],
          fun g => ⟨fun m => rep_smul μ₂ τ₁ c ((a6 g).1 m), fun m => rep_smul μ₂ τ₂ c ((a6 g).2 m)⟩⟩
        · simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
          rw [integral_const_mul, a1 g]
        · rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (a3 g) (norm_nonneg c) }
  refine ⟨S, ?_, fun f => ⟨fun hf => ⟨(secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hf.1).2 hf.2, hf.1⟩,
    fun hf => ⟨hf.2, (secCrit μ₂ τ₁ τ₂ D h₁ h₂ f hf.2).1 hf.1⟩⟩⟩
  obtain ⟨E₁, E₂, hE₁, hE₂, -, -, hE⟩ := secStr μ₂ τ₁ τ₂ D h₁ h₂
  obtain ⟨-, -, A, hA, -, hAf⟩ := typeFin D
  obtain ⟨a, x, hx⟩ := fd_pts E₁
  obtain ⟨b, y, hy⟩ := fd_pts E₂
  obtain ⟨c, z, hz⟩ := fd_pts A
  obtain ⟨s, -, hs⟩ := cosets D
  let pts : (Fin a × Fin a) × (Fin b × Fin b) × s × (Fin c × Fin c) → G1 K (2 + 2) := fun p =>
    lv (x p.1.1 p.1.2) (y p.2.1.1 p.2.1.2) 0 * (p.2.2.1 : G1 K (2 + 2)) * (z p.2.2.2.1 p.2.2.2.2 : G1 K (2 + 2))
  refine FiniteDimensional.of_injective ((LinearMap.funLeft ℂ ℂ pts).comp S.subtype) ?_
  rw [injective_iff_map_eq_zero]
  rintro ⟨f, a1, a2, a3, a4, a5, a6⟩ hf
  have h0 : ∀ p, f (pts p) = 0 := fun p => congrFun hf p
  have h1 : ∀ i p j q, ∀ k ∈ KG K (2 + 2), f (lv (x i p) (y j q) 0 * k) = 0 := by
    intro i p j q k hk
    obtain ⟨w, hw, u, hu, rfl⟩ := hs k hk
    rw [← mul_assoc]
    exact hz _ (hAf f a2 a1 (lv (x i p) (y j q) 0 * w)) (fun r r' => h0 ((i, p), (j, q), ⟨w, hw⟩, (r, r'))) ⟨u, hu⟩
  have h2 : ∀ m₁ m₂, ∀ k ∈ KG K (2 + 2), f (lv m₁ m₂ 0 * k) = 0 := by
    intro m₁ m₂ k hk
    have hk' := hE f a2 a1 a6 k hk
    exact hy _ (hk'.2 m₁) (fun j q => hx _ (hk'.1 (y j q)) (fun i p => h1 i p j q k hk) m₁) m₂
  apply Subtype.ext
  funext g
  obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  have hl : lv m₁ m₂ t = lv 1 1 t * lv m₁ m₂ 0 := by
    rw [(blkLaws (K := K)).2.1]; simp
  change f _ = 0
  rw [mul_assoc, a4, hl, mul_assoc, a5, h2 m₁ m₂ k hk]
