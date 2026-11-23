import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem pi_const_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (κ : Measure X) [SigmaFinite κ] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • κ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => κ) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem subst_row_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (u : Rˣ) (w : (Fin n → R ⊗[F] E) → HermR R σ n), Measurable w → ∀ f : (Fin n → R ⊗[F] E) × HermR R σ n → ℝ≥0∞, Measurable f → ∫⁻ c, ∫⁻ S', f (c, S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) = (cm u : ℝ≥0∞) ^ n * ∫⁻ r, ∫⁻ S'', f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D u w hw f hf
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ D.hCM R d b lam D.hlam
  haveI := hK
  haveI := hH n
  have hVU : ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) : R ⊗[F] E) *
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, inv_mul_cancel₀ D.ht, map_one, Units.inv_mul]
    rfl
  have hTm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply j).const_mul _
  have hDm : Measurable (fun (r : Fin n → R ⊗[F] E) (j : Fin n) =>
      (((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply j).const_mul _
  have hmap : (Measure.pi fun _ : Fin n => coordK R b lam).map
      (fun (r : Fin n → R ⊗[F] E) (j : Fin n) => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * r j) =
      ((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam := by
    have hm : ∀ _ : Fin n, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        cm u • coordK R b lam := fun _ => D.hmod u
    have hsf : ∀ _ : Fin n, SigmaFinite ((coordK R b lam).map
        (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)) := fun i => by
      rw [hm i]; infer_instance
    have h1 := Measure.pi_map_pi (X := fun _ : Fin n => R ⊗[F] E) (Y := fun _ : Fin n => R ⊗[F] E)
      (hμ := hsf) (μ := fun _ : Fin n => coordK R b lam)
      (f := fun _ y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y)
      (fun _ => (measurable_const_mul _).aemeasurable)
    rw [h1]
    simp only [D.hmod u]
    rw [pi_const_smul, Fintype.card_fin]
  have hh : Measurable (fun r : Fin n → R ⊗[F] E => ∫⁻ S'', f (fun j =>
      ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * r j), S'' - w r) ∂(coordHerm R σ b lam n)) := by
    refine Measurable.lintegral_prod_right' (f := fun p : (Fin n → R ⊗[F] E) × HermR R σ n =>
      f (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * p.1 j), p.2 - w p.1)) ?_
    exact hf.comp ((hDm.comp measurable_fst).prodMk (measurable_snd.sub (hw.comp measurable_fst)))
  have hsm : ∀ g : (Fin n → R ⊗[F] E) → ℝ≥0∞, ((cm u : ℝ≥0∞) ^ n) * ∫⁻ r, g r ∂(Measure.pi fun _ : Fin n => coordK R b lam) =
      ∫⁻ r, g r ∂(((cm u : ℝ≥0∞) ^ n) • Measure.pi fun _ : Fin n => coordK R b lam) := fun g => by
    rw [lintegral_smul_measure, smul_eq_mul]
  rw [hsm, ← hmap, lintegral_map hh hTm]
  refine lintegral_congr fun c => ?_
  have hc : (fun j => ((((u⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) *
      (((u : R) ⊗ₜ[F] (algebraMap F E t)) * c j))) = c := by
    funext j
    rw [← mul_assoc, hVU, one_mul]
  rw [hc]
  exact (lintegral_sub_right_eq_self (fun S' => f (c, S')) _).symm

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
