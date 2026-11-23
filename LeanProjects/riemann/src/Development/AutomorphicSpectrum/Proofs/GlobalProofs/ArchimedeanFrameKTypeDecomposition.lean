import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DilU

open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Dil

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulHomeo (t : R) (ht : IsUnit t) : R ≃ₜ R where
  toFun y := t * y
  invFun y := (ht.unit⁻¹ : Rˣ) * y
  left_inv y := by
    change ((ht.unit⁻¹ : Rˣ) : R) * (t * y) = y
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  right_inv y := by
    change t * (((ht.unit⁻¹ : Rˣ) : R) * y) = y
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def mulPiU (ι : Type) (t : R) (ht : IsUnit t) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ => (mulHomeo R t ht).toMeasurableEquiv

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (t : R) (ht : IsUnit t)
    (c : ℝ≥0) (h : lam.map (fun y => t * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι t ht) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
  [T2Space R] [MeasurableSpace R] [BorelSpace R] in
theorem half_trace_tmul (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← (map_ofNat (algebraMap F R) 2), ← map_mul]
    norm_num
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hc : Fintype.card (Fin (Module.finrank F E)) = 2 := by
    rw [Fintype.card_fin, hσ.2.2.1]
  rw [e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E)), hc,
    two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

theorem coordHerm_map_unit (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] (t : R) (ht : IsUnit t) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j) :
    (coordHerm R σ b lam 1).map τ = c • coordHerm R σ b lam 1 := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›
  haveI := hK
  haveI := hH 1
  set φ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hφ
  set Q : Measure ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := Measure.pi fun _ => coordK R b lam with hQ
  set P := (Measure.pi fun _ : Fin 1 => lam).prod Q with hP
  have hν : coordHerm R σ b lam 1 = Measure.comap φ P := rfl
  have hemp : ∀ p : {p : Fin 1 × Fin 1 // p.1 < p.2}, False := fun p =>
    absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : coordHerm R σ b lam 1 = 0 := by
      rw [hν, Measure.comap, dif_neg hc]
    have := isOpen_univ.measure_pos (coordHerm R σ b lam 1) Set.univ_nonempty
    simp [h0] at this
  have hs : Function.Surjective φ := by
    rintro ⟨y, w⟩
    refine ⟨hermScal R σ (y 0), Prod.ext ?_ ?_⟩
    · funext i
      rw [Subsingleton.elim i 0]
      exact half_trace_tmul R σ hσ (y 0)
    · funext p
      exact (hemp p).elim
  have hD : P.map ((mulPiU R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPiU R (Fin 1) t ht).measurable
      (measurable_id)
    rw [map_mulPiU R lam t ht c h, Measure.map_id] at e
    simp only [Fintype.card_fin, pow_one] at e
    rw [Measure.prod_smul_left] at e
    exact e.symm
  rw [hν]
  refine map_comap_scale φ P τ hτm _ c hs hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _ =
      t * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _)
    rw [hτ, ← Algebra.smul_def t, map_smul, smul_eq_mul]
    ring
  · funext p
    exact (hemp p).elim

end H

theorem coordHerm_map_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → ∀ τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1, Measurable τ → (∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1).map τ = c • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam t ht c h τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_unit (Ainf F) σ hσ b lam t ht c h τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DilU
