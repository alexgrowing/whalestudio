import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeightStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquivStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SdTuples

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

def cf (y : R ⊗[F] E) (k : Fin d) : R := (Algebra.TensorProduct.basis R b).repr y k

variable {R b}

def tupE (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ ((Fin M × Fin d) × Fin n → R) where
  toFun X p := cf R b (X p.2 p.1.1) p.1.2
  invFun Y a i := hc.homeomorph.symm (fun k => Y ((i, k), a))
  left_inv X := by
    funext a i
    exact hc.homeomorph.symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨⟨i, k⟩, a⟩ := p
    exact congrFun (hc.homeomorph.apply_symm_apply (fun k => Y ((i, k), a))) k
  map_add' X Y := by
    funext p
    simp [cf]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.1.2).comp (hc.continuous.comp
      ((continuous_apply p.1.1).comp (continuous_apply p.2)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact hc.homeomorph.symm.continuous.comp
      (continuous_pi fun k => continuous_apply ((i, k), a))

end Coord

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E}

omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] in

theorem coordK_preimage (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (lam : Measure R)
    (T : Set (Fin d → R)) :
    coordK R b lam (cf R b ⁻¹' T) = Measure.pi (fun _ => lam) T := by
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have he : MeasurableEmbedding (cf (F := F) (E := E) R b) := hc.homeomorph.measurableEmbedding
  have := he.comap_apply (Measure.pi fun _ : Fin d => lam) (cf R b ⁻¹' T)
  rw [Set.image_preimage_eq _ hc.surjective] at this
  exact this

theorem map_coordW (hCM : IsCMExt F E σ) (hc : IsHomeomorph (cf (F := F) (E := E) R b))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (n M : ℕ) :
    (coordW R b lam n M).map (tupE hc n M) = Measure.pi fun _ : (Fin M × Fin d) × Fin n => lam := by
  obtain ⟨h1, h2, h3, h4, -, -, -, hB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hB n M
  haveI := (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam).1
  have hm : Measurable (tupE hc n M) := (map_continuous (tupE hc n M)).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (tupE hc n M) ⁻¹' Set.univ.pi s = Set.univ.pi fun a : Fin n => Set.univ.pi fun i : Fin M =>
      cf R b ⁻¹' (Set.univ.pi fun k : Fin d => s ((i, k), a)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
    exact ⟨fun h a i k => h i k a, fun h i k a => h a i k⟩
  rw [hpre]
  unfold coordW
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi, coordK_preimage hc, Measure.pi_pi]
  rw [Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]

omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] in

theorem BR_eq (hc : IsHomeomorph (cf (F := F) (E := E) R b)) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X Y = tupE hc n M X ⬝ᵥ
      ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ tupE hc n M Y) := by
  rw [Matrix.blockDiagonal_map _ _ (map_zero _)]
  unfold BR
  simp_rw [hB]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type_right (f := fun p : (Fin M × Fin d) × Fin n => _)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  have hs : ∑ c : Fin n, ∑ q : Fin M × Fin d,
      Matrix.blockDiagonal (fun _ : Fin n => B.map (algebraMap F R)) (p, a) (q, c) *
        tupE hc n M Y (q, c) =
      ∑ q : Fin M × Fin d, B.map (algebraMap F R) p q *
        (Algebra.TensorProduct.basis R b).repr (Y a q.1) q.2 := by
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_eq]
      rfl
    · intro c _ hca
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hca), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hs]
  rfl

theorem sdW_iff (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (ψR : R → ℂ) (n : ℕ) (cc : ℝ≥0)
    (hmain : ∀ μ : Measure ((Fin M × Fin d) × Fin n → R),
      SelfDual μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y))) ↔
        μ = cc • Measure.pi fun _ => lam)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) :
    SdW F E σ M J R ψR n μ ↔ μ = cc • coordW R b lam n M := by
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (cf (F := F) (E := E) R b) := hcc d b
  set e := tupE hc n M with he
  have hm : Measurable e := (map_continuous e).measurable
  have hm' : Measurable e.symm := (map_continuous e.symm).measurable
  have inj : ∀ ν : Measure (Fin n → Fin M → R ⊗[F] E), (ν.map e).map e.symm = ν := by
    intro ν
    rw [Measure.map_map hm' hm]
    have : (e.symm ∘ e) = id := by funext X; exact e.symm_apply_apply X
    rw [this, Measure.map_id]
  have key := GlobalTheory.T.selfdual_measure_transport_equiv _ _ e μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y)))
  have hform : SdW F E σ M J R ψR n μ ↔ SelfDual μ (fun X Y => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
    unfold SdW
    have : (fun X Y => ψR (BR R σ J X Y)) = (fun X Y : Fin n → Fin M → R ⊗[F] E => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
      funext X Y
      rw [BR_eq hc J B hB X Y]
    rw [this]
  rw [hform, key, hmain]
  constructor
  · intro h
    rw [← inj μ, h, ← map_coordW hCM hc lam hlam n M, ← Measure.map_smul, inj]
  · intro h
    rw [h, Measure.map_smul, map_coordW hCM hc lam hlam n M]

end Meas

theorem sdW_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ ↔ μ = cinf • coordW (Ainf F) b laminf n M) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ ↔ μ = c v • coordW (Fv F v) b (lam v) n M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b laminf lam hinf hv ψ hψ n
  obtain ⟨B, hsym, hdet, -, hR'⟩ := GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ d b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.T.exists_unipotentInvariant_compactlySupported_weight F hCM.1 laminf lam hinf hv ψ hψ
    ((Fin M × Fin d) × Fin n) (Matrix.blockDiagonal fun _ : Fin n => B) hsym' hdet'
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Ainf F)).1 laminf hinf.1 (psiInf F ψ) n cinf h1 μ
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Fv F v)).1 (lam v) (hv v).1 (psiV F ψ v) n (c v) (h2 v) μ

end GlobalTheory.CompanionTheory.SW.SdTuples
