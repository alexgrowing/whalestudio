import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresSupportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

theorem pi_map_scale {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (f : X → X) (hf : Measurable f) (c : ℝ≥0) (h : μ.map f = c • μ) :
    (Measure.pi fun _ : ι => μ).map (fun x i => f (x i)) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  haveI : SigmaFinite (μ.map f) := by rw [h]; infer_instance
  rw [Measure.pi_map_pi (f := fun _ => f) (fun _ => hf.aemeasurable)]
  simp only [h]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]
  push_cast
  rfl

theorem map_comap_scale {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (φ : X → Y)
    (P : Measure Y) (f : X → X) (hf : Measurable f) (D : Y ≃ᵐ Y) (C : ℝ≥0)
    (hs : Function.Surjective φ) (hi : Function.Injective φ)
    (him : ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P)
    (hc : ∀ x, φ (f x) = D (φ x)) (hD : P.map D = C • P) :
    (Measure.comap φ P).map f = C • Measure.comap φ P := by
  ext B hB
  rw [Measure.map_apply hf hB, Measure.comap_apply₀ φ P hi him (hf hB).nullMeasurableSet,
    Measure.smul_apply, Measure.comap_apply₀ φ P hi him hB.nullMeasurableSet]
  have e : φ '' (f ⁻¹' B) = D ⁻¹' (φ '' B) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f x, hx, hc x⟩
    · rintro ⟨z, hz, hzy⟩
      obtain ⟨x, rfl⟩ := hs y
      refine ⟨x, ?_, rfl⟩
      have : f x = z := hi (by rw [hc, hzy])
      simpa [this] using hz
  rw [e, ← MeasurableEquiv.map_apply, hD, Measure.smul_apply]

variable {F : Type} [Field F] [NumberField F]

theorem norm_natCast (v : HeightOneSpectrum (𝓞 F)) (a e : ℕ) (ha : 0 < a)
    (h1 : (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e)
    (h2 : ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1)) :
    ‖(a : Fv F v)‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ e := by
  rw [Ideal.span_singleton_le_iff_mem] at h1 h2
  rw [← v.intValuation_le_pow_iff_mem] at h1 h2
  have hv : Valued.v (a : Fv F v) = v.intValuation (a : 𝓞 F) := by
    have := GlobalTheory.LocalDifferentProduct.valued_coe_algebraMap v (a : 𝓞 F)
    simpa using this
  have h0 : v.intValuation (a : 𝓞 F) ≠ 0 :=
     v.intValuation_ne_zero _ (by exact_mod_cast ha.ne')
  have hval : v.intValuation (a : 𝓞 F) = WithZero.exp (-(e : ℤ)) := by
    rw [← WithZero.exp_log h0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h2
    omega
  rw [FinitePlace.norm_def, hv, hval, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  push_cast
  change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e : ℤ)) = _
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem scale_fv (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) [lam.IsAddHaarMeasure]
    (x : Fv F v) (hx : x ≠ 0) (k : ℕ) (hk : ‖x‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ k) :
    lam.map (fun y => x * y) = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k) • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ k := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    rw [this, hk]
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k) := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil

section K
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPi (ι : Type) (t : R) (ht : t ≠ 0) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ => (Homeomorph.mulLeft₀ t ht).toMeasurableEquiv

theorem mulPi_apply (ι : Type) (t : R) (ht : t ≠ 0) (x : ι → R) (i : ι) :
    mulPi R ι t ht x i = t * x i := rfl

theorem map_mulPi {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPi R ι t ht) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) :
    (coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) t * y) = (c ^ d) • coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPi (ι := Fin d) R lam t ht c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPi R (Fin d) t ht) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPi_apply, ← Algebra.smul_def, map_smul]
    rfl

end K
end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil
theorem cT_scalar {A : Type} [CommRing A] (s : A →+* A) (c : A) (hs : s c = c)
    (S : Matrix (Fin 1) (Fin 1) A) (i j : Fin 1) :
    (cT s (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) A) * S * (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) A)) i j = c ^ 2 * S i j := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply, hs]
  ring
end GlobalTheory.CompanionTheory.SW.Dil

namespace GlobalTheory.CompanionTheory.SW.Dil

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

theorem half_trace_tmul (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    norm_num
  rw [e, Algebra.trace_algebraMap, Module.finrank_baseChange, hσ.2.2.1, two_nsmul, ← two_mul,
    ← mul_assoc, h2, one_mul]

theorem coordHerm_map (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] (t : R) (ht : t ≠ 0) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) (τ : HermR R σ 1 → HermR R σ 1) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j) :
    (coordHerm R σ b lam 1).map τ = c • coordHerm R σ b lam 1 := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›
  haveI := hK
  haveI := hH 1
  set φ : HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
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
  have hD : P.map ((mulPi R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPi R (Fin 1) t ht).measurable
      (measurable_id)
    rw [map_mulPi R lam t ht c h, Measure.map_id] at e
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

theorem dilation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → 1 ≤ M → ∀ (a : ℕ) (e : ℕ), 0 < a → (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ e → ¬ (Ideal.span {(a : 𝓞 F)}) ≤ v.asIdeal ^ (e + 1) → ∀ (s : Fv F v) (A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet A → m (hermScal (Fv F v) σ s) {X | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞) ^ (e * (2 * M - 2)) * m (hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s)) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b v lam hlam m hm hM a e ha h1 h2 s A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := scale_fv v lam _ ht e hnorm
  have hs2 := scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have key := GlobalTheory.T.gram_fiber_measures_rmul_equivariant F E σ hσ M J hJ (Fv F v) hloc 1 (coordW (Fv F v) b lam 1 M)
    (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermScal (Fv F v) σ s)
  have hτs : τ (hermScal (Fv F v) σ s) = hermScal (Fv F v) σ ((a : Fv F v) ^ 2 * s) := by
    apply Subtype.ext
    funext i j
    rw [hτe]
    change _ * (s ⊗ₜ[F] (1 : E)) = ((a : Fv F v) ^ 2 * s) ⊗ₜ[F] (1 : E)
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  rw [hset, ← key3, hqdef]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.Dil
