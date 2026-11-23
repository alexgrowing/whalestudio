import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.HermOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem sig_sig (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  apply τ.injective
  rw [h τ, h τ, star_star]

theorem exists_sig_ne (hcm : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  obtain ⟨-, htc, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  have hc : (InfinitePlace.mk τ).IsComplex := htc.isComplex _
  rw [InfinitePlace.isComplex_mk_iff] at hc
  by_contra hall
  push_neg at hall
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h τ x
  rw [hall x] at this
  simpa using this.symm

theorem trace_sig (hcm : IsCMExt F E σ) (y : E) :
    Algebra.trace F E (σ y) = Algebra.trace F E y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig hcm)) (AlgHom.ext (sig_sig hcm))
  have h : (e.toLinearEquiv).conj (Algebra.lmul F E y) = Algebra.lmul F E (σ y) := by
    ext z
    have h1 : e.toLinearEquiv.symm z = σ z := rfl
    have h2 : ∀ w, e.toLinearEquiv w = σ w := fun _ => rfl
    have h3 : ∀ w, e w = σ w := fun _ => rfl
    have h4 : ∀ w, e.symm w = σ w := fun _ => rfl
    simp [LinearEquiv.conj_apply, h1, h2, h3, h4, sig_sig hcm]
  rw [Algebra.trace_apply, Algebra.trace_apply]
  show LinearMap.trace F E (Algebra.lmul F E (σ y)) = LinearMap.trace F E (Algebra.lmul F E y)
  rw [← h, LinearMap.trace_conj']

theorem add_sig_eq_trace (hcm : IsCMExt F E σ) (y : E) :
    y + σ y = algebraMap F E (Algebra.trace F E y) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨x, hx⟩ := exists_sig_ne hcm
  set θ : E := x - σ x with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσθ : σ θ = -θ := by simp [hθ, sig_sig hcm]
  have htr : Algebra.trace F E θ = 0 := by
    have h := trace_sig hcm θ
    rw [hσθ, map_neg] at h
    have h2 : (2 : F) * Algebra.trace F E θ = 0 := by linear_combination -h
    simpa using h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (w : E), σ (c • w) = c • σ w := fun c w => by simp [Algebra.smul_def]
    have h2 := congrArg σ hst
    rw [map_add, hσs, hσs, map_one, hσθ, map_zero] at h2
    have h3 : (2 * t) • θ = 0 := by
      have : (2 * t) • θ = (s • (1 : E) + t • θ) - (s • (1 : E) + t • -θ) := by
        simp only [smul_neg, mul_smul, two_smul]
        abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by simpa [hθ0] using h3
    refine ⟨?_, ht⟩
    simpa [ht] using hst
  let bb : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hbb : ∀ i, bb i = ![(1 : E), θ] i := fun i => by
    simp [bb]
  have hmaps : (LinearMap.id + σ.toLinearMap : E →ₗ[F] E) =
      (Algebra.linearMap F E) ∘ₗ Algebra.trace F E := by
    refine bb.ext fun i => ?_
    fin_cases i
    · have h1 : Algebra.trace F E (1 : E) = 2 := by
        have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
        simpa [hfr] using this
      simp [hbb, h1]
      rw [map_ofNat]
      norm_num
    · simp [hbb, htr, hσθ]
  simpa using LinearMap.congr_fun hmaps y

end Field

section Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : r ⊗ₜ[F] e = r • ((1 : R) ⊗ₜ[F] e) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = (Algebra.lmul F E e).baseChange R := by
    ext z
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, Algebra.trace_apply]
  show r * LinearMap.trace R _ (Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)) = _
  rw [h2, LinearMap.trace_baseChange]

theorem add_sigR_eq_trace (hcm : IsCMExt F E σ) (z : R ⊗[F] E) :
    z + sigR R σ z = (Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have h1 : sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by simp [sigR]
    rw [h1, ← TensorProduct.tmul_add, add_sig_eq_trace hcm, trace_tmul,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_comm]
  | add a c ha hc =>
    rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hc]
    abel

end Ring

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

def tH (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem tH_hermScal (hcm : IsCMExt F E σ) (r : R) : tH R σ (hermScal R σ r) = r := by
  have h1 : Algebra.trace F E (1 : E) = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
    simpa [hcm.2.2.1] using this
  have h2 : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
    rw [← map_mul]
    norm_num
  show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r
  rw [trace_tmul, h1]
  linear_combination r * h2

theorem hermScal_tH (hcm : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (tH R σ S) = S := by
  apply Subtype.ext
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  set z : R ⊗[F] E := (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 with hz
  have hfix : sigR R σ z = z := S.2 0 0
  have hs := add_sigR_eq_trace R hcm z
  rw [hfix] at hs
  show (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) = z
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', ← hs, ← two_smul F z, smul_smul]
  norm_num

variable [TopologicalSpace R] [IsTopologicalRing R]

def hermHomeo (hcm : IsCMExt F E σ) : HermR R σ 1 ≃ₜ R :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toFun := tH R σ
    invFun := hermScal R σ
    left_inv := hermScal_tH R hcm
    right_inv := tH_hermScal R hcm
    continuous_toFun := continuous_const.mul
      ((IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.trace R (R ⊗[F] E))).comp
        ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)))
    continuous_invFun := Continuous.subtype_mk (continuous_pi fun _ => continuous_pi fun _ =>
      IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.linearMap R (R ⊗[F] E))) _ }

variable [MeasurableSpace R] [BorelSpace R]

theorem map_coordHerm (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    [SigmaFinite lam] : (coordHerm R σ b lam 1).map (hermHomeo R hcm) = lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI hT : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h := p.2
      rw [Subsingleton.elim p.1.1 p.1.2] at h
      exact lt_irrefl _ h⟩
  let ψ : R → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun r => (fun _ => r, fun p => hT.elim p)
  have hψ : MeasurableEmbedding ψ := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun q => q.1 0) ?_ ?_ ?_ ?_
    · refine Measurable.prodMk (measurable_pi_lambda _ fun _ => measurable_id) ?_
      exact measurable_pi_lambda _ fun p => hT.elim p
    · have : Set.range ψ = Set.univ := by
        ext q
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        refine ⟨q.1 0, Prod.ext ?_ (Subsingleton.elim _ _)⟩
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro r
      rfl
  ext s hs
  have hfun : (fun S : HermR R σ 1 =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} =>
          (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))) = ψ ∘ hermHomeo R hcm := by
    funext S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hemb : MeasurableEmbedding (ψ ∘ hermHomeo R hcm) :=
    hψ.comp (hermHomeo R hcm).measurableEmbedding
  have hpi : Measure.pi (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam) =
      Measure.dirac (fun p => hT.elim p) := Measure.pi_of_empty _ _
  have himg : (ψ ∘ hermHomeo R hcm) '' (hermHomeo R hcm ⁻¹' s) =
      ((fun a : Fin 1 → R => a 0) ⁻¹' s) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨hS, Set.mem_univ _⟩
    · rintro ⟨hq, -⟩
      refine ⟨(hermHomeo R hcm).symm (q.1 0), ?_, ?_⟩
      · simpa using hq
      · refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [ψ]
  rw [Measure.map_apply (hermHomeo R hcm).measurable hs, coordHerm, hfun, hemb.comap_apply, hpi, himg,
    Measure.prod_prod, measure_univ, mul_one]
  exact (measurePreserving_funUnique lam (Fin 1)).measure_preimage hs.nullMeasurableSet

end Main

end GlobalTheory.CompanionTheory.SW.BB.HermOne
