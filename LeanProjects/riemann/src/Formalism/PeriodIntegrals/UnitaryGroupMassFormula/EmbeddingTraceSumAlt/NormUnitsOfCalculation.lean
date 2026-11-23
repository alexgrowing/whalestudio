import Mathlib
import Formalism.PeriodIntegrals.ScPsiExists

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScPsiExists.UnitaryGroupMassFormula

theorem sum_embedding_eq_trace (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : F) :
    ∑ v : InfinitePlace F, v.embedding y = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by
  rw [trace_eq_sum_embeddings (E := ℂ)]
  refine Fintype.sum_bijective (fun v : InfinitePlace F => v.embedding.toRatAlgHom) ⟨?_, ?_⟩ _ _ ?_
  · intro v w h
    have h' : v.embedding = w.embedding := by
      have := congrArg AlgHom.toRingHom h
      simpa [RingHom.toRatAlgHom_toRingHom] using this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, h']
  · intro σ
    refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
    have hr : ComplexEmbedding.IsReal (σ : F →+* ℂ) :=
      InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
    apply AlgHom.ext
    intro x
    show (InfinitePlace.mk (σ : F →+* ℂ)).embedding x = σ x
    rw [InfinitePlace.embedding_mk_eq_of_isReal hr]
    rfl
  · intro v
    simp

theorem sum_embedding_int (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : 𝓞 F) :
    ∃ n : ℤ, ∑ v : InfinitePlace F, v.embedding (algebraMap (𝓞 F) F c) = (n : ℂ) := by
  have hi : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F c)) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe c)
  obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hi
  refine ⟨n, ?_⟩
  rw [sum_embedding_eq_trace, ← hn]
  simp

section Tau

variable {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]

theorem add_star_mem (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    ∃ a : F, algebraMap F E a = x + star x :=
  RingHom.mem_range.1 ((hfix (x + star x)).1 (by rw [star_add, star_star, add_comm]))

def tauFun (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) : F :=
  (add_star_mem hfix x).choose

theorem tauFun_spec (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    algebraMap F E (tauFun hfix x) = x + star x :=
  (add_star_mem hfix x).choose_spec

def tau (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) : E →ₗ[F] F where
  toFun := tauFun hfix
  map_add' x y := (algebraMap F E).injective (by
    rw [map_add, tauFun_spec, tauFun_spec, tauFun_spec, star_add]; ring)
  map_smul' a x := (algebraMap F E).injective (by
    rw [RingHom.id_apply, smul_eq_mul, map_mul, tauFun_spec, tauFun_spec, Algebra.smul_def,
      star_mul, (hfix (algebraMap F E a)).2 ⟨a, rfl⟩]
    ring)

theorem tau_apply (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (x : E) :
    algebraMap F E (tau hfix x) = x + star x :=
  tauFun_spec hfix x

theorem tau_int [NumberField F] [NumberField E]
    (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (c : 𝓞 E) :
    ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = tau hfix (algebraMap (𝓞 E) E c) := by
  have h1 : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
  have h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E c)) := by
    have := h1.map (starRingEnd E).toIntAlgHom
    exact this
  have h3 : IsIntegral ℤ (algebraMap F E (tau hfix (algebraMap (𝓞 E) E c))) := by
    rw [tau_apply]
    exact h1.add h2
  have h4 := (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h3
  exact ⟨⟨_, h4⟩, rfl⟩

end Tau

theorem alg_int_mem (F : Type) [Field F] [NumberField F] (d : 𝓞 F) :
    algebraMap F (Af F) (algebraMap (𝓞 F) F d) ∈ Formalism.UG.intAd F := by
  intro v
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F d)) v ∈ v.adicCompletionIntegers F
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact HeightOneSpectrum.valuation_le_one v d

theorem int_of_alg_mem (F : Type) [Field F] [NumberField F] (y : F)
    (h : algebraMap F (Af F) y ∈ Formalism.UG.intAd F) : ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = y := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := by
    intro v
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact RingHom.mem_range.1 (HeightOneSpectrum.mem_integers_of_valuation_le_one F y hv)

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tT (τ : E →ₗ[F] F) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map τ LinearMap.id

theorem tT_tmul (τ : E →ₗ[F] F) (x : E) (b : Af F) :
    tT τ (x ⊗ₜ b) = algebraMap F (Af F) (τ x) * b := by
  simp [tT, Algebra.smul_def]

theorem tT_mem (τ : E →ₗ[F] F)
    (hτ : ∀ c : 𝓞 E, ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ (algebraMap (𝓞 E) E c))
    (z : E ⊗[F] Af F) (hz : z ∈ IntAf F E) : tT τ z ∈ Formalism.UG.intAd F := by
  let f : 𝓞 E →ₐ[ℤ] E ⊗[F] Af F :=
    ((Formalism.UG.inclE (F := F) (Af F)).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  let g : Formalism.UG.intAd F →ₐ[ℤ] E ⊗[F] Af F :=
    (((Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) : Af F →+* E ⊗[F] Af F).comp
      (Formalism.UG.intAd F).subtype).toIntAlgHom
  have hP : ∀ w, tT τ (Algebra.TensorProduct.productMap f g w) ∈ Formalism.UG.intAd F := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      have hfg : f c * g b = (algebraMap (𝓞 E) E c) ⊗ₜ[F] (b : Af F) := by
        show ((algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] (b : Af F)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfg, tT_tmul]
      obtain ⟨d, hd⟩ := hτ c
      rw [← hd]
      exact mul_mem (alg_int_mem F d) b.2
    | add w w' hw hw' =>
      rw [map_add, map_add]
      exact add_mem hw hw'
  have hle : IntAf F E ≤ (Algebra.TensorProduct.productMap f g).range.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hx
      refine ⟨c ⊗ₜ 1, ?_⟩
      show (Algebra.TensorProduct.productMap f g) (c ⊗ₜ[ℤ] 1) = (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ((algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : Af F)) *
        ((1 : E) ⊗ₜ[F] ((1 : Formalism.UG.intAd F) : Af F)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp
    · refine ⟨1 ⊗ₜ ⟨y, hy⟩, ?_⟩
      show (Algebra.TensorProduct.productMap f g) (1 ⊗ₜ[ℤ] ⟨y, hy⟩) = (1 : E) ⊗ₜ[F] y
      rw [Algebra.TensorProduct.productMap_apply_tmul]
      show ((algebraMap (𝓞 E) E 1) ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] y) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, map_one, one_mul, one_mul]
  obtain ⟨w, rfl⟩ := (AlgHom.mem_range _).1 (Subalgebra.mem_toSubring.1 (hle hz))
  exact hP w

theorem int_of_inclE_mem (τ : E →ₗ[F] F)
    (hτ : ∀ c : 𝓞 E, ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ (algebraMap (𝓞 E) E c))
    (x : E) (hx : Formalism.UG.inclE (F := F) (Af F) x ∈ IntAf F E) :
    ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ x := by
  have h := tT_mem τ hτ _ hx
  have he : tT τ (Formalism.UG.inclE (F := F) (Af F) x) = algebraMap F (Af F) (τ x) := by
    simp [Formalism.UG.inclE, tT_tmul]
  rw [he] at h
  exact int_of_alg_mem F _ h

end Tens

def sHom (I : AutInst) : I.E →+ ℝ :=
  AddMonoidHom.mk' (fun x => ∑ v, 2 * (I.φ v x).re) (by
    intro x y
    simp only [map_add, Complex.add_re, mul_add, Finset.sum_add_distrib])

theorem add_star_eq (z : ℂ) : z + star z = ((2 * z.re : ℝ) : ℂ) := by
  rw [Complex.star_def]
  exact Complex.add_conj z

theorem sHom_coe (I : AutInst) (x : I.E) :
    ((sHom I x : ℝ) : ℂ) = ∑ v, (I.φ v x + star (I.φ v x)) := by
  simp only [add_star_eq]
  simp [sHom]

theorem psiEinf_eq (I : AutInst) (x : I.E) :
    psiEinf I x = Complex.exp (2 * Real.pi * Complex.I * ((sHom I x : ℝ) : ℂ)) := by
  rw [sHom_coe, Finset.mul_sum, Complex.exp_sum]
  rfl

theorem sHom_int (I : AutInst) (x : I.E)
    (hx : Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E) : ∃ n : ℤ, sHom I x = n := by
  have := I.cm.totReal
  obtain ⟨d, hd⟩ := int_of_inclE_mem (tau I.cm.fixed) (tau_int I.cm.fixed) x hx
  obtain ⟨n, hn⟩ := sum_embedding_int I.F d
  refine ⟨n, ?_⟩
  apply Complex.ofReal_injective
  have h2 : ∀ v, I.φ v x + star (I.φ v x) = v.embedding (algebraMap (𝓞 I.F) I.F d) := by
    intro v
    rw [hd, ← I.φ_over, tau_apply, map_add, I.cm.cmUnram.2.1 (I.φ v) x]
    rfl
  rw [sHom_coe, Finset.sum_congr rfl (fun v _ => h2 v), hn]
  simp

theorem norm_units_of_calculation : Target := by
  intro I
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let N : AddSubgroup (I.E ⊗[I.F] Af I.F) := (IntAf I.F I.E).toAddSubgroup
  let π : I.E ⊗[I.F] Af I.F →+ (I.E ⊗[I.F] Af I.F) ⧸ N := QuotientAddGroup.mk' N
  let j : I.E →+ (I.E ⊗[I.F] Af I.F) ⧸ N :=
    π.comp (Formalism.UG.inclE (F := I.F) (Af I.F)).toAddMonoidHom
  let sb : I.E →+ AddCircle (1 : ℝ) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (sHom I)
  have hker : j.ker ≤ sb.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hx' : Formalism.UG.inclE (F := I.F) (Af I.F) x ∈ IntAf I.F I.E :=
      (QuotientAddGroup.eq_zero_iff _).1 hx
    obtain ⟨n, hn⟩ := sHom_int I x hx'
    show ((sHom I x : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [hn, AddCircle.coe_eq_zero_iff]
    exact ⟨n, by simp⟩
  let g0 : I.E ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker sb hker
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g0
  have hj : ∀ x, h (j x) = sb x := by
    intro x
    have := DFunLike.congr_fun hh (x : I.E ⧸ j.ker)
    simpa [g0] using this
  refine ⟨fun z => ((AddCircle.toCircle (-(h (π z))) : Circle) : ℂ), ?_, ?_, ?_⟩
  · intro z w
    simp only [map_add, neg_add, AddCircle.toCircle_add, Circle.coe_mul]
  · intro z hz
    have hz0 : π z = 0 := (QuotientAddGroup.eq_zero_iff z).2 hz
    simp only [hz0, map_zero, neg_zero]
    rw [← AddCircle.coe_zero, AddCircle.toCircle_apply_mk]
    simp
  · intro x
    show ((AddCircle.toCircle (-(h (j x)))) : ℂ) * psiEinf I x = 1
    rw [hj, psiEinf_eq]
    show ((AddCircle.toCircle (-((sHom I x : ℝ) : AddCircle (1 : ℝ)))) : ℂ) * _ = 1
    rw [← AddCircle.coe_neg, AddCircle.toCircle_apply_mk, Circle.coe_exp, ← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring

end PI.ScPsiExists.UnitaryGroupMassFormula
