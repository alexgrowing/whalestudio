import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussMean.OneVec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Transport

variable {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]

theorem selfDual_map (e : X ≃ₜ+ Y) {ν : Measure X} {χ : X → X → ℂ} {χ' : Y → Y → ℂ}
    (hχ : ∀ s t, χ' (e s) (e t) = χ s t) (h : SelfDual ν χ) : SelfDual (ν.map e) χ' := by
  obtain ⟨hH, hF⟩ := h
  set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm
  have hmap : ν.map e = ν.map m := rfl
  refine ⟨?_, ?_⟩
  · exact ContinuousAddEquiv.isAddHaarMeasure_map ν e
  intro Φ hc hs hI z
  rw [hmap] at hI ⊢
  have hinner : ∀ t : X, ∫ x, Φ x * χ' x (e t) ∂(ν.map m) = ∫ s, Φ (e s) * χ s t ∂ν := by
    intro t
    rw [integral_map_equiv]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    show Φ (e s) * χ' (e s) (e t) = Φ (e s) * χ s t
    rw [hχ]
  have hIΨ : Integrable (fun t => ∫ s, Φ (e s) * χ s t ∂ν) ν := by
    have h0 := (integrable_map_equiv m _).mp hI
    exact h0.congr (ae_of_all _ fun t => hinner t)
  have key := hF (fun s => Φ (e s)) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hIΨ (e.symm z)
  rw [integral_map_equiv]
  calc ∫ t, (∫ x, Φ x * χ' x (m t) ∂(ν.map m)) * χ' (m t) z ∂ν
      = ∫ t, (∫ s, Φ (e s) * χ s t ∂ν) * χ t (e.symm z) ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun t => ?_)
        show (∫ x, Φ x * χ' x (e t) ∂(ν.map m)) * χ' (e t) z =
          (∫ s, Φ (e s) * χ s t ∂ν) * χ t (e.symm z)
        rw [hinner t, ← hχ t (e.symm z), e.apply_symm_apply]
    _ = Φ (-z) := by rw [key, map_neg, e.apply_symm_apply]

omit [IsTopologicalAddGroup X] [IsTopologicalAddGroup Y] in

theorem density_comp {V Z : Type} [MeasurableSpace V] (e : X ≃ₜ+ Y) {μ : Measure V} {ν : Measure X}
    {f : V → Z} {ι : Y → Z} (hι : Function.Injective ι) {f' : V → X} (hf : ∀ v, f v = ι (e (f' v)))
    {B' : Set Y} {B : Set X} (hB : ∀ s ∈ B, e s ∈ B') {Φ : V → ℂ} {g : Y → ℂ}
    (h : IsContDensityOn μ f ι (ν.map e) B' Φ g) : IsContDensityOn μ f' id ν B Φ (fun s => g (e s)) := by
  obtain ⟨hg, hS⟩ := h
  set m : X ≃ᵐ Y := e.toHomeomorph.toMeasurableEquiv with hm
  refine ⟨hg.comp e.continuous.continuousOn (fun s hs => hB s hs), fun S hSc hSB => ?_⟩
  have h1 := hS (e '' S) (hSc.image e.continuous) (by rintro _ ⟨s, hs, rfl⟩; exact hB s (hSB hs))
  have hpre : f ⁻¹' (ι '' (e '' S)) = f' ⁻¹' (id '' S) := by
    ext v
    constructor
    · rintro ⟨y, ⟨s, hs, rfl⟩, hy⟩
      rw [hf v] at hy
      have hs' : s = f' v := EquivLike.injective e (hι hy)
      exact ⟨f' v, hs' ▸ hs, rfl⟩
    · rintro ⟨s, hs, hsv⟩
      exact ⟨e s, ⟨s, hs, rfl⟩, by rw [hf v, ← hsv]; rfl⟩
  rw [hpre] at h1
  rw [h1]
  have hmap : ν.map e = ν.map m := rfl
  rw [hmap, setIntegral_map_equiv]
  rw [show ⇑m ⁻¹' (⇑e '' S) = S from Set.preimage_image_eq S (EquivLike.injective e)]
  rfl

end Transport

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

private theorem exists_not_fixed_of_isCMExt (h : IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  by_contra hno
  push Not at hno
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := h.2.1.isComplex w
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, ← h.2.2.2, hno]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (h : IsCMExt F E σ) :
    ∃ w : E, σ w = -w ∧ ∀ x : E, ∃ a b : F, x = algebraMap F E a + algebraMap F E b * w := by
  obtain ⟨y, hy⟩ := exists_not_fixed_of_isCMExt h
  refine ⟨y - σ y, by rw [map_sub, sigma_sigma h]; ring, ?_⟩
  have hw : y - σ y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hli : LinearIndependent F ![(1 : E), y - σ y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have h2 := congrArg σ hst
    simp only [map_add, map_mul, AlgHom.commutes, map_sub, sigma_sigma h, map_zero] at h2
    have h3 : (2 : E) * algebraMap F E t * (y - σ y) = 0 := by linear_combination hst - h2
    have ht : algebraMap F E t = 0 := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · rcases mul_eq_zero.mp h4 with h5 | h5
        · exact absurd h5 two_ne_zero
        · exact h5
      · exact absurd h4 hw
    have ht' : t = 0 := (algebraMap F E).injective (by rw [ht, map_zero])
    subst ht'
    refine ⟨(algebraMap F E).injective ?_, rfl⟩
    simpa using hst
  have hsp := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, h.2.2.1])
  intro x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp (hsp ▸ Submodule.mem_top : x ∈ _)
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp [Algebra.smul_def]

theorem add_sigma (h : IsCMExt F E σ) (x : E) : x + σ x = algebraMap F E (Algebra.trace F E x) := by
  obtain ⟨w, hw, hdec⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul h
  have htw : Algebra.trace F E w = 0 := by
    let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun z => sigma_sigma h z)
      (AlgHom.ext fun z => sigma_sigma h z)
    have h1 := Algebra.trace_eq_of_algEquiv σe w
    change Algebra.trace F E (σ w) = _ at h1
    rw [hw, map_neg] at h1
    have h2 : (2 : F) * Algebra.trace F E w = 0 := by linear_combination -h1
    simpa using h2
  obtain ⟨a, b, rfl⟩ := hdec x
  have e1 : σ (algebraMap F E a + algebraMap F E b * w) = algebraMap F E a - algebraMap F E b * w := by
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hw]
    ring
  have e2 : Algebra.trace F E (algebraMap F E a + algebraMap F E b * w) = 2 * a := by
    rw [map_add, ← Algebra.smul_def, map_smul, htw, smul_zero, add_zero, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul,
      Nat.cast_ofNat]
  rw [e1, e2, map_mul, map_ofNat]
  ring

variable (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have e : r ⊗ₜ[F] x = r • ((1 : R) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e, map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have hl : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = (Algebra.lmul F E x).baseChange R := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  rw [hl, LinearMap.trace_baseChange]

theorem add_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    z + sigR R σ z = algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [trace_tmul]
    have hs : sigR R σ (r ⊗ₜ[F] x) = r ⊗ₜ[F] σ x := by simp [sigR]
    rw [hs, ← TensorProduct.tmul_add, add_sigma h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self_apply, Algebra.algebraMap_eq_smul_one (A := E),
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  | add p q hp hq => rw [map_add, map_add, map_add, ← hp, ← hq]; abel

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [sigR, sigma_sigma h]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

theorem sigR_algebraMap (t : R) : sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (t ⊗ₜ[F] (1 : E)) = t ⊗ₜ[F] (1 : E)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

theorem half_two : algebraMap F R (1 / 2) * 2 = 1 := by
  rw [show (2 : R) = algebraMap F R 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem fixed_eq (h : IsCMExt F E σ) {z : R ⊗[F] E} (hz : sigR R σ z = z) :
    algebraMap R (R ⊗[F] E) (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) = z := by
  rw [map_mul, ← add_sigR R h z, hz]
  have h2 := congrArg (algebraMap R (R ⊗[F] E)) (half_two (F := F) R)
  rw [map_mul, map_one, map_ofNat] at h2
  linear_combination z * h2

theorem half_trace (h : IsCMExt F E σ) (t : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) t) = t := by
  have e : algebraMap R (R ⊗[F] E) t = t ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [e, trace_tmul, ← map_one (algebraMap F E), Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul,
    mul_one, Nat.cast_ofNat, map_ofNat]
  linear_combination t * half_two (F := F) R

theorem sigR_hR (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (x : Fin M → R ⊗[F] E) : sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [JR, inclR, sigR, hJ.1 j i]
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R h, hJR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def hermOne (h : IsCMExt F E σ) : R ≃ₜ+ HermR R σ 1 where
  toFun t := ⟨fun _ _ => algebraMap R (R ⊗[F] E) t, fun _ _ => sigR_algebraMap R t⟩
  invFun S := algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S.1 0 0)
  left_inv t := half_trace R h t
  right_inv S := by
    apply Subtype.ext
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact fixed_eq R h (S.2 0 0)
  map_add' s t := by
    apply Subtype.ext
    funext a b
    exact map_add _ s t
  continuous_toFun := by
    haveI := isModTop (F := F) (E := E) R
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
    refine Continuous.subtype_mk (continuous_pi fun _ => continuous_pi fun _ => ?_) _
    simp only [Algebra.algebraMap_eq_smul_one]
    fun_prop
  continuous_invFun := by
    haveI := isModTop (F := F) (E := E) R
    refine continuous_const.mul ((IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))).comp ?_)
    exact (continuous_apply_apply 0 0).comp continuous_subtype_val

theorem hermOne_val (h : IsCMExt F E σ) (t : R) (a b : Fin 1) :
    (hermOne R h t).1 a b = algebraMap R (R ⊗[F] E) t := rfl

theorem pair_hermOne (h : IsCMExt F E σ) (s t : R) : pairHerm R σ 1 (hermOne R h s) (hermOne R h t) = s * t := by
  simp only [pairHerm, hermOne_val R h, Fin.sum_univ_one, ← map_mul]
  exact half_trace R h (s * t)

theorem gram_hermOne (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (X : Fin 1 → Fin M → R ⊗[F] E) : gramR R σ J X = (hermOne R h (qR R σ J (X 0))).1 := by
  ext a b
  rw [hermOne_val R h, Subsingleton.elim a 0, Subsingleton.elim b 0]
  exact (fixed_eq R h (sigR_hR R h hJ (X 0))).symm

theorem unit_hermOne (h : IsCMExt F E σ) {t : R} (ht : IsUnit t) : IsUnit (hermOne R h t).1.det := by
  rw [Matrix.det_fin_one, hermOne_val R h]
  exact ht.map _

theorem hermOf_eq (h : IsCMExt F E σ) (β : F) (hT) :
    hermOf R σ (fun _ _ : Fin 1 => algebraMap F E β) hT = hermOne R h (algebraMap F R β) := by
  apply Subtype.ext
  funext a b
  rw [hermOne_val R h]
  show inclR R (algebraMap F E β) = _
  rw [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
    IsScalarTower.algebraMap_apply F R (R ⊗[F] E)]

end Field

theorem rapid_of_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d M n : ℕ} (b : Module.Basis (Fin d) F E) {Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ}
    (hc : Continuous Φ) (hs : HasCompactSupport Φ) : RapidDecay b Φ := by
  intro N
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hsize : Continuous (sizeTup b : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ) := by
    unfold sizeTup sizeInf
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
    have hk : Continuous fun y : Ainf F ⊗[F] E => (Algebra.TensorProduct.basis (Ainf F) b).repr y k :=
      (IsModuleTopology.continuous_of_linearMap (R := Ainf F)
        ((Algebra.TensorProduct.basis (Ainf F) b).coord k)).congr fun y => Module.Basis.coord_apply _ _ _
    exact (((continuous_apply v).comp hk).comp ((continuous_apply i).comp (continuous_apply a))).norm
  have hg : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hc.norm.mul ((continuous_const.add hsize).pow N)
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hs.norm.mul_right
  exact ⟨C, fun X => (Real.le_norm_self _).trans (hC X)⟩

theorem hermGroup {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (n : ℕ) : IsTopologicalAddGroup (HermR R σ n) := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have : ContinuousNeg (R ⊗[F] E) := by
    refine ⟨?_⟩
    have hn : (fun x : R ⊗[F] E => -x) = fun x => (-1 : R) • x :=
      funext fun x => (neg_one_smul R x).symm
    rw [hn]
    exact continuous_const_smul _
  have : IsTopologicalAddGroup (R ⊗[F] E) :=
    { toContinuousAdd := inferInstance, toContinuousNeg := inferInstance }
  infer_instance

section Sd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R]

theorem sd_of_herm (h : IsCMExt F E σ) {ψ : R → ℂ} {ν : Measure (HermR R σ 1)} (hν : SdHerm F E σ R ψ 1 ν) :
    SelfDual (ν.map (hermOne R h).symm) (fun s t => ψ (s * t)) := by
  have := hermGroup σ R 1
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  refine selfDual_map (hermOne R h).symm ?_ hν
  intro S T
  obtain ⟨s, rfl⟩ := EquivLike.surjective (hermOne R h) S
  obtain ⟨t, rfl⟩ := EquivLike.surjective (hermOne R h) T
  show ψ ((hermOne R h).symm (hermOne R h s) * (hermOne R h).symm (hermOne R h t)) =
    ψ (pairHerm R σ 1 (hermOne R h s) (hermOne R h t))
  rw [ContinuousAddEquiv.symm_apply_apply, ContinuousAddEquiv.symm_apply_apply, pair_hermOne R h]

theorem sd_to_herm (h : IsCMExt F E σ) {ψ : R → ℂ} {ν : Measure R} (hν : SelfDual ν (fun s t => ψ (s * t))) :
    SdHerm F E σ R ψ 1 (ν.map (hermOne R h)) := by
  have := hermGroup σ R 1
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  unfold SdHerm
  exact selfDual_map (hermOne R h) (χ' := fun S T => ψ (pairHerm R σ 1 S T))
    (fun s t => congrArg ψ (pair_hermOne R h s t)) hν

theorem dens_of_herm (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    {μ : Measure (Fin 1 → Fin M → R ⊗[F] E)} {ν : Measure R} {B : Set R} (hB : ∀ s ∈ B, IsUnit s)
    {Φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ} {g : HermR R σ 1 → ℂ}
    (hd : IsContDensityOn μ (gramR R σ J) Subtype.val (ν.map (hermOne R h))
      {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} Φ g) :
    IsContDensityOn μ (fun X => qR R σ J (X 0)) id ν B Φ (fun s => g (hermOne R h s)) := by
  have : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have key := density_comp (V := Fin 1 → Fin M → R ⊗[F] E) (Z := Matrix (Fin 1) (Fin 1) (R ⊗[F] E))
    (hermOne R h) (μ := μ) (ν := ν) (f := gramR R σ J) (ι := Subtype.val) Subtype.val_injective
    (f' := fun X => qR R σ J (X 0)) (fun X => gram_hermOne R h hJ X)
    (B' := {S | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}) (B := B)
    (fun s hs => unit_hermOne R h (hB s hs)) (Φ := Φ) (g := g)
  exact key hd

end Sd

theorem gram_form (hP : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (n : ℕ) (hn : 2 * n < M)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hd : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)
    (h1 : Continuous Φinf) (h2 : HasCompactSupport Φinf)
    (h3 : ∀ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φinf ∘ e.symm))
    (h4 : IsPureFin b Φf Φv) (h5 : IsProdInfFin Φ Φinf Φf) :
    AllSome (IsHaarH F E σ M J) fun μ => AllSome (IsFDH F E σ M J μ) fun 𝓕 =>
    AllSome (IsCharAF F) fun ψ =>
    AllSome (SdW F E σ M J (Ainf F) (psiInf F ψ) n) fun μinf =>
    AllSome (SdHerm F E σ (Ainf F) (psiInf F ψ) n) fun νinf =>
    AllSome (fun μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
      ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) fun μv =>
    AllSome (fun νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ n) =>
      ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) n (νv v)) fun νv =>
    ∃ (ginf : HermR (Ainf F) σ n → ℂ) (gv : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → ℂ),
      IsContDensityOn μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φinf ginf ∧
      (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
        {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
      Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
      meanC μ 𝓕 (thSum F E σ M J Φ {X | gramE σ J X = T}) =
        ginf (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT) := by
  exact (hP F E σ h M J hJ).2 n hn T hT hd d b Φ Φinf Φf Φv h1 (rapid_of_compact b h1 h2) ⟨h2, h3⟩ h4 h5

end GlobalTheory.GaussMean.OneVec

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice OneVec

theorem oneVectorCc_of_siegelWeil (hP : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) : OneVectorCc := by
  intro F E _ _ _ _ _ σ h M J hJ
  refine ⟨(hP F E σ h M J hJ).1, ?_⟩
  intro hM β hβ d b Φ Φi Φf Φv h1 h2 h3 h4 h5
  have hd : Matrix.det (fun _ _ : Fin 1 => algebraMap F E β) ≠ 0 :=
    fun h0 => hβ ((map_eq_zero _).mp ((Matrix.det_fin_one _).symm.trans h0))
  have G := gram_form hP h hJ 1 (by omega) (fun _ _ => algebraMap F E β) (fun _ _ => σ.commutes β) hd
    d b Φ Φi Φf Φv h1 h2 h3 h4 h5
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨⟨μ0, hμ0⟩, Gμ⟩ := G
  obtain ⟨⟨𝓕0, h𝓕0⟩, G𝓕⟩ := Gμ μ0 hμ0
  obtain ⟨⟨ψ0, hψ0⟩, -⟩ := G𝓕 𝓕0 h𝓕0
  refine ⟨⟨ψ0, hψ0⟩, fun ψ hψ => ?_⟩
  refine ⟨⟨μ0, hμ0⟩, fun μ hμ => ?_⟩
  obtain ⟨⟨𝓕1, h𝓕1⟩, Gμ'⟩ := Gμ μ hμ
  refine ⟨⟨𝓕1, h𝓕1⟩, fun 𝓕 h𝓕 => ?_⟩
  obtain ⟨-, Gψ⟩ := Gμ' 𝓕 h𝓕
  obtain ⟨⟨μi0, hμi0⟩, G2⟩ := Gψ ψ hψ
  obtain ⟨⟨νi0, hνi0⟩, G3⟩ := G2 μi0 hμi0
  obtain ⟨⟨μv0, hμv0⟩, G4⟩ := G3 νi0 hνi0
  obtain ⟨⟨νv0, hνv0⟩, -⟩ := G4 μv0 hμv0
  refine ⟨⟨μi0, hμi0⟩, ⟨_, sd_of_herm h (ψ := psiInf F ψ) hνi0⟩, ⟨μv0, hμv0⟩,
    ⟨fun v => (νv0 v).map (hermOne (Fv F v) h).symm, fun v => sd_of_herm h (ψ := psiV F ψ v) (hνv0 v)⟩, ?_⟩
  intro μi νi μv νv hμi hνi hμv hνv
  obtain ⟨-, G3'⟩ := G2 μi hμi
  obtain ⟨-, G4'⟩ := G3' (νi.map (hermOne (Ainf F) h)) (sd_to_herm h (ψ := psiInf F ψ) hνi)
  obtain ⟨-, G5'⟩ := G4' μv hμv
  obtain ⟨ginf, gv, hdi, hdv, hmul, hmean⟩ :=
    G5' (fun v => (νv v).map (hermOne (Fv F v) h)) (fun v => sd_to_herm h (ψ := psiV F ψ v) (hνv v))
  refine ⟨fun s => ginf (hermOne (Ainf F) h s), fun v s => gv v (hermOne (Fv F v) h s), ?_, ?_, ?_, ?_⟩
  · exact dens_of_herm h hJ (fun s hs => hs) hdi
  · intro v
    exact dens_of_herm h hJ (fun s hs => isUnit_iff_ne_zero.mpr hs) (hdv v)
  · simpa only [hermOf_eq _ h] using hmul
  · have hS : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E β} =
        {x | hE σ J (x 0) (x 0) = algebraMap F E β} := by
      ext X
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hX
        exact congrFun (congrFun hX 0) 0
      · intro hX
        funext a c
        rw [Subsingleton.elim a 0, Subsingleton.elim c 0]
        exact hX
    rw [← hS]
    simpa only [hermOf_eq _ h] using hmean

end GlobalTheory.GaussMean
