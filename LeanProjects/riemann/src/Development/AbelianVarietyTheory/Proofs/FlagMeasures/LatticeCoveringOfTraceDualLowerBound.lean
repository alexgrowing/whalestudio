import Mathlib
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Complexify
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.TraceCover

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

theorem eq_zero_of_sum_re (a : InfinitePlace K → ℂ)
    (h : ∀ x : K, ∑ w, (w.embedding x * a w).re = 0) : a = 0 := by
  classical
  let F : mixedEmbedding.mixedSpace K →ₗ[ℝ] ℝ :=
    { toFun := fun z => ∑ w : InfinitePlace K, (z.2 ⟨w, IsTotallyComplex.isComplex w⟩ * a w).re
      map_add' := by
        intro x y
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Prod.smul_snd, Pi.smul_apply, smul_mul_assoc, Complex.smul_re, smul_eq_mul,
          RingHom.id_apply, Finset.mul_sum] }
  have hF : F = 0 := by
    apply (mixedEmbedding.latticeBasis K).ext
    intro i
    rw [mixedEmbedding.latticeBasis_apply]
    simpa [F] using h _
  funext w
  have := LinearMap.congr_fun hF (0, Pi.single ⟨w, IsTotallyComplex.isComplex w⟩ (starRingEnd ℂ (a w)))
  simp only [F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at this
  rw [Finset.sum_eq_single w] at this
  · rw [Pi.single_eq_same, mul_comm, Complex.mul_conj, Complex.ofReal_re] at this
    simpa using this
  · intro b _ hb
    rw [Pi.single_eq_of_ne (by simpa using hb)]
    simp
  · simp

theorem eq_zero_of_sum_re_lin {ι : Type} [Fintype ι] (g : InfinitePlace K → ((ι → ℂ) →ₗ[ℂ] ℂ))
    (h : ∀ y : ι → K, ∑ w, (g w (fun j => w.embedding (y j))).re = 0) (w : InfinitePlace K) :
    g w = 0 := by
  classical
  apply (Pi.basisFun ℂ ι).ext
  intro i
  have := eq_zero_of_sum_re (fun w => g w (Pi.single i 1)) (by
    intro x
    rw [← h (Pi.single i x)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← smul_eq_mul, ← map_smul]
    congr 2
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj])
  simpa using congrFun this w

theorem trace_eq_sum (a : K) :
    ((Algebra.trace ℚ K a : ℚ) : ℝ) = ∑ w : InfinitePlace K, 2 * (w.embedding a).re := by
  classical
  have e := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := a))
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at e
  rw [e, ← (RingHom.equivRatAlgHom (R := K) (S := ℂ)).sum_comp,
    ← Finset.univ.sum_fiberwise (fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
      ((RingHom.equivRatAlgHom (R := K) (S := ℂ)) φ a).re = (w.embedding a).re := by
    intro φ hφ
    have h1 : InfinitePlace.mk φ = InfinitePlace.mk w.embedding := by
      rw [InfinitePlace.mk_embedding]; simpa using hφ
    rcases InfinitePlace.mk_eq_iff.1 h1 with h2 | h2
    · rw [← h2]; rfl
    · rw [← h2]; simp [RingHom.equivRatAlgHom]
  rw [Finset.sum_congr rfl this, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two]
  simp

omit [IsTotallyComplex K] in

theorem exists_basis {ι : Type} [Fintype ι] (L : Submodule (𝓞 K) (ι → K)) (hfg : L.FG)
    (hsp : Submodule.span K (L : Set (ι → K)) = ⊤) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ (ι → K)),
      ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ y ∈ L := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let b0 := Module.Free.chooseBasis ℤ L
  let s : L →ₗ[ℤ] (ι → K) := L.subtype.restrictScalars ℤ
  have hs : Function.Injective s := Subtype.val_injective
  have hli : LinearIndependent ℤ (s ∘ b0) :=
    b0.linearIndependent.map' s (LinearMap.ker_eq_bot.2 hs)
  have hli' : LinearIndependent ℚ (s ∘ b0) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have hmem : ∀ y, y ∈ Submodule.span ℤ (Set.range (s ∘ b0)) ↔ y ∈ L := by
    intro y
    rw [Set.range_comp, ← Submodule.map_span, b0.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨z, rfl⟩; exact z.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have hL : ∀ y ∈ L, y ∈ Submodule.span ℚ (Set.range (s ∘ b0)) := fun y hy =>
    Submodule.span_subset_span ℤ ℚ _ ((hmem y).2 hy)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range (s ∘ b0)) := by
    intro y _
    have hy : y ∈ Submodule.span K (L : Set (ι → K)) := by rw [hsp]; trivial
    have key : ∀ k : K, k • y ∈ Submodule.span ℚ (Set.range (s ∘ b0)) := by
      induction hy using Submodule.span_induction with
      | mem x hx =>
        intro k
        rw [← (integralBasis K).sum_repr k, Finset.sum_smul]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [smul_assoc]
        refine Submodule.smul_mem _ _ (hL _ ?_)
        rw [integralBasis_apply, algebraMap_smul]
        exact L.smul_mem _ hx
      | zero => intro k; simp
      | add x y _ _ hx hy => intro k; rw [smul_add]; exact Submodule.add_mem _ (hx trivial k) (hy trivial k)
      | smul a x _ hx => intro k; rw [smul_smul]; exact hx trivial _
    simpa using key 1
  refine ⟨_, inferInstance, Module.Basis.mk hli' htop, ?_⟩
  intro y
  rw [Module.Basis.coe_mk]
  exact hmem y

omit [IsTotallyComplex K] in

theorem exists_trace_form {ι : Type} [Fintype ι] (φ : (ι → K) →ₗ[ℚ] ℚ) :
    ∃ f : ι → K, ∀ y, Algebra.trace ℚ K (f ⬝ᵥ y) = φ y := by
  classical
  let D := (Algebra.traceForm ℚ K).toDual (traceForm_nondegenerate ℚ K)
  refine ⟨fun i => D.symm (φ ∘ₗ LinearMap.single ℚ (fun _ => K) i), fun y => ?_⟩
  rw [dotProduct, map_sum]
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_toDual_symm_apply _ _

section Main

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

noncomputable def rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) :
    (ι → K) →ₗ[ℚ] PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ) :=
  AddMonoidHom.toRatLinearMap
  { toFun := fun y => WithLp.toLp 2 (fun p => M p.1 (fun j => p.1.embedding (y j)) p.2)
    map_zero' := by
      ext p
      have : (fun j : ι => p.1.embedding ((0 : ι → K) j)) = 0 := by funext j; simp
      simp only [this, map_zero]; rfl
    map_add' := by
      intro x y
      ext p
      have : (fun j : ι => p.1.embedding ((x + y) j)) =
          (fun j => p.1.embedding (x j)) + (fun j => p.1.embedding (y j)) := by funext j; simp
      simp only [this, map_add]; rfl }

noncomputable def form (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (w : InfinitePlace K) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := (fun i => starRingEnd ℂ (u (w, i))) ⬝ᵥ M w z
  map_add' x y := by rw [map_add, dotProduct_add]
  map_smul' c x := by rw [map_smul, dotProduct_smul]; rfl

omit [IsTotallyComplex K] [Fintype ι] in
theorem inner_rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (y : ι → K) :
    inner ℝ (rho M y) u = ∑ w, (form M u w (fun j => w.embedding (y j))).re := by
  rw [real_inner_comm, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [form, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, mul_comm]
  rfl

omit [IsTotallyComplex K] [Fintype ι] [NumberField K] in
theorem eq_zero_of_form (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ)))
    (u : PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) (h : ∀ w, form M u w = 0) : u = 0 := by
  classical
  ext ⟨w, i⟩
  have := LinearMap.congr_fun (h w) ((M w).symm (Pi.single i 1))
  simpa [form] using this

theorem finrank_eq (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) :
    Module.finrank ℝ (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) =
      2 * (Fintype.card (InfinitePlace K) * Fintype.card ι) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h := (M w).finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card] at h
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, h, mul_comm]

theorem finrank_rat : Module.finrank ℚ (ι → K) =
      2 * (Fintype.card (InfinitePlace K) * Fintype.card ι) := by
  rw [Module.finrank_pi_fintype, IsTotallyComplex.finrank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  simp; ring

theorem span_rho (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) {κ : Type}
    (b : Module.Basis κ ℚ (ι → K)) : ⊤ ≤ Submodule.span ℝ (Set.range (rho M ∘ b)) := by
  rw [top_le_iff, ← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro u hu
  apply eq_zero_of_form M
  apply eq_zero_of_sum_re_lin
  intro y
  rw [← inner_rho]
  apply (Submodule.mem_orthogonal _ _).1 hu
  apply Submodule.span_subset_span ℚ ℝ
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq]
  exact ⟨y, trivial, rfl⟩

end Main

theorem cover : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι ι' : Type) [Fintype ι] [Fintype ι'] (L : Submodule (𝓞 K) (ι → K)) (M : InfinitePlace K → ((ι → ℂ) ≃ₗ[ℂ] (ι' → ℂ))) (lam : ℝ), L.FG → Submodule.span K (L : Set (ι → K)) = ⊤ → 0 < lam → (∀ (f : ι → K) (c : InfinitePlace K → ι' → ℂ), f ≠ 0 → (∀ y ∈ L, ∃ m : ℤ, Algebra.trace ℚ K (f ⬝ᵥ y) = m) → (∀ (w : InfinitePlace K) (y : ι → ℂ), (fun i => w.embedding (f i)) ⬝ᵥ y = c w ⬝ᵥ M w y) → lam ^ 2 ≤ ∑ w, ∑ i, ‖c w i‖ ^ 2) → ∀ t : InfinitePlace K → ι' → ℂ, ∃ y ∈ L, Real.sqrt (∑ w, ∑ i, ‖t w i - M w (fun j => w.embedding (y j)) i‖ ^ 2) ≤ (Fintype.card (InfinitePlace K) : ℝ) * (Fintype.card ι : ℝ) / (2 * lam) := by
  intro K _ _ _ ι ι' _ _ L M lam hfg hsp hlam hdual t
  classical
  obtain ⟨κ, _, b, hb⟩ := exists_basis L hfg hsp
  have hcard : Fintype.card κ = Module.finrank ℝ (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ)) := by
    rw [finrank_eq M, ← finrank_rat, Module.finrank_eq_card_basis b]
  let B := basisOfTopLeSpanOfCardEqFinrank (rho M ∘ b) (span_rho M b) hcard
  have hB : ⇑B = rho M ∘ b := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have hΛ : ∀ x, x ∈ Submodule.span ℤ (Set.range B) ↔ ∃ y ∈ L, rho M y = x := by
    intro x
    have e : Set.range B = ((rho M).restrictScalars ℤ) '' Set.range b := by
      rw [hB, Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, Submodule.mem_map]
    simp only [hb, LinearMap.restrictScalars_apply]
  obtain ⟨l, hl, hle⟩ := GlobalTheory.transferenceCover_holds (PiLp 2 (fun _ : InfinitePlace K × ι' => ℂ))
    (Submodule.span ℤ (Set.range B)) (2 * lam) (by positivity) (by
      intro u hu hint
      have hint' : ∀ y ∈ L, ∃ n : ℤ, inner ℝ (rho M y) u = (n : ℝ) :=
        fun y hy => hint _ ((hΛ _).2 ⟨y, hy, rfl⟩)
      choose m hm using fun k => hint' (b k) ((hb _).1 (Submodule.subset_span ⟨k, rfl⟩))
      obtain ⟨f, hf⟩ := exists_trace_form (b.constr ℚ (fun k => (m k : ℚ)))
      have hφ : ∀ y, ((b.constr ℚ (fun k => (m k : ℚ)) y : ℚ) : ℝ) = inner ℝ (rho M y) u := by
        have : (Algebra.linearMap ℚ ℝ) ∘ₗ b.constr ℚ (fun k => (m k : ℚ)) =
            (((innerₗ _).flip u).restrictScalars ℚ) ∘ₗ rho M := by
          apply b.ext
          intro k
          simp [← hm, real_inner_comm]
        intro y
        simpa [real_inner_comm] using LinearMap.congr_fun this y
      let d : (w : InfinitePlace K) → (ι → ℂ) →ₗ[ℂ] ℂ := fun w =>
        { toFun := fun z => (fun i => w.embedding (f i)) ⬝ᵥ z
          map_add' := fun x y => dotProduct_add _ _ _
          map_smul' := fun c x => by rw [dotProduct_smul]; rfl }
      have hz := eq_zero_of_sum_re_lin (fun w => (2 : ℂ) • d w - form M u w) (by
        intro y
        have h1 := hφ y
        rw [← hf, trace_eq_sum, inner_rho, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [d, dotProduct])
      have hz' : ∀ w z, (fun i => w.embedding (f i)) ⬝ᵥ z =
          (fun i => starRingEnd ℂ (u (w, i)) / 2) ⬝ᵥ M w z := by
        intro w z
        have h1 := LinearMap.congr_fun (hz w) z
        simp only [d, form, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.zero_apply, smul_eq_mul, sub_eq_zero] at h1
        have h2 : (fun i => starRingEnd ℂ (u (w, i)) / 2) ⬝ᵥ M w z =
            ((fun i => starRingEnd ℂ (u (w, i))) ⬝ᵥ M w z) / 2 := by
          simp only [dotProduct, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [h2, ← h1]; ring
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hu
        apply eq_zero_of_form M
        intro w
        have h1 := hz w
        have h2 : d w = 0 := by ext z; simp [d, dotProduct]
        simpa [h2] using h1
      have hl := hdual f (fun w i => starRingEnd ℂ (u (w, i)) / 2) hf0 (by
        intro y hy
        obtain ⟨n, hn⟩ := hint' y hy
        refine ⟨n, ?_⟩
        rw [← hφ, ← hf] at hn
        exact_mod_cast hn) hz'
      have hn : ‖u‖ ^ 2 = 4 * ∑ w, ∑ i, ‖starRingEnd ℂ (u (w, i)) / 2‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp; ring
      apply le_of_sq_le_sq _ (norm_nonneg _) |>.trans le_rfl
      nlinarith) (WithLp.toLp 2 (fun p => t p.1 p.2))
  obtain ⟨y, hy, rfl⟩ := (hΛ _).1 hl
  refine ⟨y, hy, ?_⟩
  rw [finrank_eq M, PiLp.norm_eq_of_L2, Fintype.sum_prod_type] at hle
  rw [le_div_iff₀ (by positivity)]
  refine le_trans (le_of_eq ?_) (hle.trans (le_of_eq ?_))
  · rfl
  · push_cast; ring

end GlobalTheory.TraceCover
