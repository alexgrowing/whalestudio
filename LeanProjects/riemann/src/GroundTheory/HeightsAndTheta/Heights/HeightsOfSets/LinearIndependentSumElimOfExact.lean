import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Extension
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HermitianDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open scoped ComplexOrder

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem gramDet_comap {E M : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]
    [Module.Projective (𝓞 K) M] (h : HermitianMetric K E) (f : M →ₗ[𝓞 K] E)
    (hf : Function.Injective f) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → M) :
    gramDet (h.comap f hf) σ s = gramDet h σ (fun i ↦ f (s i)) := by
  simp only [gramDet]
  congr 3

theorem HermitianBundle.degree_eq_of_linearIndependent (E : HermitianBundle K)
    (F : Submodule (𝓞 K) E.carrier) {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → F}
    (hs : LinearIndependent (𝓞 K) s) (hcard : Fintype.card ι = E.rank F) :
    E.degree F = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ,
        Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun i ↦ (s i : E.carrier))) := by
  rw [HermitianBundle.degree_eq_arithDegree, arithDegree_eq _ hs hcard, GroundTheory.Heights₂.Heights.degreeWith]
  simp only [gramDet_comap, Submodule.subtype_apply]

section Exact

variable {A B C : Type*} [AddCommGroup A] [Module (𝓞 K) A] [AddCommGroup B] [Module (𝓞 K) B]
  [AddCommGroup C] [Module (𝓞 K) C] {i : A →ₗ[𝓞 K] B} {p : B →ₗ[𝓞 K] C}

omit [NumberField K] in

theorem finrank_eq_add_of_exact [Module.Finite (𝓞 K) A] [Module.Finite (𝓞 K) B]
    [Module.Finite (𝓞 K) C] (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) :
    Module.finrank (𝓞 K) B = Module.finrank (𝓞 K) A + Module.finrank (𝓞 K) C := by
  have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range i)
  have hker : LinearMap.ker p = LinearMap.range i := hex.linearMap_ker_eq
  let e1 : (B ⧸ LinearMap.range i) ≃ₗ[𝓞 K] C :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (p.quotKerEquivOfSurjective hp)
  let e2 : A ≃ₗ[𝓞 K] LinearMap.range i := LinearEquiv.ofInjective i hi
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h1
  norm_cast at h1
  rw [e1.finrank_eq, ← e2.finrank_eq] at h1
  omega

variable {m n : Type*} [Fintype m] [Fintype n]

omit [NumberField K] in

theorem linearIndependent_sumElim_of_exact (hi : Function.Injective i) (hex : Function.Exact i p)
    {s' : m → A} {s'' : n → C} {u : n → B} (hu : ∀ j, p (u j) = s'' j)
    (hs' : LinearIndependent (𝓞 K) s') (hs'' : LinearIndependent (𝓞 K) s'') :
    LinearIndependent (𝓞 K) (Sum.elim (fun k ↦ i (s' k)) u) := by
  rw [Fintype.linearIndependent_iff] at hs' hs'' ⊢
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
    have := congrArg p hg
    simpa [map_add, map_sum, map_smul, hex.apply_apply_eq_zero, hu] using this
  have hr := hs'' _ h2
  have h1 : ∑ k, g (Sum.inl k) • s' k = 0 := by
    apply hi
    simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
    rw [map_sum, map_zero]
    simpa [map_smul] using hg
  have hl := hs' _ h1
  rintro (k | j)
  exacts [hl k, hr j]

omit [NumberField K] in

theorem card_quotient_sumElim_of_exact (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) {s' : m → A} {s'' : n → C} {u : n → B} (hu : ∀ j, p (u j) = s'' j)
    (hs'' : LinearIndependent (𝓞 K) s'') :
    Nat.card (B ⧸ Submodule.span (𝓞 K) (Set.range (Sum.elim (fun k ↦ i (s' k)) u))) =
      Nat.card (A ⧸ Submodule.span (𝓞 K) (Set.range s')) *
        Nat.card (C ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
  set w := Sum.elim (fun k ↦ i (s' k)) u
  set N := Submodule.span (𝓞 K) (Set.range w)
  set S := N ⊔ LinearMap.range i
  rw [← Submodule.card_quotient_mul_card_quotient S N le_sup_left]
  congr 1
  · have hS : S.map N.mkQ = LinearMap.range (N.mkQ ∘ₗ i) := by
      rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, LinearMap.range_comp]
    have hker : LinearMap.ker (N.mkQ ∘ₗ i) = Submodule.span (𝓞 K) (Set.range s') := by
      ext x
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        rw [Fintype.sum_sum_type] at hg
        simp only [w, Sum.elim_inl, Sum.elim_inr] at hg
        have h2 : ∑ j, g (Sum.inr j) • s'' j = 0 := by
          have := congrArg p hg
          simpa [map_add, map_sum, map_smul, hex.apply_apply_eq_zero, hu] using this
        have hr := (Fintype.linearIndependent_iff.mp hs'') _ h2
        simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
        have : i (∑ k, g (Sum.inl k) • s' k) = i x := by
          rw [← hg, map_sum]
          simp [map_smul]
        rw [← hi this]
        exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · intro hx
        have : i x ∈ (Submodule.span (𝓞 K) (Set.range s')).map i :=
          Submodule.mem_map_of_mem hx
        rw [Submodule.map_span] at this
        refine Submodule.span_mono ?_ this
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨Sum.inl k, rfl⟩
    rw [hS, ← hker]
    exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
  · set φ := (Submodule.span (𝓞 K) (Set.range s'')).mkQ ∘ₗ p
    have hφ : Function.Surjective φ := (Submodule.mkQ_surjective _).comp hp
    have hker : LinearMap.ker φ = S := by
      apply le_antisymm
      · intro x hx
        simp only [φ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
        have hy : x - ∑ j, b j • u j ∈ LinearMap.range i := by
          rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, map_sub, map_sum]
          simp only [map_smul, hu, hb, sub_self]
        have hN : ∑ j, b j • u j ∈ N :=
          Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        have := Submodule.add_mem_sup hN hy
        rwa [add_sub_cancel] at this
      · refine sup_le ?_ ?_
        · rw [Submodule.span_le]
          rintro _ ⟨k, rfl⟩
          rcases k with k | j
          · simp [φ, w, hex.apply_apply_eq_zero]
          · simp only [φ, w, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
              Function.comp_apply, Sum.elim_inr, hu, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span ⟨j, rfl⟩
        · rintro _ ⟨y, rfl⟩
          simp [φ, hex.apply_apply_eq_zero]
    rw [← hker]
    exact Nat.card_congr (φ.quotKerEquivOfSurjective hφ).toEquiv

end Exact

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

theorem gramDet_sumElim_ge (σ : K →+* ℂ) {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (s' : m → E'.carrier) (u : n → E.carrier) :
    gramDet E'.metric σ s' * gramDet E''.metric σ (fun j ↦ X.proj (u j)) ≤
      gramDet E.metric σ (Sum.elim (fun k ↦ X.incl (s' k)) u) := by
  let L : FibreSpace E'.metric σ →ₗ[ℂ] FibreSpace E.metric σ :=
    { toFun := fun x ↦ X.incl.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.incl }
  let W := LinearMap.range L
  have : FiniteDimensional ℂ W := inferInstance
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  let a : m → FibreSpace E.metric σ := fun k ↦ fibreVec E.metric σ (X.incl (s' k))
  let b : n → FibreSpace E.metric σ := fun j ↦ fibreVec E.metric σ (u j)
  have ha : ∀ k, a k ∈ W := fun k ↦ ⟨fibreVec E'.metric σ (s' k), by
    change X.incl.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ s' k) = _
    rw [LinearMap.lTensor_tmul]
    rfl⟩
  have key := re_det_gram_sumElim_ge W a ha b
  have hga : gram ℂ a = gram ℂ (fun k ↦ fibreVec E'.metric σ (s' k)) := by
    ext i k
    exact X.incl_isometric σ (1 ⊗ₜ s' i) (1 ⊗ₜ s' k)
  let P : FibreSpace E.metric σ →ₗ[ℂ] FibreSpace E''.metric σ :=
    { toFun := fun x ↦ X.proj.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.proj }
  have hcomp : ∀ y : Fibre σ E'.carrier,
      X.proj.lTensor (ComplexAt σ) (X.incl.lTensor (ComplexAt σ) y) = 0 := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, X.exact.linearMap_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hPL : ∀ y, P (L y) = 0 := fun y ↦ hcomp y
  have hQ : ∀ j, P (Wᗮ.starProjection (b j)) = fibreVec E''.metric σ (X.proj (u j)) := by
    intro j
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    obtain ⟨y, hy⟩ := W.starProjection_apply_mem (b j)
    rw [← hy, hPL, sub_zero]
    change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ u j) = _
    rw [LinearMap.lTensor_tmul]
    rfl
  have hperp : ∀ j (w : Fibre σ E'.carrier),
      (E.metric.form σ).inner (X.incl.lTensor (ComplexAt σ) w) (Wᗮ.starProjection (b j)) = 0 :=
    fun j w ↦ Submodule.inner_right_of_mem_orthogonal (K := W) ⟨w, rfl⟩
      (Wᗮ.starProjection_apply_mem (b j))
  have hgq : gram ℂ (fun j ↦ Wᗮ.starProjection (b j)) =
      gram ℂ (fun j ↦ fibreVec E''.metric σ (X.proj (u j))) := by
    ext j k
    rw [gram_apply, gram_apply, ← hQ j, ← hQ k]
    exact (X.proj_coisometric σ _ _ (hperp j) (hperp k)).symm
  have hfam : (fun k ↦ fibreVec E.metric σ (Sum.elim (fun k ↦ X.incl (s' k)) u k)) =
      Sum.elim a b := by
    funext k
    rcases k with k | j <;> rfl
  simp only [gramDet]
  rw [hfam, ← hga, ← hgq]
  exact key

variable (F : Submodule (𝓞 K) E.carrier)

def subIncl : F.comap X.incl →ₗ[𝓞 K] F := X.incl.restrict fun _ hx ↦ hx

def subProj : F →ₗ[𝓞 K] F.map X.proj := X.proj.restrict fun _ hx ↦ Submodule.mem_map_of_mem hx

theorem subIncl_injective : Function.Injective (X.subIncl F) := fun _ _ h ↦
  Subtype.ext (X.incl_injective (congrArg Subtype.val h))

theorem subProj_surjective : Function.Surjective (X.subProj F) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem subExact : Function.Exact (X.subIncl F) (X.subProj F) := by
  intro y
  constructor
  · intro hy
    have h0 : X.proj (y : E.carrier) = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := (X.exact (y : E.carrier)).mp h0
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change X.incl x ∈ F
    rw [hx]
    exact y.2
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (X.exact.apply_apply_eq_zero (x : E'.carrier))

theorem rank_sub_eq : E.rank F = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) :=
  finrank_eq_add_of_exact (X.subIncl_injective F) (X.subProj_surjective F) (X.subExact F)

theorem degree_submodule_le : E.degree F ≤ E'.degree (F.comap X.incl) + E''.degree (F.map X.proj) := by
  set F' := F.comap X.incl
  set F'' := F.map X.proj
  obtain ⟨s', hs'⟩ := HermitianBundle.exists_linearIndependent_rank E' F'
  obtain ⟨s'', hs''⟩ := HermitianBundle.exists_linearIndependent_rank E'' F''
  choose u hu using fun j ↦ X.subProj_surjective F (s'' j)
  have hw := linearIndependent_sumElim_of_exact (X.subIncl_injective F) (X.subExact F) hu hs' hs''
  have hcard : Fintype.card (Fin (E'.rank F') ⊕ Fin (E''.rank F'')) = E.rank F := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact (X.rank_sub_eq F).symm
  rw [E.degree_eq_of_linearIndependent F hw hcard,
    E'.degree_eq_of_linearIndependent F' hs' (Fintype.card_fin _),
    E''.degree_eq_of_linearIndependent F'' hs'' (Fintype.card_fin _),
    card_quotient_sumElim_of_exact (X.subIncl_injective F) (X.subProj_surjective F) (X.subExact F)
      hu hs'']
  have hfin' := finite_quotient_span hs' (by rw [Fintype.card_fin]; rfl)
  have hfin'' := finite_quotient_span hs'' (by rw [Fintype.card_fin]; rfl)
  have hc' : (0 : ℝ) < Nat.card (F' ⧸ Submodule.span (𝓞 K) (Set.range s')) := by
    exact_mod_cast Nat.card_pos
  have hc'' : (0 : ℝ) < Nat.card (F'' ⧸ Submodule.span (𝓞 K) (Set.range s'')) := by
    exact_mod_cast Nat.card_pos
  rw [Nat.cast_mul, Real.log_mul hc'.ne' hc''.ne']
  have hli' : LinearIndependent (𝓞 K) (fun k ↦ (s' k : E'.carrier)) :=
    hs'.map' F'.subtype (Submodule.ker_subtype _)
  have hli'' : LinearIndependent (𝓞 K) (fun j ↦ (s'' j : E''.carrier)) :=
    hs''.map' F''.subtype (Submodule.ker_subtype _)
  have hG : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ (fun k ↦ (s' k : E'.carrier))) +
      Real.log (gramDet E''.metric σ (fun j ↦ (s'' j : E''.carrier))) ≤
      Real.log (gramDet E.metric σ
        (fun k ↦ ((Sum.elim (fun k ↦ X.subIncl F (s' k)) u k : F) : E.carrier))) := by
    intro σ
    have h1 := gramDet_pos E'.metric σ hli'
    have h2 := gramDet_pos E''.metric σ hli''
    rw [← Real.log_mul h1.ne' h2.ne']
    refine Real.log_le_log (mul_pos h1 h2) ?_
    have hfam : (fun k ↦ ((Sum.elim (fun k ↦ X.subIncl F (s' k)) u k : F) : E.carrier)) =
        Sum.elim (fun k ↦ X.incl (s' k : E'.carrier)) (fun j ↦ (u j : E.carrier)) := by
      funext k
      rcases k with k | j <;> rfl
    have hsu : (fun j ↦ (s'' j : E''.carrier)) = fun j ↦ X.proj (u j : E.carrier) := by
      funext j
      rw [← hu j]
      rfl
    rw [hfam, hsu]
    exact X.gramDet_sumElim_ge σ _ _
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) ↦ hG σ)
  rw [Finset.sum_add_distrib] at hsum
  linarith

end HermitianExtension

end

end GroundTheory.Heights₂.Heights
