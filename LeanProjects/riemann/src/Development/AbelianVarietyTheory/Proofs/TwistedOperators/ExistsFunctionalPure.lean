import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp

noncomputable section

open NumberField IsDedekindDomain Filter

namespace GlobalTheory.FiniteAdelicPoints

theorem exists_functional {ι V : Type} [AddCommGroup V] [Module ℂ V] (p : ι → V) (a : ι → ℂ)
    (h : ∀ (s : Finset ι) (c : ι → ℂ), ∑ i ∈ s, c i • p i = 0 → ∑ i ∈ s, c i * a i = 0) :
    ∃ Λ : V →ₗ[ℂ] ℂ, ∀ i, Λ (p i) = a i := by
  classical

  let P : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ p
  let A : (ι →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ a

  have hk : LinearMap.ker P ≤ LinearMap.ker A := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have h0 : ∑ i ∈ c.support, c i • p i = 0 := by
      simpa [P, Finsupp.linearCombination_apply, Finsupp.sum] using hc
    simpa [A, Finsupp.linearCombination_apply, Finsupp.sum] using h c.support c h0

  let B : LinearMap.range P →ₗ[ℂ] ℂ :=
    ((LinearMap.ker P).liftQ A hk).comp (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℂ] _)
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend B
  refine ⟨Λ, fun i => ?_⟩
  have hp : P (Finsupp.single i 1) = p i := by simp [P]
  have hA : A (Finsupp.single i 1) = a i := by simp [A]
  calc Λ (p i) = Λ (P (Finsupp.single i 1)) := by rw [hp]
    _ = B ⟨P (Finsupp.single i 1), LinearMap.mem_range_self P _⟩ := by rw [← hΛ]; rfl
    _ = A (Finsupp.single i 1) := by
      simp only [B, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    _ = a i := hA

theorem sum_prod_apply {ι P : Type} {X : P → Type} [∀ v, Nonempty (X v)] (s : Finset ι) (φ : ι → ∀ v, X v → ℂ)
    (l : ∀ v, (X v → ℂ) →ₗ[ℂ] ℂ) (T : Finset P) :
    ∀ c : ι → ℂ, (∀ y : ∀ v, X v, ∑ i ∈ s, c i * ∏ v ∈ T, φ i v (y v) = 0) →
      ∑ i ∈ s, c i * ∏ v ∈ T, l v (φ i v) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro c hc
    simpa using hc (fun v => Classical.arbitrary (X v))
  | insert w T hw ih =>
    intro c hc

    have key : ∀ y : ∀ v, X v, ∑ i ∈ s, (c i * l w (φ i w)) * ∏ v ∈ T, φ i v (y v) = 0 := by
      intro y
      have hfun : (∑ i ∈ s, (c i * ∏ v ∈ T, φ i v (y v)) • φ i w) = 0 := by
        funext t
        have hupd : ∀ i, ∏ v ∈ T, φ i v (Function.update y w t v) = ∏ v ∈ T, φ i v (y v) := fun i =>
          Finset.prod_congr rfl fun v hv => by
            rw [Function.update_of_ne (fun h => hw (by rw [← h]; exact hv))]
        have h1 := hc (Function.update y w t)
        simp only [Finset.prod_insert hw, Function.update_self, hupd] at h1
        rw [Finset.sum_apply, Pi.zero_apply, ← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring

      have h2 := congrArg (l w) hfun
      rw [map_sum, map_zero] at h2
      simp only [map_smul, smul_eq_mul] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have h3 := ih (fun i => c i * l w (φ i w)) key
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.prod_insert hw]
    ring

variable {F : Type} [Field F] [NumberField F]

open Classical in

def finAd (T : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) :
    FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then y v else 0, by
    filter_upwards [T.eventually_cofinite_notMem] with v hv
    simp only [hv, if_false]
    exact zero_mem _⟩

def adPt {κ : Type} (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F :=
  fun k => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x k), finAd T fun v => y v k)

open Classical in

theorem pure_apply {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
    (hφ : ∀ v ∉ T, φ v 0 = 1) (x : κ → mixedEmbedding.mixedSpace F)
    (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ (adPt T x y) = f x * ∏ v ∈ T, φ v (y v) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure

  have h1 : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (adPt T x y i)) = x := by
    funext i
    simp [adPt, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]

  have h2 : ∀ v, (fun i => GlobalTheory.AdelicU.evFin F v (adPt T x y i)) =
      fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) := fun v => by
    funext i
    rfl
  rw [h1]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [h2 v]
    simp only [if_pos hv]
  · intro v hv
    by_contra hvT
    have hvT' : v ∉ T := by simpa using hvT
    have h0 : (fun i => if v ∈ T then y v i else (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) = 0 := by
      funext i
      simp [hvT']
    rw [Function.mem_mulSupport, h2 v, h0] at hv
    exact hv (hφ v hvT')

theorem exists_functional_pure {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)
    (hvac : ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) in Filter.cofinite, vac v =
      Set.indicator {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ (i : κ), x i ∈ HeightOneSpectrum.adicCompletionIntegers F v}
        (1 : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ))
    (lam : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ℂ)
    (l : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (hl : Set.Finite {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F | l v (vac v) ≠ 1}) :
    ∃ (Λ : ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) →ₗ[ℂ] ℂ),
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) in Filter.cofinite, φ v = vac v) →
        Λ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = lam f * ∏ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), l v (φ v) := by
  classical

  obtain ⟨Λ, hΛ⟩ := exists_functional
    (ι := {q : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ × ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) //
      ∀ᶠ v in Filter.cofinite, q.2 v = vac v})
    (fun q => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure q.1.1 q.1.2) (fun q => lam q.1.1 * ∏ᶠ v, l v (q.1.2 v)) (by
    intro s c hc

    have f1 := Filter.eventually_cofinite.1 hvac
    have f2 := s.finite_toSet.biUnion fun q _ => Filter.eventually_cofinite.1 q.2
    let T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := ((hl.union f1).union f2).toFinset
    have hout : ∀ v ∉ T, l v (vac v) = 1 ∧ (∀ q ∈ s, q.1.2 v = vac v) ∧ vac v 0 = 1 := by
      intro v hv
      simp only [T, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe,
        not_or, not_exists, not_not, ne_eq] at hv
      obtain ⟨⟨hv0, hv1⟩, hv2⟩ := hv
      refine ⟨hv0, fun q hq => hv2 q hq, ?_⟩
      rw [hv1]
      have hz : (0 : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈
          {x : κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | ∀ i, x i ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
        fun i => zero_mem _
      rw [Set.indicator_of_mem hz, Pi.one_apply]

    have hrel : ∀ (x : κ → mixedEmbedding.mixedSpace F) (y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v),
        ∑ q ∈ s, c q * (q.1.1 x * ∏ v ∈ T, q.1.2 v (y v)) = 0 := by
      intro x y
      have h0 := congrFun hc (adPt T x y)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [pure_apply q.1.1 q.1.2 T (fun v hv => by rw [(hout v hv).2.1 q hq, (hout v hv).2.2]) x y]

    have hrel2 : ∀ y : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v,
        ∑ q ∈ s, (c q * lam q.1.1) * ∏ v ∈ T, q.1.2 v (y v) = 0 := by
      intro y
      have hz : ∑ q ∈ s, (c q * ∏ v ∈ T, q.1.2 v (y v)) • q.1.1 = 0 := by
        ext x
        simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply]
        rw [← hrel x y]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      have h0 := congrArg lam hz
      rw [map_sum, map_zero] at h0
      simp only [map_smul, smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring

    have h3 := sum_prod_apply s (fun q v => q.1.2 v) l T (fun q => c q * lam q.1.1) hrel2
    rw [← h3]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · ring
    · intro v hv
      by_contra hvT
      rw [Function.mem_mulSupport, (hout v (by simpa using hvT)).2.1 q hq] at hv
      exact hv (hout v (by simpa using hvT)).1)
  exact ⟨Λ, fun f φ hφ => hΛ ⟨(f, φ), hφ⟩⟩

end GlobalTheory.FiniteAdelicPoints

end
