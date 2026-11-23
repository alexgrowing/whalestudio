import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbitDecomp

open GlobalTheory.HeisSchA GlobalTheory.DiffDecay GlobalTheory.XTermDecay

theorem continuous_of_weak {T : Type} [TopologicalSpace T] [CompactSpace T] {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : T → SchwartzMap V ℂ)
    (h : ∀ l : SchwartzMap V ℂ →L[ℂ] ℂ, Continuous fun t => l (f t)) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun t₀ =>
    GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded f t₀ (fun v => ?_) fun k n => ?_
  · exact (h ((BoundedContinuousFunction.evalCLM ℂ v).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ))).continuousAt
  · obtain ⟨C, hC⟩ := bounded_of_weak f (fun l => by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (h l).continuousOn
      exact ⟨C, fun t => hC t trivial⟩) (SchwartzMap.seminorm ℂ k n)
      ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, n))
    exact ⟨C, Eventually.of_forall fun t v => (SchwartzMap.le_seminorm ℂ k n (f t) v).trans (hC t)⟩

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_decomp_continuous {T : Type} [TopologicalSpace T] [CompactSpace T] (Ψ : T → (κ → AF F) → ℂ)
    (hΨ : ∀ t, Ψ t ∈ schA F κ) (hc : ∀ l ∈ (adeleClass F).adm κ, Continuous fun t => l (Ψ t)) :
    ∃ (m : ℕ) (g : Fin m → (κ → Af F) → ℂ) (f : Fin m → T → SInf F κ), (∀ j, g j ∈ SB _) ∧
      (∀ t, Ψ t = ∑ j, pureA F (f j t) (g j)) ∧ ∀ j, Continuous (f j) := by
  have hb : ∀ l ∈ (adeleClass F).adm κ, ∃ C : ℝ, ∀ t, ‖l (Ψ t)‖ ≤ C := fun l hl => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hc l hl).continuousOn
    exact ⟨C, fun t => hC t trivial⟩
  obtain ⟨W, hW, hsl⟩ := GlobalTheory.T.schwartz_family_finite_dim_span F κ T Ψ hΨ hb
  let W' : Submodule ℂ ((κ → Af F) → ℂ) := W ⊓ SB _
  haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_left
  let b := Module.finBasis ℂ W'
  choose β hβ using fun j => LinearMap.exists_extend (b.coord j)
  obtain ⟨r, hr⟩ := (coeL (F := F) (κ := κ)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 DFunLike.coe_injective)
  have hr' : ∀ f, r (coeL f) = f := fun f => LinearMap.congr_fun hr f
  refine ⟨_, fun j => b j, fun j t => r (coefFun (β j) (Ψ t)), fun j => (b j).2.2, fun t => ?_, fun j => ?_⟩
  · funext x
    let y : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1
    let s : W' := ⟨_, hsl t _, slice_mem_SB y _ (hΨ t)⟩
    have h1 := congrFun (congrArg Subtype.val (b.sum_repr s)) fun i => (x i).2
    have h2 : ∀ j, r (coefFun (β j) (Ψ t)) y = b.repr s j := fun j => by
      obtain ⟨f, hf⟩ := coefFun_mem (β j) _ (hΨ t)
      rw [← hf, hr']
      exact (congrFun hf y).trans (LinearMap.congr_fun (hβ j) s)
    have h3 : (s : (κ → Af F) → ℂ) (fun i => (x i).2) = Ψ t x := by
      simp only [s, y, RingEquiv.symm_apply_apply]
      rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [Finset.sum_apply]
    refine (h1.trans h3).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← h2 j]
    rfl
  · refine continuous_of_weak _ fun l =>
      hc (l.toLinearMap ∘ₗ r ∘ₗ coefFun (β j)) fun g _ => ⟨β j g • l, fun f => ?_⟩
    simp only [LinearMap.comp_apply, coefFun_pureA, hr', map_smul]
    rfl

theorem exists_orbit_decomp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ K : Subgroup (UA σ G.V.J), IsStab B K →
    ∀ Ψ ∈ schA F (Fin a × Fin (a + a')),
      ∃ (n : ℕ) (g : Fin n → (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ) (S : Set (SInf F (Fin a × Fin (a + a'))))
        (f : K → Fin n → SInf F (Fin a × Fin (a + a'))), (∀ i, g i ∈ SB (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F)) ∧
        IsCompact S ∧ (∀ k i, f k i ∈ S) ∧ ∀ k : K, om (k.1, 1) Ψ = ∑ i, pureA F (f k i) (g i) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT K hK Ψ hΨ
  obtain ⟨K', -, -, hK', hKc, -⟩ := GlobalTheory.StabHaar.stabEx hKP.base F E σ B a G.V _ _ hT.base hT.geo.hV
  have hKK : K' = K := Subgroup.ext fun g => (hK' g).trans (hK g).symm
  subst hKK
  haveI : CompactSpace K' := isCompact_iff_compactSpace.1 hKc
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hT.weil
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp_continuous (fun k : K' => om (k.1, 1) Ψ)
    (fun k => hw.isUSplitting.pres (k.1, 1) Ψ hΨ) fun l hl =>
      (hw.2.2 l hl Ψ hΨ).comp (continuous_subtype_val.prodMk continuous_const)
  exact ⟨m, g, ⋃ j, Set.range (f j), fun k j => f j k, hg, isCompact_iUnion fun j => isCompact_range (hf j),
    fun k j => Set.mem_iUnion.2 ⟨j, k, rfl⟩, hdec⟩

end GlobalTheory.OrbitDecomp

end
