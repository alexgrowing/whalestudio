import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace PositivityTheory.RL.SeminormBoundRestriction

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_compact_open : ∃ U : Set (Af F), IsCompact U ∧ IsOpen U ∧ U.Nonempty := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have he := RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun _ => Valued.isOpen_valuationSubring _
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact ⟨_, isCompact_range he.continuous, he.isOpen_range, ⟨_, ⟨fun v => ⟨0, zero_mem _⟩, rfl⟩⟩⟩

theorem exists_SB : ∃ g ∈ SB (κ → Af F), ∃ y, g y = 1 := by
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨U, hc, ho, u, hu⟩ := exists_compact_open (F := F)
  let W : Set (κ → Af F) := Set.pi Set.univ fun _ => U
  have hWc : IsCompact W := isCompact_univ_pi fun _ => hc
  have hW : IsClopen W := ⟨hWc.isClosed, isOpen_set_pi Set.finite_univ fun _ _ => ho⟩
  refine ⟨W.indicator fun _ => (1 : ℂ), ⟨?_, ?_⟩, fun _ => u, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ W
    · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hW.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro hWc fun x hx => Set.indicator_of_notMem hx _
  · exact Set.indicator_of_mem (show (fun _ => u) ∈ W from fun _ _ => hu) _

def pt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

omit [Fintype κ] in
theorem pureA_pt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (pt a y) = f a * g y := by
  simp only [pureA, pt, RingEquiv.apply_symm_apply]

theorem slice_mem {Φ : (κ → AF F) → ℂ} (h : Φ ∈ schA F κ) (a : κ → mixedEmbedding.mixedSpace F) :
    (fun y => Φ (pt a y)) ∈ SB (κ → Af F) := by
  induction h using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    have : (fun y => pureA F f g (pt a y)) = f a • g := by
      funext y
      rw [pureA_pt]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul c Φ _ h₁ => exact Submodule.smul_mem _ c h₁

omit [Fintype κ] in
theorem at_iff (z : κ → AF F) : At (evI F) z ↔ ∀ i, (z i).2 = 0 := by
  constructor
  · intro h i
    have h1 := congrFun (h ((0 : Ainf F), (1 : Af F)) (map_zero _)) i
    have h2 := congrArg Prod.snd h1
    exact (one_mul (z i).2).symm.trans h2
  · intro h u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
    funext i
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      rw [h i, mul_zero]

theorem rest_of_SB (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    Rest (evI F) f (fun x => g fun i => (x i).2) := by
  refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  rw [at_iff] at hz
  refine congrArg g (funext fun i => ?_)
  show (x i).2 + (z i).2 = (x i).2
  rw [hz i, add_zero]

theorem exists_of_rest {f : SInf F κ} (hf : f ≠ 0) {r : (κ → AF F) → ℂ} (hr : Rest (evI F) f r) :
    ∃ g ∈ SB (κ → Af F), r = fun x => g fun i => (x i).2 := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (SchwartzMap.ext h)
  have key : ∀ x : κ → AF F, r x = r (pt a fun i => (x i).2) := by
    intro x
    have h := hr.1 (pt a fun i => (x i).2) (x - pt a fun i => (x i).2) ((at_iff _).2 fun i => sub_self (x i).2)
    rwa [add_sub_cancel] at h
  refine ⟨(f a)⁻¹ • fun y => tens (evI F) f r (pt a y), Submodule.smul_mem _ _ (slice_mem hr.2 a), funext fun x => ?_⟩
  rw [key x]
  simp only [tens, evI, pt, RingEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem eval_adm (x : κ → AF F) : (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (x i))).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  show f (fun i => evI F (x i)) * g (fun i => (x i).2) = g (fun i => (x i).2) * f (fun i => evI F (x i))
  exact mul_comm _ _

theorem eq_of_pureA {f₁ f₂ : SInf F κ} (h : ∀ g ∈ SB (κ → Af F), ∀ x, pureA F f₁ g x = pureA F f₂ g x) : f₁ = f₂ := by
  obtain ⟨g, hg, y, hy⟩ := exists_SB (F := F) (κ := κ)
  ext a
  have := h g hg (pt a y)
  rwa [pureA_pt, pureA_pt, hy, mul_one, mul_one] at this

theorem pureA_zero (g : (κ → Af F) → ℂ) : pureA F (0 : SInf F κ) g = 0 := by
  funext x
  exact zero_mul _

theorem tens_zero (r : (κ → AF F) → ℂ) : tens (evI F) (0 : SInf F κ) r = 0 := by
  funext x
  exact zero_mul _

end PositivityTheory.RL.SeminormBoundRestriction

namespace PositivityTheory.RL

open SeminormBoundRestriction

theorem actsLaws : GlobalTheory.RealLift.ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  refine ⟨fun T hT h r hr x => ?_, fun T hT h r hr => ?_, fun T h₁ h₂ => ?_, fun T h₁ h₂ => ?_, fun T h₁ h₂ => ?_⟩
  · by_cases hf : f = 0
    · subst hf
      have h1 : f₁ = 0 := by
        refine eq_of_pureA fun g hg y => ?_
        have h2 := h g hg _ (eval_adm y)
        simp only [pureA_zero, hT, map_zero] at h2
        rw [pureA_zero]
        exact h2.unique (hasDerivAt_const _ _)
      subst h1
      simp only [tens_zero, hT]
      exact hasDerivAt_const _ _
    · obtain ⟨g, hg, rfl⟩ := exists_of_rest hf hr
      exact h g hg _ (eval_adm x)
  · by_cases hf : f = 0
    · subst hf
      have h1 : f₁ = 0 := by
        refine eq_of_pureA fun g hg y => ?_
        have h2 := h g hg
        rw [pureA_zero, hT] at h2
        rw [pureA_zero, ← h2]
      subst h1
      rw [tens_zero, hT]
    · obtain ⟨g, hg, rfl⟩ := exists_of_rest hf hr
      exact h g hg
  · exact eq_of_pureA fun g hg x => (h₁ _ (rest_of_SB f hg) x).unique (h₂ _ (rest_of_SB f hg) x)
  · exact eq_of_pureA fun g hg x => congrFun ((h₁ _ (rest_of_SB f hg)).symm.trans (h₂ _ (rest_of_SB f hg))) x
  · exact eq_of_pureA fun g hg x => (h₁ g hg _ (eval_adm x)).unique (h₂ g hg _ (eval_adm x))

end PositivityTheory.RL

end
