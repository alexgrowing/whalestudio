import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvNonzero

theorem pure_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ) (hf : f ≠ 0)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ≠ 0 := by
  classical
  obtain ⟨yi, hyi⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  have hS : Set.Finite {v | ¬ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)} :=
    Filter.eventually_cofinite.mp hstd
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  set S := hS.toFinset with hSdef
  let yf : κ → FiniteAdeleRing (𝓞 F) F := fun i =>
    (⟨fun v => if v ∈ S then p v i else 0, by
      apply Filter.eventually_cofinite.mpr
      refine S.finite_toSet.subset ?_
      intro v hv
      by_contra hvS
      apply hv
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      show (if v ∈ S then p v i else 0) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [if_neg hvS']
      exact zero_mem (v.adicCompletionIntegers F)⟩ :
      RestrictedProduct (fun v : Pl F => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
  let x : κ → AdeleRing (𝓞 F) F := fun i =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i), yf i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  intro hz
  have hx := congrFun hz x
  have h1 : (fun i => evI F (x i)) = yi := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (yi i)) = yi i
    exact RingEquiv.apply_symm_apply _ _
  have h2 : ∀ v, (fun i => evFin F v (x i)) = fun i => if v ∈ S then p v i else 0 := fun v => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.zero_apply, h1, h2] at hx
  have hg : ∀ v, v ∉ S → φ v (fun i => if v ∈ S then p v i else 0) = 1 := by
    intro v hv
    have hv' : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      by_contra h
      exact hv (hS.mem_toFinset.mpr h)
    rw [hv']
    have hzero : (fun i : κ => if v ∈ S then p v i else 0) = fun _ => 0 := funext fun i => if_neg hv
    rw [hzero, Set.indicator_of_mem (show (fun _ : κ => (0 : Fv F v)) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hsub : Function.mulSupport (fun v => φ v (fun i => if v ∈ S then p v i else 0)) ⊆ S := by
    intro v hv
    by_contra h
    exact hv (hg v h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hx
  refine (mul_ne_zero hyi (Finset.prod_ne_zero_iff.mpr fun v hv => ?_)) hx
  have hpv : (fun i : κ => if v ∈ S then p v i else 0) = p v := funext fun i => if_pos hv
  rw [hpv]
  exact hp v

theorem exists_mem_schA_ev_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac, GlobalTheory.TensUniq.pure_mem_schA f M.vac (fun v => (hM.vac v).1) hM.std, ?_⟩
  rw [hpure f M.vac (fun v => (hM.vac v).1) (Filter.Eventually.of_forall fun _ => rfl)]
  have hv : (fun v => ev v (M.vac v)) = M₁.vac := funext fun v => (hev v).1
  rw [hv]
  exact pure_ne_zero (ei f) hf M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std

end GlobalTheory.EvNonzero

end
