import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolumeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

variable {F : Type} [Field F] [NumberField F]

theorem singleV_apply_self' (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : (singleV F v s) v = s := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v s

theorem singleV_apply_ne' (v w : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (h : w ≠ v) :
    (singleV F v s) w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) s h

theorem singleV_mul_box (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) (b : Af F) :
    singleV F v s * b = singleV F v (s * b v) := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change (singleV F v s) w * b w = (singleV F v (s * b v)) w
  by_cases h : w = v
  · subst h
    rw [singleV_apply_self', singleV_apply_self']
  · rw [singleV_apply_ne' v w _ h, singleV_apply_ne' v w _ h, zero_mul]

open Classical in
theorem sum_singleV_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (c : Af F) (w : HeightOneSpectrum (𝓞 F)) :
    (∑ v ∈ T, singleV F v (c v)) w = if w ∈ T then c w else 0 := by
  classical
  have h1 : (∑ v ∈ T, singleV F v (c v)) w = ∑ v ∈ T, (singleV F v (c v)) w :=
    map_sum (evalV F w) _ T
  rw [h1]
  split_ifs with hw
  · rw [Finset.sum_eq_single w (fun v _ hv => singleV_apply_ne' v w _ (Ne.symm hv))
      (fun h => absurd hw h), singleV_apply_self']
  · exact Finset.sum_eq_zero fun v hv => singleV_apply_ne' v w _ (fun h => hw (h ▸ hv))

theorem singleV_mem_boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (hU : ∀ v, (0 : Fv F v) ∈ U v) (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v)
    (hS : v ∈ S → s ∈ U v) (hO : v ∉ S → s ∈ v.adicCompletionIntegers F) :
    singleV F v s ∈ Coef.boxA S U := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hS hw
    · rw [singleV_apply_ne' v w _ h]; exact hU w
  · by_cases h : w = v
    · subst h; rw [singleV_apply_self']; exact hO hw
    · rw [singleV_apply_ne' v w _ h]; exact zero_mem _

theorem annF_boxA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  intro F _ _ ψ hψ S hS U hU
  classical
  ext b
  constructor
  · intro hb
    have key : ∀ v (s : Fv F v), (v ∈ S → s ∈ U v) → (v ∉ S → s ∈ v.adicCompletionIntegers F) →
        psiV F ψ v (s * b v) = 1 := by
      intro v s h1 h2
      have := hb _ (singleV_mem_boxA S U hU v s h1 h2)
      rwa [singleV_mul_box, psiF_singleV] at this
    refine ⟨fun v hv s hs => key v s (fun _ => hs) (fun h => absurd hv h), fun v hv => ?_⟩
    have hmem : b v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) :=
      fun s hs => key v s (fun h => absurd h hv) (fun _ => hs)
    rw [hS v hv] at hmem
    exact hmem
  · rintro ⟨hb1, hb2⟩ y ⟨hy1, hy2⟩
    obtain ⟨T, hT⟩ := GlobalTheory.T.adelic_character_trivial_almost_everywhere F ψ hψ
    set c := y * b with hc
    have hcv : ∀ v, c v = y v * b v := fun v => rfl
    set T' := T ∪ S with hT'
    set e : Af F := ∑ v ∈ T', singleV F v (c v) with he
    have hcint : ∀ v, v ∉ S → c v ∈ v.adicCompletionIntegers F := fun v hv => by
      rw [hcv]; exact mul_mem (hy2 v hv) (hb2 v hv)
    have hd : psiF ψ (c - e) = 1 := by
      have happ : ∀ w, (c - e) w = c w - (if w ∈ T' then c w else 0) := fun w => by
        rw [← sum_singleV_apply T' c w]; rfl
      refine hT _ (fun w => ?_) (fun w hw => ?_)
      · rw [happ]
        split_ifs with h
        · rw [sub_self]; exact zero_mem _
        · rw [sub_zero]
          exact hcint w (fun hw => h (Finset.mem_union_right _ hw))
      · rw [happ, if_pos (Finset.mem_union_left _ hw), sub_self]
    have hsum : psiF ψ e = 1 := by
      rw [he]
      refine Finset.sum_induction _ (fun x => psiF ψ x = 1) (fun a b ha hb => by rw [psiF_add, ha, hb, one_mul])
        (psiF_zero ψ) (fun v _ => ?_)
      rw [psiF_singleV]
      by_cases hv : v ∈ S
      · rw [hcv]; exact hb1 v hv (y v) (hy1 v hv)
      · have h1 : c v ∈ annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) := by
          rw [hS v hv]; exact hcint v hv
        have := h1 1 (one_mem _)
        rwa [one_mul] at this
    have : c = (c - e) + e := by abel
    change psiF ψ c = 1
    rw [this, psiF_add, hd, hsum, one_mul]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
