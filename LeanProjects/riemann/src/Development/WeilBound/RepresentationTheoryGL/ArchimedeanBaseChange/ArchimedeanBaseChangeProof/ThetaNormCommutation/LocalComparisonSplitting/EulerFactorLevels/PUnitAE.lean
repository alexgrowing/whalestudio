import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8.Fin

open PositivityTheory.Rg.BcB.G8

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem unitae_nrm (hU : Unr E) (n : ℕ) (w : Pl E) (δ : GL (Fin n) E) :
    nrmL n w (locEl n w δ) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
  by_cases hs : IsSplitAt w
  · unfold nrmL locEl
    rw [if_pos hs, if_pos hs]
  · unfold nrmL locEl
    rw [if_neg hs, if_neg hs]
    obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨hp, -⟩ := hns hs
    rw [map_mul, thE, GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) _ (cj w) (fun x => (hp x).symm)]

theorem unitae_single (hU : Unr E) (n : ℕ) (δ : GL (Fin n) E) (hsep : (polE δ).Separable) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w n ∧
      (∀ g : GLw n w, g⁻¹ * locEl n w δ * thL n w g ∈ GlobalTheory.LFun.KGL w n →
        ∃ t ∈ twCent (thL n w) (locEl n w δ), t⁻¹ * g ∈ GlobalTheory.LFun.KGL w n) ∧
      (∀ t ∈ twCent (thL n w) (locEl n w δ), IsCompact (closure (Subgroup.zpowers t : Set (GLw n w))) →
        t ∈ GlobalTheory.LFun.KGL w n) := by
  filter_upwards [GlobalTheory.EulerTwU.eventually_pc_ratF_mem δ, GlobalTheory.EulerTwU.eventually_pc_ratF_mem (δ * thE E n δ),
    GlobalTheory.BCT.SepBezout.bezout_eventually E _ hsep] with w h1 h2 h3
  rw [GlobalTheory.EulerTwU.pc_ratF] at h1 h2
  have hN := unitae_nrm hU n w δ
  have hbez : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w (locEl n w δ)).val.charpoly + v * derivative (nrmL n w (locEl n w δ)).val.charpoly = 1 := by
    have e : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ)).val.charpoly =
        (polE δ).map (algebraMap E (w.adicCompletion E)) := Matrix.charpoly_map _ _
    rw [hN, e]
    exact h3
  have hy : locEl n w δ ∈ GlobalTheory.LFun.KGL w n := by
    unfold locEl
    split_ifs
    · exact h2
    · exact h1
  have hNK : nrmL n w (locEl n w δ) ∈ GlobalTheory.LFun.KGL w n := by rw [hN]; exact h2
  refine ⟨hy, ?_, ?_⟩
  · intro g hg
    by_cases hs : IsSplitAt w
    · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hnr : nrmL n w (locEl n w δ) = locEl n w δ := by unfold nrmL; rw [if_pos hs]
      rw [hθ, MonoidHom.id_apply] at hg
      rw [hnr] at hbez
      obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.SplitUniq.splitUniq E n w _ g hy hbez hg
      refine ⟨t, ?_, ?_⟩
      · show t * locEl n w δ = locEl n w δ * thL n w t
        rw [hθ, MonoidHom.id_apply]
        exact ht
      · rw [hgk, inv_mul_cancel_left]
        exact hk
    · obtain ⟨t, ht, k, hk, hgk⟩ := GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs _ g hy hbez hg
      refine ⟨t, ht, ?_⟩
      rw [hgk, inv_mul_cancel_left]
      exact hk
  · intro t ht hc
    have ht' : t * locEl n w δ = locEl n w δ * thL n w t := ht
    have hcomm : t * nrmL n w (locEl n w δ) = nrmL n w (locEl n w δ) * t := by
      by_cases hs : IsSplitAt w
      · have hθ : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
        rw [hθ, MonoidHom.id_apply] at ht'
        unfold nrmL
        rw [if_pos hs]
        exact ht'
      · have hθ : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
        obtain ⟨-, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
        rw [hθ] at ht'
        have hth := GlobalTheory.ThetaPull.thetaGL_thetaGL (a := n) (cj w) hinv t
        unfold nrmL
        rw [if_neg hs]
        calc t * (locEl n w δ * thetaGL n (cj w) (locEl n w δ))
            = locEl n w δ * thetaGL n (cj w) t * thetaGL n (cj w) (locEl n w δ) := by rw [← mul_assoc, ht']
          _ = locEl n w δ * thetaGL n (cj w) (t * locEl n w δ) := by rw [map_mul, mul_assoc]
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ * thetaGL n (cj w) t) := by rw [ht']
          _ = locEl n w δ * thetaGL n (cj w) (locEl n w δ) * t := by rw [map_mul, hth, mul_assoc]
    exact GlobalTheory.StabInt.mem_KGL_of_commute E n w _ t hNK hbez hcomm hc

theorem unitae_cpt_fst {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set A)) := by
  have hK := h.image continuous_fst
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitae_cpt_snd {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (t : A × B) (h : IsCompact (closure (Subgroup.zpowers t : Set (A × B)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set B)) := by
  have hK := h.image continuous_snd
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem unitAE_holds : UnitAE := by
  intro E _ _ _ hU a b S _ δ₁ δ₂ h₁ h₂
  have hs₁ : (polE δ₁).Separable := by obtain ⟨-, -, h, -⟩ := h₁; exact h
  have hs₂ : (polE δ₂).Separable := by obtain ⟨-, -, h, -⟩ := h₂; exact h
  have hev := (unitae_single hU a δ₁ hs₁).and (unitae_single hU b δ₂ hs₂)
  filter_upwards [(Subtype.val_injective (p := (· ∈ S))).tendsto_cofinite.eventually hev] with w hw
  obtain ⟨⟨hy1, hc1, hk1⟩, ⟨hy2, hc2, hk2⟩⟩ := hw
  rintro y rfl
  refine ⟨Subgroup.mem_prod.2 ⟨hy1, hy2⟩, ?_, ?_⟩
  · rintro ⟨g1, g2⟩ hg
    have hg' := Subgroup.mem_prod.1 hg
    obtain ⟨t1, ht1, hk1'⟩ := hc1 g1 hg'.1
    obtain ⟨t2, ht2, hk2'⟩ := hc2 g2 hg'.2
    refine ⟨(t1, t2), ?_, Subgroup.mem_prod.2 ⟨hk1', hk2'⟩⟩
    have e1 : t1 * locEl a w.1 δ₁ = locEl a w.1 δ₁ * thL a w.1 t1 := ht1
    have e2 : t2 * locEl b w.1 δ₂ = locEl b w.1 δ₂ * thL b w.1 t2 := ht2
    show (t1, t2) * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
      (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) (t1, t2)
    exact Prod.ext e1 e2
  · refine (Subgroup.closure_le _).2 fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := ht
    have e : t * (locEl a w.1 δ₁, locEl b w.1 δ₂) =
        (locEl a w.1 δ₁, locEl b w.1 δ₂) * ((thL a w.1).prodMap (thL b w.1)) t := ht1
    have e1 : t.1 ∈ twCent (thL a w.1) (locEl a w.1 δ₁) := congrArg Prod.fst e
    have e2 : t.2 ∈ twCent (thL b w.1) (locEl b w.1 δ₂) := congrArg Prod.snd e
    exact Subgroup.mem_prod.2 ⟨hk1 _ e1 (unitae_cpt_fst t ht2), hk2 _ e2 (unitae_cpt_snd t ht2)⟩

end PositivityTheory.Rg.BcB.G8.Fin

end
