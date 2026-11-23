import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.GlobalFields.Adele.WeakApprox
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.PlaceApprox

variable {F : Type} [Field F] [NumberField F]

open Classical in

def locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) : AF F :=
  ((fun u : InfinitePlace F => if h : u ∈ S₁ then p.2 ⟨u, h⟩ else 0 : InfiniteAdeleRing F),
    ∑ v : S₂, GlobalTheory.AdelicU.singleFin v.1 (p.1 v))

open Classical in
theorem continuous_locAdele (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (locAdele S₁ S₂) := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun u => ?_
    by_cases h : u ∈ S₁
    · simp only [h, dite_true]
      exact (continuous_apply _).comp continuous_snd
    · simp only [h, dite_false]
      exact continuous_const
  · exact continuous_finset_sum _ fun v _ =>
      (GlobalTheory.AdelicU.continuous_singleFin v.1).comp ((continuous_apply v).comp continuous_fst)

open Classical in
theorem locAdele_zero (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    locAdele S₁ S₂ 0 = 0 := by
  refine Prod.ext ?_ ?_
  · funext u
    change (if h : u ∈ S₁ then (0 : u.Completion) else 0) = 0
    split_ifs <;> rfl
  · simp [locAdele]
    rfl

open Classical in
theorem mul_eq_locAdele {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (hε : IsPlacesIdem S₁ S₂ ε) (a : AF F) :
    ε * a = locAdele S₁ S₂ ((fun v => evalV F v.1 (sndA F a)), (fun w => fstA F a w.1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  refine Prod.ext ?_ ?_
  · funext u
    change fstA F ε u * fstA F a u = _
    by_cases h : u ∈ S₁
    · simp only [locAdele, h, dite_true, h1 u h, one_mul]
    · simp only [locAdele, h, dite_false, h2 u h, zero_mul]
  · apply GlobalTheory.AdelicU.af_ext
    intro u
    change evalV F u (sndA F ε) * evalV F u (sndA F a) = _
    simp only [locAdele, map_sum]
    by_cases h : u ∈ S₂
    · rw [h3 u h, one_mul, Finset.sum_eq_single ⟨u, h⟩]
      · exact (GlobalTheory.AdelicU.evalV_singleFin_self u _).symm
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => hb (Subtype.ext e.symm)) _
      · intro hn; exact absurd (Finset.mem_univ _) hn
    · rw [h4 u h, zero_mul, Finset.sum_eq_zero]
      intro b _
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun e => h (by rw [e]; exact b.2)) _

theorem loc_sub_algebraMap (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (x : AF F) (t : F) :
    (((fun v : S₂ => evalV F v.1 (sndA F (x - algebraMap F (AF F) t))),
      (fun w : S₁ => fstA F (x - algebraMap F (AF F) t) w.1)) :
        ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion)) =
      ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) -
        ((fun v : S₂ => algebraMap F (v.1.adicCompletion F) t), (fun w : S₁ => algebraMap F w.1.Completion t)) := by
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · simp only [map_sub, AlgHom.commutes, Prod.fst_sub, Pi.sub_apply]
  · simp only [map_sub, AlgHom.commutes, Prod.snd_sub, Pi.sub_apply]
    rfl

theorem weak_approx_idem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 (0 : AF F) → ∃ t : F, ε * (x - algebraMap F (AF F) t) ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  set c : ((v : S₂) → Fv F v.1) × ((w : S₁) → w.1.Completion) :=
    ((fun v : S₂ => evalV F v.1 (sndA F x)), (fun w : S₁ => fstA F x w.1)) with hc
  have hO : {p | locAdele S₁ S₂ (c - p) ∈ U} ∈ 𝓝 c := by
    have hcont : Continuous fun p => locAdele S₁ S₂ (c - p) :=
      (continuous_locAdele S₁ S₂).comp (continuous_const.sub continuous_id)
    have h0 : locAdele S₁ S₂ (c - c) = 0 := by
      rw [sub_self, locAdele_zero]
    exact hcont.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  have hd := GroundTheory.Global.denseRange_algebraMap_prod_pi (K := F) S₂ S₁
  obtain ⟨_, hy, t, rfl⟩ := mem_closure_iff_nhds.1 (hd c) _ hO
  refine ⟨t, ?_⟩
  rw [mul_eq_locAdele hε, loc_sub_algebraMap]
  exact hy

end GlobalTheory.PlaceApprox
