import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_mem_eq_zero_of_factor {ι : Type} (f : ι → ℂ) (S : Set ι)
    (hfin : {w | f w ≠ 1}.Finite) {w₀ : ι} (hw₀ : w₀ ∈ S) (h0 : f w₀ = 0) :
    ∏ᶠ w ∈ S, f w = 0 := by
  have hs : (S ∩ Function.mulSupport f).Finite := hfin.subset fun w hw => hw.2
  rw [finprod_mem_eq_prod f hs]
  refine Finset.prod_eq_zero (i := w₀) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw₀, ?_⟩
  rw [Function.mem_mulSupport, h0]
  exact zero_ne_one

theorem finsum_finprod_local_sums_expand : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  intro ι S Cl _ D R _ loc O s good N hA hB hC hD hE
  classical
  haveI : ∀ w, Fintype (Cl w) := fun w => Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨T, hTfin, hTA⟩ : ∃ T : Set ι, T.Finite ∧ ∀ w, w ∉ T →
      ((∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) :=
    ⟨_, Filter.eventually_cofinite.1 hA, fun w hw => not_not.1 hw⟩
  have hO : ∀ w, w ∉ T → ∀ c, O w c = if good w c then 1 else 0 := fun w hw c => ((hTA w hw).2 c).1
  have hs1 : ∀ w, w ∉ T → ∀ c, good w c → ∀ d, s d w c = 1 := fun w hw c => ((hTA w hw).2 c).2
  have huniq : ∀ w, w ∉ T → ∀ c c', good w c → good w c' → c = c' :=
    fun w hw c c' hc hc' => (hTA w hw).1.unique hc hc'
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ w, w ∈ F ↔ w ∈ S ∧ w ∈ T :=
    ⟨hTfin.toFinset.filter (· ∈ S), fun w => by simp [and_comm]⟩
  obtain ⟨ext, ext_F, ext_good⟩ : ∃ ext : (∀ w : F, Cl w) → ∀ w, Cl w,
      (∀ x (w : F), ext x w = x w) ∧ ∀ x w, w ∉ T → good w (ext x w) := by
    refine ⟨fun x w => if h : w ∈ F then x ⟨w, h⟩ else if hw : w ∈ T then
      (hB w (fun hS => h ((hF w).2 ⟨hS, hw⟩))).some else (hTA w hw).1.exists.choose,
      fun x w => dif_pos w.2, fun x w hw => ?_⟩
    have hwF : w ∉ F := fun h => hw ((hF w).1 h).2
    simp only [dif_neg hwF, dif_neg hw]
    exact (hTA w hw).1.exists.choose_spec
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : R → ∀ w : F, Cl w, ∀ r (w : F), ρ r w = loc r w :=
    ⟨fun r w => loc r w, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set R, ∀ r, r ∈ G ↔ ∀ w ∈ S, w ∉ T → good w (loc r w) :=
    ⟨{r | ∀ w ∈ S, w ∉ T → good w (loc r w)}, fun _ => Iff.rfl⟩
  have prodS : ∀ φ : ι → ℂ, (∀ w ∈ S, w ∉ T → φ w = 1) → ∏ᶠ w ∈ S, φ w = ∏ w : F, φ w := by
    intro φ hφ
    have h1 : S ∩ Function.mulSupport φ ⊆ (F : Set ι) := by
      rintro w ⟨hwS, hw1⟩
      by_contra hwF
      exact hw1 (hφ w hwS fun hT => hwF (Finset.mem_coe.2 ((hF w).2 ⟨hwS, hT⟩)))
    have h2 : (F : Set ι) ⊆ S := fun w hw => ((hF w).1 (Finset.mem_coe.1 hw)).1
    rw [finprod_mem_eq_prod_of_subset φ h1 h2, ← Finset.prod_coe_sort]
  have hR : ∀ d, ∏ᶠ w ∈ S, ∑ᶠ c, s d w c * O w c =
      ∑ x : (∀ w : F, Cl w), (∏ w : F, s d w (x w)) * ∏ w : F, O w (x w) := by
    intro d
    rw [prodS]
    · simp only [finsum_eq_sum_of_fintype]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib
    · intro w _ hw
      obtain ⟨c0, hc0⟩ := (hTA w hw).1.exists
      rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single c0]
      · rw [hO w hw c0, if_pos hc0, hs1 w hw c0 hc0 d, mul_one]
      · intro c _ hc
        rw [hO w hw c, if_neg (fun hg => hc (huniq w hw c c0 hg hc0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c0) h
  have hs_ext : ∀ d x, ∏ᶠ w ∈ S, s d w (ext x w) = ∏ w : F, s d w (x w) := by
    intro d x
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [ext_F]
    · intro w _ hw
      exact hs1 w hw _ (ext_good x w hw) d
  have hEx : ∀ x, ∑ d, ∏ w : F, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = ext x w then N else 0 := by
    intro x
    rw [← hE (ext x) ?_, finsum_eq_sum_of_fintype]
    · exact Finset.sum_congr rfl fun d _ => (hs_ext d x).symm
    · exact Filter.eventually_cofinite.2 (hTfin.subset fun w hw => by_contra fun hwT => hw (ext_good x w hwT))
  have hρ : ∀ r ∈ G, ∀ w ∈ S, loc r w = ext (ρ r) w := by
    intro r hr w hwS
    by_cases hwF : w ∈ F
    · have h := ext_F (ρ r) ⟨w, hwF⟩
      rw [hρdef] at h
      exact h.symm
    · have hwT : w ∉ T := fun hT => hwF ((hF w).2 ⟨hwS, hT⟩)
      exact huniq w hwT _ _ ((hG r).1 hr w hwS hwT) (ext_good _ w hwT)
  have hρinj : Set.InjOn ρ G := by
    intro r hr r' hr' h
    apply hD
    intro w hwS
    rw [hρ r hr w hwS, hρ r' hr' w hwS, h]
  have hP0 : ∀ r, r ∉ G → ∏ᶠ w ∈ S, O w (loc r w) = 0 := by
    intro r hr
    rw [hG] at hr
    push_neg at hr
    obtain ⟨w, hwS, hwT, hg⟩ := hr
    refine finprod_mem_eq_zero_of_factor _ S ?_ hwS ?_
    · refine (hTfin.union (Filter.eventually_cofinite.1 (hC r))).subset fun v hv => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hv (by rw [hO v hcon.1, if_pos hcon.2])
    · rw [hO w hwT, if_neg hg]
  have hP1 : ∀ r ∈ G, ∏ᶠ w ∈ S, O w (loc r w) = ∏ w : F, O w (ρ r w) := by
    intro r hr
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [hρdef]
    · intro w hwS hwT
      rw [hO w hwT, if_pos ((hG r).1 hr w hwS hwT)]
  have hGfin : G.Finite := Set.Finite.of_finite_image (Set.toFinite _) hρinj
  have hmem : ∀ x, x ∈ ρ '' G ↔ ∃ r, ∀ w ∈ S, loc r w = ext x w := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hρ r hr⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · rw [hG]
        intro w hwS hwT
        rw [hr w hwS]
        exact ext_good x w hwT
      · funext w
        rw [hρdef, hr w ((hF w).1 w.2).1, ext_F]
  have hsum : ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) =
      ∑ x : (∀ w : F, Cl w), if ∃ r, ∀ w ∈ S, loc r w = ext x w then ∏ w : F, O w (x w) else 0 := by
    calc ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) = ∑ᶠ r ∈ G, ∏ w : F, O w (ρ r w) := by
          rw [finsum_mem_def]
          apply finsum_congr
          intro r
          by_cases hr : r ∈ G
          · simp only [Set.indicator_apply, hr, if_true]
            exact hP1 r hr
          · simp only [Set.indicator_apply, hr, if_false]
            exact hP0 r hr
      _ = ∑ᶠ x ∈ ρ '' G, ∏ w : F, O w (x w) :=
          (finsum_mem_image (f := fun x : (∀ w : F, Cl w) => ∏ w : F, O w (x w)) hρinj).symm
      _ = _ := by
          rw [finsum_mem_def, finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, hmem]
  refine ⟨hGfin.subset fun r hr => by_contra fun hrG => hr (hP0 r hrG), ?_⟩
  rw [hsum, finsum_congr hR, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, hEx x]
  split_ifs <;> ring

end GlobalTheory
