import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Helpers

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

open Classical in

theorem weightedHomogeneousComponent_mul_form {x y : MRing ι R} {j : K → ℕ}
    (hy : IsMultiHomog y j) (n : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) n (x * y) =
      if j ≤ n then weightedHomogeneousComponent (blockWeight ι) (n - j) x * y else 0 := by
  let _ := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) n hy

theorem exists_component_not_mem {H : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ H) :
    ∃ e : K → ℕ, weightedHomogeneousComponent (blockWeight ι) e x ∉ H := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hx
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) (φ := x),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp x)]
  exact H.sum_mem fun e _ => h e

theorem exists_form_pair {P H : Ideal (MRing ι R)} [hP : P.IsPrime] [hH : H.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hgP : g ∉ P) (hu : u ∉ H)
    (hv : v ∉ H) (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ v' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    set v' := weightedHomogeneousComponent (blockWeight ι) (e + bf - bg) v
    refine ⟨u', v', e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, ?_, hc⟩
    intro hv'
    have h2 : g * (u * v' - u' * v) ∈ P := by
      have e2 : g * (u * v' - u' * v) = u' * (u * f - v * g) - u * (u' * f - v' * g) := by ring
      rw [e2]
      exact P.sub_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hc)
    have h3 : u * v' - u' * v ∈ H := hPH ((hP.mem_or_mem h2).resolve_left hgP)
    have h4 : u' * v ∈ H := by
      have h5 := H.sub_mem (H.mul_mem_left u hv') h3
      rwa [sub_sub_cancel] at h5
    exact (hH.mem_or_mem h4).elim he hv
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim

theorem exists_form_mem_not_mem {H H' : Ideal (MRing ι R)} (hH' : IsMultiHomogIdeal H')
    (h : ¬ H' ≤ H) : ∃ (x : MRing ι R) (e : K → ℕ), IsMultiHomog x e ∧ x ∈ H' ∧ x ∉ H := by
  obtain ⟨y, hy, hyH⟩ := Set.not_subset.mp h
  obtain ⟨e, he⟩ := exists_component_not_mem hyH
  exact ⟨_, e, weightedHomogeneousComponent_isWeightedHomogeneous _ _, hH' y hy e, he⟩

theorem exists_form_separator {H : Ideal (MRing ι R)} [hH : H.IsPrime]
    (S : Finset (Ideal (MRing ι R))) (hS : ∀ H' ∈ S, IsMultiHomogIdeal H' ∧ ¬ H' ≤ H) :
    ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ H ∧ ∀ H' ∈ S, a ∈ H' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, 0, isWeightedHomogeneous_one _ _, (Ideal.ne_top_iff_one H).mp hH.ne_top, by simp⟩
  | @insert H₀ S _ ih =>
    obtain ⟨a, A, ha, haH, haS⟩ := ih fun H' h => hS H' (Finset.mem_insert_of_mem h)
    have h₀ := hS H₀ (Finset.mem_insert_self _ _)
    obtain ⟨x, e, hx, hxH₀, hxH⟩ := exists_form_mem_not_mem h₀.1 h₀.2
    refine ⟨x * a, e + A, hx.mul ha, fun hm => (hH.mem_or_mem hm).elim hxH haH, ?_⟩
    intro H' hH'
    rcases Finset.mem_insert.mp hH' with rfl | h
    · exact Ideal.mul_mem_right _ _ hxH₀
    · exact Ideal.mul_mem_left _ _ (haS H' h)

theorem exists_form_not_mem_of_isRelevant [Fintype K] {H : Ideal (MRing ι R)} [hH : H.IsPrime]
    (hrel : IsRelevant H) (c : K → ℕ) : ∃ m : MRing ι R, IsMultiHomog m c ∧ m ∉ H := by
  choose i hi using hrel
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ c k) (fun k => c k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
    have hc : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hc] at hprod
    exact hprod
  · intro hm
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hi k (hH.mem_of_pow_mem _ hk)

omit [DecidableEq K] in

theorem divCycle_eq_of_sub_mem {P : Ideal (MRing ι R)} {x y : MRing ι R} (h : x - y ∈ P) :
    divCycle P x = divCycle P y := by
  have hI : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {y} := by
    have key : ∀ {x' y' : MRing ι R}, x' - y' ∈ P → P ⊔ Ideal.span {x'} ≤ P ⊔ Ideal.span {y'} := by
      intro x' y' h'
      refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e : x' = (x' - y') + y' := by ring
      rw [e]
      exact Submodule.add_mem_sup h' (Ideal.subset_span rfl)
    refine le_antisymm (key h) (key ?_)
    rw [← neg_sub]
    exact P.neg_mem h
  funext W
  unfold divCycle
  by_cases hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W
  · have hW' : W ∈ (P ⊔ Ideal.span {y}).minimalPrimes ∧ IsRelevant W := hI ▸ hW
    rw [dif_pos hW, dif_pos hW']
    simp only [hI]
  · have hW' : ¬ (W ∈ (P ⊔ Ideal.span {y}).minimalPrimes ∧ IsRelevant W) := hI ▸ hW
    rw [dif_neg hW, dif_neg hW']

end Helpers

section Main

theorem Representative.proof (h1 : DivCycleMul.Statement.{u}) : Representative.Statement.{u} := by
  intro O _ _ _ ϖ _ K _ _ ι _ P b f g hP hV T hT
  classical
  haveI := hP.isPrime
  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hV.degrees
  have claim : ∃ f₁ g₁ : MRing ι O, (∃ F E : K → ℕ, IsMultiHomog f₁ F ∧ IsMultiHomog g₁ E ∧
      (fun k => (F k : ℤ) - E k) = b) ∧ f₁ ∉ P ∧ g₁ ∉ P ∧ f₁ * g - g₁ * f ∈ P ∧
      ∀ H ∈ T, f₁ ∉ H ∧ g₁ ∉ H := by
    rcases T.eq_empty_or_nonempty with hTe | ⟨H₀, hH₀⟩
    · refine ⟨f, g, ⟨bf, bg, hbf, hbg, hb⟩, hV.num_not_mem, hV.den_not_mem, ?_, by simp [hTe]⟩
      rw [mul_comm, sub_self]
      exact P.zero_mem

    set T' := T.filter (fun H => ∀ H' ∈ T, H ≤ H' → H' = H) with hT'
    have hmax : ∀ H ∈ T, ∃ H' ∈ T', H ≤ H' := by
      intro H hH
      obtain ⟨H', hle, hm⟩ := T.exists_le_maximal hH
      exact ⟨H', Finset.mem_filter.mpr ⟨hm.1, fun H'' hH'' hle' => le_antisymm (hm.2 hH'' hle') hle'⟩,
        hle⟩
    obtain ⟨H₁, hH₁, -⟩ := hmax H₀ hH₀
    have hdata : ∀ H, ∃ (a u v : MRing ι O) (A e d : K → ℕ), H ∈ T' →
        (IsMultiHomog a A ∧ a ∉ H ∧ (∀ H' ∈ T', H' ≠ H → a ∈ H') ∧ IsMultiHomog u e ∧
          IsMultiHomog v d ∧ d + bg = e + bf ∧ u ∉ H ∧ v ∉ H ∧ u * f - v * g ∈ P) := by
      intro H
      by_cases hH : H ∈ T'
      · have hHT := (Finset.mem_filter.mp hH).1
        obtain ⟨hH1, hPH, hϖH, -⟩ := hT H hHT
        haveI := hH1.isPrime
        obtain ⟨u0, v0, hu0, hv0, h0⟩ :=
          hV.unit_off_special H hH1.isPrime hPH hH1.relevant hϖH
        obtain ⟨u, v, e, d, hu, hv, hde, huH, hvH, huv⟩ := exists_form_pair hP.multiHomog hPH hbf hbg
          hV.num_not_mem hV.den_not_mem hu0 hv0 h0
        obtain ⟨a, A, ha, haH, haS⟩ := exists_form_separator (H := H) (T'.erase H)
          (fun H' hH' => ⟨(hT H' (Finset.mem_filter.mp (Finset.mem_of_mem_erase hH')).1).1.multiHomog,
            fun hle => Finset.ne_of_mem_erase hH'
              ((Finset.mem_filter.mp (Finset.mem_of_mem_erase hH')).2 H hHT hle).symm⟩)
        exact ⟨a, u, v, A, e, d, fun _ => ⟨ha, haH,
          fun H' hH' hne => haS H' (Finset.mem_erase.mpr ⟨hne, hH'⟩), hu, hv, hde, huH, hvH, huv⟩⟩
      · exact ⟨0, 0, 0, 0, 0, 0, fun h => absurd h hH⟩
    choose a u v A e d hprop using hdata
    set E : K → ℕ := ∑ H ∈ T', (A H + e H) with hE
    have hmono : ∀ H, ∃ m : MRing ι O, H ∈ T' → IsMultiHomog m (E - (A H + e H)) ∧ m ∉ H := by
      intro H
      by_cases hH : H ∈ T'
      · obtain ⟨hH1, -⟩ := hT H (Finset.mem_filter.mp hH).1
        haveI := hH1.isPrime
        obtain ⟨m, hm⟩ := exists_form_not_mem_of_isRelevant hH1.relevant (E - (A H + e H))
        exact ⟨m, fun _ => hm⟩
      · exact ⟨0, fun h => absurd h hH⟩
    choose m hm using hmono
    have hle : ∀ H ∈ T', A H + e H ≤ E := fun H hH =>
      Finset.single_le_sum (f := fun H => A H + e H) (fun _ _ _ => Nat.zero_le _) hH
    set F : K → ℕ := A H₁ + (E - (A H₁ + e H₁)) + d H₁ with hF
    have hFeq : F + bg = E + bf := by
      obtain ⟨-, -, -, -, -, hde, -⟩ := hprop H₁ hH₁
      funext k
      have h1k := hle H₁ hH₁ k
      have h2k := congrFun hde k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k h2k ⊢
      simp only [hF, Pi.add_apply, Pi.sub_apply]
      omega
    have hdegv : ∀ H ∈ T', A H + (E - (A H + e H)) + d H = F := by
      intro H hH
      obtain ⟨-, -, -, -, -, hde, -⟩ := hprop H hH
      funext k
      have h1k := hle H hH k
      have h2k := congrFun hde k
      have h3k := congrFun hFeq k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k h2k h3k ⊢
      omega
    have hdegu : ∀ H ∈ T', A H + (E - (A H + e H)) + e H = E := by
      intro H hH
      funext k
      have h1k := hle H hH k
      simp only [Pi.add_apply, Pi.sub_apply] at h1k ⊢
      omega
    have hnot : ∀ H ∈ T', (∑ H' ∈ T', a H' * m H' * v H') ∉ H ∧
        (∑ H' ∈ T', a H' * m H' * u H') ∉ H := by
      intro H hH
      obtain ⟨hH1, -⟩ := hT H (Finset.mem_filter.mp hH).1
      have hp := hH1.isPrime
      obtain ⟨-, haH, -, -, -, -, huH, hvH, -⟩ := hprop H hH
      have hrest : ∀ w : Ideal (MRing ι O) → MRing ι O,
          (∑ H' ∈ T'.erase H, a H' * m H' * w H') ∈ H := fun w =>
        H.sum_mem fun H' hH' => H.mul_mem_right _ (H.mul_mem_right _
          ((hprop H' (Finset.mem_of_mem_erase hH')).2.2.1 H hH (Finset.ne_of_mem_erase hH').symm))
      have hone : ∀ w : Ideal (MRing ι O) → MRing ι O, w H ∉ H →
          (∑ H' ∈ T', a H' * m H' * w H') ∉ H := by
        intro w hw hmem
        rw [← Finset.add_sum_erase T' _ hH] at hmem
        have h' := (Submodule.add_mem_iff_left _ (hrest w)).mp hmem
        rcases hp.mem_or_mem h' with h'' | h''
        · rcases hp.mem_or_mem h'' with h''' | h'''
          · exact haH h'''
          · exact (hm H hH).2 h'''
        · exact hw h''
      exact ⟨hone v hvH, hone u huH⟩
    refine ⟨∑ H ∈ T', a H * m H * v H, ∑ H ∈ T', a H * m H * u H, ⟨F, E, ?_, ?_, ?_⟩,
      fun h' => (hnot H₁ hH₁).1 (((hT H₁ (Finset.mem_filter.mp hH₁).1).2.1) h'),
      fun h' => (hnot H₁ hH₁).2 (((hT H₁ (Finset.mem_filter.mp hH₁).1).2.1) h'), ?_, ?_⟩
    · refine IsWeightedHomogeneous.sum _ _ _ fun H hH => ?_
      obtain ⟨ha, -, -, -, hv, -⟩ := hprop H hH
      have h' := (ha.mul (hm H hH).1).mul hv
      rwa [hdegv H hH] at h'
    · refine IsWeightedHomogeneous.sum _ _ _ fun H hH => ?_
      obtain ⟨ha, -, -, hu, -⟩ := hprop H hH
      have h' := (ha.mul (hm H hH).1).mul hu
      rwa [hdegu H hH] at h'
    · rw [← hb]
      funext k
      have hk := congrFun hFeq k
      simp only [Pi.add_apply] at hk
      omega
    · rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine P.sum_mem fun H hH => ?_
      obtain ⟨-, -, -, -, -, -, -, -, huv⟩ := hprop H hH
      have e2 : a H * m H * v H * g - a H * m H * u H * f = -(a H * m H) * (u H * f - v H * g) := by
        ring
      rw [e2]
      exact P.mul_mem_left _ huv
    · intro H hH
      obtain ⟨H', hH', hle'⟩ := hmax H hH
      exact ⟨fun h' => (hnot H' hH').1 (hle' h'), fun h' => (hnot H' hH').2 (hle' h')⟩
  obtain ⟨f₁, g₁, hdeg, hf₁, hg₁, hmem, hT₁⟩ := claim
  have hunitP : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f₁ - v * g₁ ∈ P := by
    intro W hW hPW hrel hϖW
    obtain ⟨u, v, hu, hv, h⟩ := hV.unit_off_special W hW hPW hrel hϖW
    refine ⟨u, v, hu, hv, ?_⟩
    have e2 : g * (u * f₁ - v * g₁) = u * (f₁ * g - g₁ * f) + g₁ * (u * f - v * g) := by ring
    have h' : g * (u * f₁ - v * g₁) ∈ P := by
      rw [e2]
      exact P.add_mem (P.mul_mem_left _ hmem) (P.mul_mem_left _ h)
    exact (hP.isPrime.mem_or_mem h').resolve_left hV.den_not_mem
  refine ⟨f₁, g₁, IsVerticalDivisor.of_unit_off_special hdeg hf₁ hg₁ hunitP, ?_, fun H hH => ?_⟩
  · have hx := h1 O K ι P f₁ g hP.isPrime hf₁ hV.den_not_mem
    have hy := h1 O K ι P g₁ f hP.isPrime hg₁ hV.num_not_mem
    have hxy : divCycle P (f₁ * g) = divCycle P (g₁ * f) := divCycle_eq_of_sub_mem hmem
    funext W
    have h' := congrFun (hx.symm.trans (hxy.trans hy)) W
    simp only [Pi.add_apply] at h'
    unfold ratDiv
    linarith
  · obtain ⟨hH1, hPH, -, -⟩ := hT H hH
    exact IsVerticalDivisor.of_unit_off_special hdeg (hT₁ H hH).1 (hT₁ H hH).2
      fun W hW hHW hrel hϖW =>
        let ⟨u, v, hu, hv, h⟩ := hunitP W hW (hPH.trans hHW) hrel hϖW
        ⟨u, v, hu, hv, hPH h⟩

end Main

end

end GroundTheory.Heights₂.Heights.NumbersDVR
