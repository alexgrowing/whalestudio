import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Avoid

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_avoid_primes (S : Finset (Ideal (MRing ι R)))
    (hS : ∀ W ∈ S, W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W) (e₀ : K → ℕ) :
    ∃ (e : K → ℕ) (h : MRing ι R), IsMultiHomog h e ∧ e₀ ≤ e ∧ ∀ W ∈ S, h ∉ W := by
  classical
  set T := S.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := (S.finite_toSet).exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hW'.prop, fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hsep : ∀ W ∈ T, ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ W ∧
      ∀ W' ∈ T.erase W, a ∈ W' := by
    intro W hW
    have := (hS W (hTS W hW)).1
    refine exists_form_separator (T.erase W) fun W' hW' => ⟨(hS W' (hTS W' (Finset.mem_of_mem_erase hW'))).2.1,
      fun hle' => Finset.ne_of_mem_erase hW' ?_⟩
    exact (hTmax W' (Finset.mem_of_mem_erase hW') W (hTS W hW) hle').symm
  choose! a A haH haW haMem using hsep
  set e : K → ℕ := e₀ + ∑ W ∈ T, A W with he
  have hAe : ∀ W ∈ T, A W ≤ e := fun W hW =>
    le_add_left (Finset.single_le_sum (f := A) (fun _ _ => fun _ => Nat.zero_le _) hW)
  have hmon : ∀ W ∈ T, ∃ m : MRing ι R, IsMultiHomog m (e - A W) ∧ m ∉ W := by
    intro W hW
    have := (hS W (hTS W hW)).1
    exact exists_form_not_mem_of_isRelevant (hS W (hTS W hW)).2.2 _
  choose! m hmH hmW using hmon
  refine ⟨e, ∑ W ∈ T, a W * m W, ?_, le_self_add, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun W hW => ?_
    have := (haH W hW).mul (hmH W hW)
    rwa [add_tsub_cancel_of_le (hAe W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ hmem
      have hp := (hS W₀ (hTS W₀ hW₀)).1
      rw [← Finset.add_sum_erase _ _ hW₀] at hmem
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _ (haMem W (Finset.mem_of_mem_erase hW) W₀
          (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hW).symm, hW₀⟩))
      rcases hp.mem_or_mem ((Ideal.add_mem_iff_left _ hrest).mp hmem) with h2 | h2
      · exact haW W₀ hW₀ h2
      · exact hmW W₀ hW₀ h2
    intro W hW hmem
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' hmem)

end Avoid

theorem mem_minimalPrimes_sup_span_of_mem {A : Type*} [CommRing A] [IsNoetherianRing A] {P H : Ideal A}
    [hP : P.IsPrime] {x y : A} (hH : H ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hy : y ∉ P)
    (hyH : y ∈ H) : H ∈ (P ⊔ Ideal.span {y}).minimalPrimes := by
  have : H.IsPrime := hH.1.1
  have hPH : P ≤ H := le_sup_left.trans hH.1.2
  obtain ⟨Q, hQ, hQH⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPH ((Ideal.span_singleton_le_iff_mem _).mpr hyH))
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hyQ : y ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  suffices hQH' : Q = H by rw [← hQH']; exact hQ
  by_contra hne
  have hlt : Q < H := lt_of_le_of_ne hQH hne
  let φ := Ideal.Quotient.mk P
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hHm : (H.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hQm : (Q.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ (by rwa [Ideal.mk_ker])
  have hcomap : ∀ I : Ideal A, P ≤ I → (I.map φ).comap φ = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI]
  have h_lt : Q.map φ < H.map φ := (Ideal.map_mono hlt.le).lt_of_not_ge fun h => hlt.not_ge (by
    simpa only [hcomap Q hPQ, hcomap H hPH] using Ideal.comap_mono (f := φ) h)
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hH
  have : (H.map φ).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h0' : Q.map φ ∈ (⊥ : Ideal (A ⧸ P)).minimalPrimes := h0
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at h0'
  have : φ y ∈ Q.map φ := Ideal.mem_map_of_mem φ hyQ
  rw [show Q.map φ = ⊥ from h0', Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact hy this

theorem relevant_minimal_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : divCycle P x W ≠ 0) :
    W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW
  · exact absurd rfl h

theorem AvoidingFormExists.proof : AvoidingFormExists.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD e₀
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hD1 := hD.1
  obtain ⟨bf, bg, hf, hg, -⟩ := hD1.degrees

  have hfin : ∀ x : MRing ι O, {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W}.Finite :=
    fun x => (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun W hW => hW.1
  have hmin : ∀ (x : MRing ι O) (c : K → ℕ), IsMultiHomog x c →
      ∀ W ∈ {W | W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W},
        W.IsPrime ∧ IsMultiHomogIdeal W ∧ IsRelevant W := fun x c hx W hW =>
    ⟨hW.1.1.1, MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hx) hW.1, hW.2⟩
  obtain ⟨e, h, hh, he, hS⟩ := exists_form_avoid_primes
    (insert P ((hfin f).toFinset ∪ (hfin g).toFinset)) (by
      intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hPp, hP.multiProj.multiHomog, hP.multiProj.relevant⟩
      rcases Finset.mem_union.mp hW with hW | hW
      · exact hmin f bf hf W ((hfin f).mem_toFinset.mp hW)
      · exact hmin g bg hg W ((hfin g).mem_toFinset.mp hW)) e₀
  have hhP : h ∉ P := hS P (Finset.mem_insert_self _ _)
  have hhf : ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((hfin f).mem_toFinset.mpr ⟨hW, hr⟩)))
  have hhg : ∀ W ∈ (P ⊔ Ideal.span {g}).minimalPrimes, IsRelevant W → h ∉ W := fun W hW hr =>
    hS W (Finset.mem_insert_of_mem (Finset.mem_union_right _ ((hfin g).mem_toFinset.mpr ⟨hW, hr⟩)))

  have hG : ∀ G, ratDiv P f g G ≠ 0 → divCycle P h G = 0 := by
    intro G hG
    by_contra hhG
    have hhG' : h ∈ G := (relevant_minimal_of_divCycle_ne_zero hhG).1.1.2
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    by_cases hfG : divCycle P f G = 0
    · have hgG : divCycle P g G ≠ 0 := fun h0 => hG (by unfold ratDiv; rw [hfG, h0, sub_zero])
      obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hgG
      exact hhg G hm hr hhG'
    · obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hfG
      exact hhf G hm hr hhG'
  have hterm : ∀ s : MRing ι O, ∀ G, ratDiv P f g G ≠ 0 →
      divCycle P (s * h) G = divCycle P s G ∨ s ∈ P := by
    intro s G hr
    by_cases hsP : s ∈ P
    · exact Or.inr hsP
    · left
      rw [DivCycleMul.proof O K ι P s h hPp hsP hhP, Pi.add_apply, hG G hr, add_zero]
  refine ⟨e, h, hh, hhP, he, ?_, fun G _ hr => hG G hr, ?_, ?_⟩
  ·
    intro H hH _
    obtain ⟨hm, hr⟩ := relevant_minimal_of_divCycle_ne_zero hH
    have : H.IsPrime := hm.1.1
    have hPH : P ≤ H := le_sup_left.trans hm.1.2
    have hhH : h ∈ H := hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))
    refine IsVerticalDivisor.of_unit_off_special hD1.degrees
      (fun hfH => hhf H (mem_minimalPrimes_sup_span_of_mem hm hD1.num_not_mem hfH) hr hhH)
      (fun hgH => hhg H (mem_minimalPrimes_sup_span_of_mem hm hD1.den_not_mem hgH) hr hhH) ?_
    intro W hW hHW hrW hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD1.unit_off_special W hW (hPH.trans hHW) hrW hϖW
    exact ⟨u, v, hu, hv, hPH huv⟩
  ·
    refine Nat.le_zero.mp (ciSup_le' fun G => ?_)
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · simp [hG G.1 hr]
  ·
    intro s hsP
    unfold commonExcess
    congr 1
    funext G
    by_cases hr : ratDiv P f g G.1 = 0
    · simp [hr]
    · rcases hterm s G.1 hr with h1 | h1
      · rw [h1]
      · exact absurd h1 hsP

end GroundTheory.Heights₂.Heights.NumbersDVR
