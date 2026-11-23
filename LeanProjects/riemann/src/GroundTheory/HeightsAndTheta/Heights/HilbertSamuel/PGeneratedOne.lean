import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GeneratedOne

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_one : IsMultiHomog (1 : MRingOver S ι) (fun _ => 0) := by
  intro m hm k
  have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, ι k) →₀ ℕ)) (a := (1 : S)) hm
  rw [Finset.mem_singleton] at h
  subst h
  simp

omit [Fintype K] in
open Classical in

theorem isMultiHomog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have h := MvPolynomial.support_monomial_subset (s := Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) (a := (1 : S)) hm
  rw [Finset.mem_singleton] at h
  subst h
  by_cases hk : k' = k
  · subst hk
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
    simp [hk]

open Classical in

theorem isMultiHomog_prodX (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver S ι))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact isMultiHomog_one
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_X k (c k)) ih
  have e : (∑ k, (Pi.single k 1 : K → ℕ)) = fun _ => 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

end GeneratedOne

theorem GeneratedOne.proof : GeneratedOne.Statement := by
  intro S _ K _ _ ι _ _ V I
  classical
  set M := MRingOver S ι ⧸ V
  choose c hc using I.2.1
  set t : MRingOver S ι := ∏ k, X ⟨k, c k⟩ with ht_def
  have ht : t ∈ KH.cellMon S I.1 :=
    Submonoid.prod_mem _ fun k _ => Submonoid.subset_closure ⟨k, c k, hc k, rfl⟩
  have htH : IsMultiHomog t (fun _ => 1) := GeneratedOne.isMultiHomog_prodX c
  have hres : ∀ F J : ∀ k, Finset (ι k), (∀ l, F l ⊆ J l) →
      KH.cellRes S M F J (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) =
        LocalizedModule.mk (Ideal.Quotient.mk V t) 1 := by
    intro F J hFJ
    have hle : KH.cellMon S F ≤ KH.cellMon S J := by
      apply Submonoid.closure_mono
      rintro f ⟨k, j, hj, rfl⟩
      exact ⟨k, j, hFJ k hj, rfl⟩
    unfold KH.cellRes
    rw [dif_pos hle, ← LocalizedModule.mkLinearMap_apply, IsLocalizedModule.liftOfLE_apply,
      LocalizedModule.mkLinearMap_apply]
  refine ⟨1, fun _ _ => LocalizedModule.mk (Ideal.Quotient.mk V t) 1,
    fun _ => LocalizedModule.mk (Ideal.Quotient.mk V 1) ⟨t, ht⟩, fun _ => ⟨?_, ?_⟩, fun _ => ?_, ?_⟩
  ·
    intro J _
    refine Submodule.subset_span ⟨Ideal.Quotient.mk V t, 1, fun _ => 0, ?_, ?_, rfl⟩
    · simpa using GeneratedOne.isMultiHomog_one (S := S) (ι := ι)
    · have e : ((fun _ : K => (1 : ℤ)) + fun k => (((fun _ : K => (0 : ℕ)) k : ℕ) : ℤ)) = fun _ => 1 := by
        funext k; simp
      rw [e]
      refine Submodule.subset_span ⟨t, ⟨fun _ => zero_le_one, ?_⟩, rfl⟩
      simpa using htH
  ·
    show _ ∈ (LinearMap.ker _).restrictScalars S
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
    funext J
    obtain ⟨J, hJne, hJ⟩ := J
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    have hle : (J k).card - 1 ≤ 1 := by
      have : (J k).card - 1 ≤ ∑ l, ((J l).card - 1) :=
        Finset.single_le_sum (f := fun l => (J l).card - 1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k)
      omega
    have hpos := (hJne k).card_pos

    have hface : ∀ x ∈ J k, ∀ y ∈ J k,
        ((∀ l, (Function.update J k ((J k).erase x) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase x) l).card - 1) = 0) →
        ((∀ l, (Function.update J k ((J k).erase y) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase y) l).card - 1) = 0) := by
      rintro x hx y hy ⟨h1, h2⟩
      have hcard : ∀ l, (Function.update J k ((J k).erase y) l).card =
          (Function.update J k ((J k).erase x) l).card := by
        intro l
        rcases eq_or_ne l k with rfl | hl
        · simp [Finset.card_erase_of_mem hx, Finset.card_erase_of_mem hy]
        · simp [Function.update_of_ne hl]
      refine ⟨fun l => Finset.card_pos.mp ?_, ?_⟩
      · rw [hcard]; exact Finset.card_pos.mpr (h1 l)
      · simp only [hcard]; exact h2
    rcases (show (J k).card = 1 ∨ (J k).card = 2 by omega) with h1 | h2
    · obtain ⟨a, hJk⟩ := Finset.card_eq_one.mp h1
      rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_singleton]
      erw [dif_neg]
      · rfl
      · rintro ⟨hne, -⟩
        have := hne k
        simp [hJk] at this
    · obtain ⟨a, b, hab, hJk⟩ : ∃ a b, a < b ∧ J k = {a, b} := by
        obtain ⟨x, y, hxy, hJk⟩ := Finset.card_eq_two.mp h2
        rcases lt_or_gt_of_ne hxy with h | h
        · exact ⟨x, y, h, hJk⟩
        · exact ⟨y, x, h, by rw [hJk, Finset.pair_comm]⟩
      have ha : a ∈ J k := by rw [hJk]; simp
      have hb : b ∈ J k := by rw [hJk]; simp
      rw [Finset.sum_congr hJk (fun _ _ => rfl), Finset.sum_pair hab.ne]
      by_cases hP : (∀ l, (Function.update J k ((J k).erase a) l).Nonempty) ∧
          ∑ l, ((Function.update J k ((J k).erase a) l).card - 1) = 0
      · erw [dif_pos hP, dif_pos (hface a ha b hb hP)]
        change KH.faceSign J k a • KH.cellRes S M (Function.update J k ((J k).erase a)) J
              (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) +
            KH.faceSign J k b • KH.cellRes S M (Function.update J k ((J k).erase b)) J
              (LocalizedModule.mk (Ideal.Quotient.mk V t) 1) = 0
        rw [hres _ _ (fun l => by
              rcases eq_or_ne l k with rfl | hl
              · simp [Finset.erase_subset]
              · simp [Function.update_of_ne hl]),
          hres _ _ (fun l => by
              rcases eq_or_ne l k with rfl | hl
              · simp [Finset.erase_subset]
              · simp [Function.update_of_ne hl])]
        have hsa : KH.faceSign J k a = (-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
          unfold KH.faceSign
          rw [hJk]
          simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
        have hsb : KH.faceSign J k b = -(-1) ^ (∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1)) := by
          unfold KH.faceSign
          rw [hJk]
          simp [Finset.filter_insert, Finset.filter_singleton, hab, pow_succ, pow_add]
        erw [hsa, hsb, neg_smul, add_neg_cancel]
      · have hP' := fun h => hP (hface b hb a ha h)
        erw [dif_neg hP, dif_neg hP']
        simp
  ·
    refine Submodule.subset_span ⟨Ideal.Quotient.mk V 1, ⟨t, ht⟩, fun _ => 1, htH, ?_, rfl⟩
    have e : (-(fun _ : K => (1 : ℤ)) + fun k => (((fun _ : K => (1 : ℕ)) k : ℕ) : ℤ)) = fun _ => 0 := by
      funext k; simp
    rw [e]
    refine Submodule.subset_span ⟨1, ⟨fun _ => le_refl 0, ?_⟩, map_one _⟩
    simpa using GeneratedOne.isMultiHomog_one (S := S) (ι := ι)
  ·
    rw [Fin.sum_univ_one, LocalizedModule.mk_mul_mk, OreLocalization.one_def]
    erw [LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp [Submonoid.smul_def, Algebra.smul_def]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
