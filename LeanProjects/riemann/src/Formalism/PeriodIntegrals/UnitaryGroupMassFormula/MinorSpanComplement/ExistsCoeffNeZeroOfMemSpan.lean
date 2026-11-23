import Mathlib

open MvPolynomial

noncomputable section

namespace PI.MSC

open scoped MonomialOrder

variable {σ R : Type*} [CommRing R]

theorem exists_coeff_ne_zero_of_mem_span (O : MonomialOrder σ) {ι : Type*}
    (c : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => O.degree (c i))
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) {g : MvPolynomial σ R}
    (hg : g ∈ Submodule.span R (Set.range c)) (hg0 : g ≠ 0) :
    ∃ i, g.coeff (O.degree (c i)) ≠ 0 := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hg0
    rw [Finsupp.support_eq_empty.mp h, Finsupp.sum_zero_index]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image f.support (fun j => O.toSyn (O.degree (c j))) hne
  refine ⟨i, ?_⟩
  have hlt : ∀ j ∈ f.support, j ≠ i → O.toSyn (O.degree (c j)) < O.toSyn (O.degree (c i)) := by
    intro j hj hji
    refine lt_of_le_of_ne (hmax j hj) ?_
    intro heq
    exact hji (hinj (O.toSyn.injective heq))
  rw [Finsupp.sum, MvPolynomial.coeff_sum, Finset.sum_eq_single i]
  · rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have h1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
    rw [h1, mul_one]
    exact Finsupp.mem_support_iff.mp hi
  · intro j hj hji
    rw [MvPolynomial.coeff_smul, MonomialOrder.coeff_eq_zero_of_lt (hlt j hj hji), smul_zero]
  · intro h
    exact absurd hi h

theorem monomial_mem_sup (O : MonomialOrder σ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) (e : σ →₀ ℕ) (a : R) :
    monomial e a ∈ Submodule.span R (Set.range c) ⊔
      restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
  classical
  haveI := O.wf
  have key : ∀ s : O.syn, ∀ e : σ →₀ ℕ, O.toSyn e = s → ∀ a : R,
      monomial e a ∈ Submodule.span R (Set.range c) ⊔
        restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by
    intro s
    induction s using WellFoundedLT.induction with
    | _ s ih =>
      intro e he a
      by_cases hmem : e ∈ Set.range fun i => O.degree (c i)
      · obtain ⟨i, rfl⟩ := hmem
        have hdecomp : monomial (O.degree (c i)) a =
            a • c i - a • (c i - monomial (O.degree (c i)) 1) := by
          rw [smul_sub, sub_sub_cancel, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hdecomp]
        refine Submodule.sub_mem _
          (Submodule.mem_sup_left (Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)))
          (Submodule.smul_mem _ a ?_)
        have hlc1 : (c i).coeff (O.degree (c i)) = 1 := hlc i
        set q := c i - monomial (O.degree (c i)) 1 with hq
        rw [MvPolynomial.as_sum q]
        refine Submodule.sum_mem _ fun d hd => ih (O.toSyn d) ?_ d rfl _
        rw [← he]
        have hd' : q.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
        have hne : d ≠ O.degree (c i) := by
          intro hdeq
          apply hd'
          rw [hdeq, hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hlc1, sub_self]
        have hci : (c i).coeff d ≠ 0 := by
          rw [hq, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne),
            sub_zero] at hd'
          exact hd'
        have hle := MonomialOrder.le_degree (m := O) (MvPolynomial.mem_support_iff.mpr hci)
        exact lt_of_le_of_ne hle (fun h => hne (O.toSyn.injective h))
      · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hmem))
  exact key _ e rfl a

theorem isCompl_map_rename (O : MonomialOrder σ) {τ : Type*} {φ : σ → τ}
    (hφ : Function.Injective φ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hinj : Function.Injective fun i => O.degree (c i)) (hlc : ∀ i, O.leadingCoeff (c i) = 1) :
    IsCompl (Submodule.map (rename φ).toLinearMap (Submodule.span R (Set.range c)))
      (restrictSupport R (Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i))ᶜ) := by
  classical
  have hmapinj : Function.Injective (Finsupp.mapDomain φ : (σ →₀ ℕ) → (τ →₀ ℕ)) :=
    Finsupp.mapDomain_injective hφ
  constructor
  · rw [Submodule.disjoint_def]
    intro g hg1 hg2
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hg1
    by_contra hne
    have hh0 : h ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    obtain ⟨i, hi⟩ := exists_coeff_ne_zero_of_mem_span O c hinj hlc hh hh0
    have hsupp := (MvPolynomial.mem_restrictSupport_iff R).mp hg2
    have hmem : Finsupp.mapDomain φ (O.degree (c i)) ∈ ((rename φ).toLinearMap h).support := by
      rw [MvPolynomial.mem_support_iff]
      show MvPolynomial.coeff (Finsupp.mapDomain φ (O.degree (c i))) (rename φ h) ≠ 0
      rw [MvPolynomial.coeff_rename_mapDomain φ hφ]
      exact hi
    exact hsupp (Finset.mem_coe.mpr hmem) ⟨O.degree (c i), ⟨i, rfl⟩, rfl⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro g _
    rw [MvPolynomial.as_sum g]
    refine Submodule.sum_mem _ fun d _ => ?_
    by_cases hd : d ∈ Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i)
    · obtain ⟨e, _, rfl⟩ := hd
      have h1 := monomial_mem_sup O c hlc e (g.coeff (Finsupp.mapDomain φ e))
      rw [← MvPolynomial.rename_monomial]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
      rw [← hyz, map_add]
      refine Submodule.add_mem_sup (Submodule.mem_map_of_mem hy) ?_
      rw [MvPolynomial.mem_restrictSupport_iff] at hz ⊢
      intro d' hd'
      have hd2 : d' ∈ (rename φ z).support := hd'
      rw [MvPolynomial.support_rename_of_injective hφ] at hd2
      obtain ⟨d'', hd'', rfl⟩ := Finset.mem_image.mp hd2
      rintro ⟨e', he', heq⟩
      exact hz (Finset.mem_coe.mpr hd'') (hmapinj heq ▸ he')
    · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hd))

end PI.MSC
