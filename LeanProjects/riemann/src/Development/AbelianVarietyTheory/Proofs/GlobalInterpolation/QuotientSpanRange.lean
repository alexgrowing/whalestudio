import Mathlib

open IsLocalRing Matrix

namespace GlobalTheory.RegularQuotient

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.quot_regular (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal Λ := by
    rw [Ideal.span_le, ← hs]
    exact (Set.subset_union_right).trans Ideal.subset_span
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm
  haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I) := by
    have hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) =
      maximalIdeal (Λ ⧸ I) := by
    rw [← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ) := by
    rw [← hspan]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (t i))
    have h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen
  have hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ) := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)
    have h' : (Set.range z).ncard ≤ Fintype.card κ := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
  rw [hd] at hge
  have h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ) :=
    hge.trans (add_le_add le_rfl hI)
  have hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ) := by
    generalize ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))
      | coe n =>
        norm_cast at h1 hle ⊢
        omega
  exact ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan,
    hdim⟩

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.exists_extend (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by
  set N : Submodule (ResidueField Λ) (CotangentSpace Λ) :=
    Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i))
    with hN
  let b := Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)
  have hsurj : Function.Surjective
      fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y) :=
    (Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective
  choose s hs using fun j => hsurj (b j)
  refine ⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance,
    fun j => (s j : Λ), ?_, ?_⟩
  · have htop : Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤ := by
      set P := Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))
      have hNP : N ≤ P := by
        rw [hN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩
      have hmap : Submodule.map N.mkQ P = ⊤ := by
        rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩
      rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP] at hmap
      exact hmap
    rw [IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
    have key := congrArg (Submodule.map (maximalIdeal Λ).subtype) htop
    rw [← Submodule.span_image, Submodule.map_subtype_top, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at key
    exact key
  · rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin,
      ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]

open IsLocalRing Matrix in
private theorem linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq (A : Type) [CommRing A]
    [IsRegularLocalRing A] (k : ℕ) (x : Fin k → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hind : ∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i => (maximalIdeal A).toCotangent (⟨x i, hx i⟩ : maximalIdeal A)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => IsLocalRing.residue_surjective (g j)
  have hmem : (∑ j, a j * x j) ∈ maximalIdeal A :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
  have hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]
    have he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) =
        ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A) := by
      ext; simp [Submodule.coe_sum, smul_eq_mul]
    rw [he, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  rw [← ha i, IsLocalRing.residue_eq_zero_iff]
  exact hind a hsum i

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.quotient_span_range : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by
  intro A _ _ d k x hd hx hind
  obtain ⟨J, _, t, hspan, hdim⟩ := _root_.GlobalTheory.RegularQuotient.exists_extend A
    (fun i => (⟨x i, hx i⟩ : maximalIdeal A))
    (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)
  have hJ : Fintype.card J = d := by
    rw [hd, Fintype.card_fin] at hdim
    have h : d + k = Fintype.card J + k := by exact_mod_cast hdim
    omega
  have hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A := hspan
  have hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ) := by
    rw [hd, Fintype.card_fin, hJ]
  obtain ⟨hreg, -, -, hq⟩ := _root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'
  exact ⟨hreg, by rw [hq, hJ]⟩

end GlobalTheory.RegularQuotient
