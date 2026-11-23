import Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf

noncomputable section

namespace LateralTheory.E.LeafCoordsPf

open LateralTheory.E.LeafChartRingPf
open scoped Pointwise

theorem linIndep_of_span {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B) (g : B) {ι : Type} [Fintype ι]
    (v : ι → Ω[Localization.Away g⁄A]) (hcard : Fintype.card ι = n)
    (hsp : Submodule.span (Localization.Away g) (Set.range v) = ⊤) :
    LinearIndependent (Localization.Away g) v := by
  cases subsingleton_or_nontrivial (Localization.Away g) with
  | inl h => exact linearIndependent_of_subsingleton
  | inr h =>
    have h0 : Algebra.IsStandardSmoothOfRelativeDimension 0 B (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
    have h1 : Algebra.IsStandardSmoothOfRelativeDimension (0 + n) A (Localization.Away g) :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans n 0 A B (Localization.Away g)
    rw [zero_add] at h1
    have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := A) (S := Localization.Away g) n
    have : Module.Free (Localization.Away g) Ω[Localization.Away g⁄A] := by
      have := h1.isStandardSmooth
      infer_instance
    have hf : Module.finrank (Localization.Away g) Ω[Localization.Away g⁄A] = n :=
      Module.finrank_eq_of_rank_eq hr
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hsp.ge (hcard.trans hf.symm)

theorem conormal_retraction {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) :
    ∃ l, l ∘ₗ (KaehlerDifferential.kerCotangentToTensor A B (B ⧸ I)) = LinearMap.id := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  exact (Algebra.FormallySmooth.iff_split_injection (R := A) (P := B) (A := B ⧸ I)
    Ideal.Quotient.mk_surjective).mp inferInstance

def dyt {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (y : Fin e → B) (t : Fin d → B) :
    Fin e ⊕ Fin d → Ω[B⁄A] :=
  Sum.elim (fun k => KaehlerDifferential.D A B (y k)) (fun j => KaehlerDifferential.D A B (t j))

theorem ideal_fg {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B) (n m : ℕ)
    (hB : Algebra.IsStandardSmoothOfRelativeDimension n A B)
    (hBI : Algebra.IsStandardSmoothOfRelativeDimension m A (B ⧸ I)) : I.FG := by
  have := hB.isStandardSmooth
  have := hBI.isStandardSmooth
  have h := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I)
  simpa using h

theorem spread (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B)
    (P : Ideal B) (t : Fin d → B) (y : Fin e → B) (h : B) (hh : h ∉ P)
    (ht : ∀ j, t j ∈ I) (hI : h • I ≤ Ideal.span (Set.range t))
    (hΩ : h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t))) :
    ∃ g ∉ P,
    I.map (algebraMap B (Localization.Away g)) = Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) ∧
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤ := by
  have hu : IsUnit (algebraMap B (Localization.Away h) h) := IsLocalization.Away.algebraMap_isUnit h
  refine ⟨h, hh, ?_, ?_⟩
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h * x ∈ Ideal.span (Set.range t) := hI (Submodule.smul_mem_pointwise_smul x h I hx)
      have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.Away h)) h1
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (ht j)
  · set T := Localization.Away h
    set S := Submodule.span T (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A T (algebraMap B T (y k)))
      (fun j => KaehlerDifferential.D A T (algebraMap B T (t j)))))
    let f := KaehlerDifferential.map A A B T
    have hspan : Submodule.span B (Set.range (dyt (A := A) y t)) ≤ (S.restrictScalars B).comap f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rcases i with k | j
      · exact Submodule.subset_span ⟨Sum.inl k, by simp [dyt, f, KaehlerDifferential.map_D]⟩
      · exact Submodule.subset_span ⟨Sum.inr j, by simp [dyt, f, KaehlerDifferential.map_D]⟩
    rw [eq_top_iff]
    intro ω _
    obtain ⟨⟨m, u⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers h) f ω
    have huu : IsUnit (algebraMap B T (u : B)) := IsLocalization.map_units T u
    have hm : f (h • m) ∈ S := hspan (hΩ (Submodule.smul_mem_pointwise_smul m h ⊤ trivial))
    have key : (algebraMap B T h * algebraMap B T (u : B)) • IsLocalizedModule.mk' f m u = f (h • m) := by
      rw [mul_smul, algebraMap_smul, algebraMap_smul, LinearMap.map_smul]
      congr 1
      exact IsLocalizedModule.mk'_cancel' f m u
    rw [← key] at hm
    exact (Submodule.smul_mem_iff_of_isUnit S (hu.mul huu)).mp hm

def LeafNakH : Prop := ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (P : Ideal B), P.IsPrime →
  ∀ (N N' : Submodule B M), N'.FG → ∀ h ∉ P, h • N' ≤ N ⊔ P • N' → ∃ u ∉ P, u • N' ≤ N

def LeafCoordsPoint : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ h ∉ P, ∃ (t : Fin d → B) (y : Fin e → B),
    (∀ j, t j ∈ I) ∧ h • I ≤ Ideal.span (Set.range t) ⊔ P • I ∧
    h • (⊤ : Submodule B Ω[B⁄A]) ≤ Submodule.span B (Set.range (dyt (A := A) y t)) ⊔ P • ⊤

theorem LeafCoords_of (hPt : LeafCoordsPoint) (hN : LeafNakH) : LeafCoords := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨h, hh, t, y, ht, hI, hΩ⟩ := hPt d e A B I hB hBI P hP hIP
  obtain ⟨u1, hu1, h1⟩ := hN B B P hP _ I (ideal_fg I _ _ hB hBI) h hh hI
  have := hB.isStandardSmooth
  obtain ⟨u2, hu2, h2⟩ := hN B Ω[B⁄A] P hP _ ⊤ Module.Finite.fg_top h hh hΩ
  have hu : u1 * u2 ∉ P := fun H => (hP.mem_or_mem H).elim hu1 hu2
  obtain ⟨g, hg, hIg, hsp⟩ := spread d e A B I P t y (u1 * u2) hu ht
    (by
      rintro _ ⟨x, hx, rfl⟩
      have : u1 * x ∈ Ideal.span (Set.range t) := h1 (Submodule.smul_mem_pointwise_smul x u1 I hx)
      have := Ideal.mul_mem_left _ u2 this
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this)
    (by
      rintro _ ⟨x, -, rfl⟩
      have : u2 • x ∈ Submodule.span B (Set.range (dyt (A := A) y t)) :=
        h2 (Submodule.smul_mem_pointwise_smul x u2 ⊤ trivial)
      show (u1 * u2) • x ∈ _
      rw [mul_smul]
      exact Submodule.smul_mem _ u1 this)
  exact ⟨g, hg, t, y, hIg, linIndep_of_span (e + d) hB g _ (by simp) hsp, hsp⟩

end LateralTheory.E.LeafCoordsPf
