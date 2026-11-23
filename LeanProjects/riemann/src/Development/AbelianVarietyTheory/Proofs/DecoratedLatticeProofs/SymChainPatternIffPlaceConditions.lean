import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedLevelPatternToFramePlaces

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.PatResidue

theorem zPos_lt {κ τ l j : ℕ} (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) : zPos a < κ + l + j * τ := by
  rcases a with (i | i) | ⟨s, u⟩
  · have := i.isLt
    simp only [zPos]
    omega
  · have := i.isLt
    simp only [zPos]
    omega
  · have hs := s.isLt
    have hu := u.isLt
    have h2 : ((s : ℕ) + 1) * τ ≤ j * τ := Nat.mul_le_mul_right _ hs
    rw [Nat.add_mul, one_mul] at h2
    simp only [zPos]
    omega

theorem zPos_injective {κ τ l j : ℕ} {a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j} (h : zPos a = zPos b) : a = b := by
  rcases a with (i | i) | ⟨s, u⟩ <;> rcases b with (i' | i') | ⟨s', u'⟩ <;> simp only [zPos] at h
  · obtain rfl := Fin.ext h
    rfl
  · have := i.isLt
    omega
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · obtain rfl := Fin.ext (Nat.add_left_cancel h)
    rfl
  · have := i.isLt
    omega
  · have := i'.isLt
    omega
  · have := i'.isLt
    omega
  · have e1 := PatPlaces.block_div (r := κ + l) (i := (s : ℕ)) u.isLt
    have e2 := PatPlaces.block_div (r := κ + l) (i := (s' : ℕ)) u'.isLt
    rw [h, e2] at e1
    obtain rfl : s = s' := Fin.ext e1.symm
    obtain rfl : u = u' := Fin.ext (Nat.add_left_cancel h)
    rfl

theorem places_to_pattern (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) →
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) := by
  rintro ⟨hA, hB⟩ a b hab
  by_cases he : a = b
  · subst he
    rw [if_pos rfl]
    rcases a with (i | i) | ⟨s, u⟩
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact (hA _ (by have := i.isLt; simp only [zPos]; omega)).1
    · exact absurd (by simp [FreeIx]) hab
  · rw [if_neg he]
    have hne : zPos a ≠ zPos b := fun h => he (zPos_injective h)
    have hs1 := PatPlaces.symIdx_cases κ ρ (zPos a)
    have hs2 := PatPlaces.symIdx_cases κ ρ (zPos b)
    rcases b with (j' | j') | ⟨s', u'⟩
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · refine (hA _ (by have := j'.isLt; simp only [zPos]; omega)).2 _ (zPos_lt a) hne ?_
      rcases a with (i | i) | ⟨s, u⟩
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · have := i.isLt
        have := j'.isLt
        simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hab hne hs1 hs2 ⊢
        omega
      · left
        simp only [zPos]
        omega
    · rcases a with (i | i) | ⟨s, u⟩
      · exact absurd (by simp [FreeIx]) hab
      · exact absurd (by simp [FreeIx]) hab
      · have hlt : (s' : ℕ) < s := by
          simp only [FreeIx, not_le, Fin.lt_iff_val_lt_val] at hab
          exact hab
        refine hB _ _ (by simp only [zPos]; omega) (zPos_lt _) (zPos_lt _) ?_
        simp only [zPos]
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt]
        exact hlt

theorem pattern_to_places (F : Type) [Zero F] [One F] (κ ρ l τ j : ℕ) (R : ℕ → ℕ → F) :
    (∀ (a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j), ¬ FreeIx ρ a b → R (zPos a) (zPos b) = if a = b then 1 else 0) →
    ((∀ p', p' < κ + l → R p' p' = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' →
        (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → R p p' = 0) ∧
      (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ →
        (p' - (κ + l)) / τ < (p - (κ + l)) / τ → R p p' = 0)) := by
  intro hpat
  refine ⟨fun p' hp' => ?_, fun p p' h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj (show p' < κ + l + j * τ by omega)
    refine ⟨?_, fun p hp hne hcond => ?_⟩
    · have h0 := hpat a a (by
        rcases a with (i | i) | ⟨s, u⟩
        · simp [FreeIx, FreeTop]
        · simp [FreeIx, FreeTop]
        · simp only [zPos] at hp'
          omega)
      rwa [if_pos rfl] at h0
    · obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj hp
      have hca : c ≠ a := fun h => hne (h ▸ rfl)
      rw [hpat c a ?_, if_neg hca]
      have hs1 := PatPlaces.symIdx_cases κ ρ (zPos c)
      have hs2 := PatPlaces.symIdx_cases κ ρ (zPos a)
      rcases a with (i | i) | ⟨s', u'⟩
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · rcases c with (i' | i') | ⟨s, u⟩
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · have := i.isLt
          have := i'.isLt
          simp only [zPos, FreeIx, FreeTop, Fin.lt_iff_val_lt_val] at hcond hne hs1 hs2 ⊢
          omega
        · simp [FreeIx]
      · simp only [zPos] at hp'
        omega
  · obtain ⟨a, rfl⟩ := PatPlaces.zPos_surj h2
    obtain ⟨c, rfl⟩ := PatPlaces.zPos_surj h3
    rcases a with (i | i) | ⟨s', u'⟩
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · have := i.isLt
      simp only [zPos] at h1
      omega
    · rcases c with (i | i) | ⟨s, u⟩
      · have h0 : zPos (Sum.inl (Sum.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · have h0 : zPos (Sum.inl (Sum.inr i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) - (κ + l) = 0 := by
          have := i.isLt
          simp only [zPos]
          omega
        rw [h0, Nat.zero_div] at h4
        exact absurd h4 (Nat.not_lt_zero _)
      · simp only [zPos] at h4
        rw [PatPlaces.block_div u'.isLt, PatPlaces.block_div u.isLt] at h4
        rw [hpat _ _ ?_, if_neg ?_]
        · intro h
          cases h
          exact lt_irrefl _ h4
        · simp only [FreeIx, Fin.le_iff_val_le_val]
          omega

section Entry
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem entry_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {m : E} (hm : IntAt P m) (c : Prop) [Decidable c] :
    valuation k (ι m - (if c then 1 else 0)) < 1 ↔ redP P m = if c then 1 else 0 := by
  have hI := (GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU).2.1
  by_cases hc : c
  · simp only [if_pos hc]
    have h0 : ι m - 1 = ι (m + algebraMap (𝓞 E) E (-1)) := by
      simp [sub_eq_add_neg]
    rw [h0, hI _ (hm.add (IntAt.coe P _)), reduction_add hm (IntAt.coe P _), reduction_coe]
    simp [add_neg_eq_zero]
  · simp only [if_neg hc, sub_zero]
    exact hI m hm

end Entry

theorem pattern_iff_places : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l ρ τ j M hM
  have h : (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b →
      valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔
      (∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → redP P (M (zPos a) (zPos b)) = if a = b then 1 else 0) := by
    refine forall_congr' fun a => forall_congr' fun b => imp_congr_right fun _ => ?_
    rw [Matrix.one_apply]
    exact entry_iff hC hU (hM _ _ (zPos_lt a) (zPos_lt b)) (a = b)
  rw [h]
  exact ⟨pattern_to_places _ κ ρ l τ j fun p p' => redP P (M p p'),
    places_to_pattern _ κ ρ l τ j fun p p' => redP P (M p p')⟩

end GlobalTheory.PatResidue
