import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

namespace GlobalTheory.LeviBlockCharacter

theorem exists_shift {F : Type} [Field F] [Finite F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (χ : AddChar F ℂ) : ∃ a : F, ∀ x, χ x = ψ (a * x) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)
  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨a, ha⟩ := hbij.2 χ
  exact ⟨a, fun x => by rw [← ha, AddChar.mulShift_apply]⟩

theorem prod_shift {ι : Type} (k : ι → Type) [∀ i, CommRing (k i)] {S : Type} [CommRing S]
    (Pg : Finset ι) (p p' : ∀ i, S →+* k i) (χ : S → ℂ) (ψ : ∀ i, AddChar (k i) ℂ)
    (hψ : ∀ i ∈ Pg, ∀ χ' : AddChar (k i) ℂ, ∃ a, ∀ x, χ' x = ψ i (a * x))
    (hadd : ∀ s t, χ (s + t) = χ s * χ t)
    (hker : ∀ s, (∀ i ∈ Pg, p i s = 0 ∧ p' i s = 0) → χ s = 1)
    (hsurj : ∀ u u' : ∀ i, k i, ∃ s, ∀ i ∈ Pg, p i s = u i ∧ p' i s = u' i)
    (hposition : ∀ i ∈ Pg, (∃ s, (∀ j ∈ Pg, (j ≠ i → p j s = 0) ∧ p' j s = 0) ∧ χ s ≠ 1) ∧
      ∃ s, (∀ j ∈ Pg, p j s = 0 ∧ (j ≠ i → p' j s = 0)) ∧ χ s ≠ 1) :
    ∃ a₁ a₂ : ∀ i, k i, (∀ i ∈ Pg, a₁ i ≠ 0 ∧ a₂ i ≠ 0) ∧
      ∀ s, χ s = ∏ i ∈ Pg, ψ i (a₁ i * p i s + a₂ i * p' i s) := by
  classical
  have h0 : χ 0 = 1 := hker 0 (fun i _ => ⟨map_zero _, map_zero _⟩)
  have hdep : ∀ s t, (∀ i ∈ Pg, p i s = p i t ∧ p' i s = p' i t) → χ s = χ t := by
    intro s t h
    have h1 : χ (s - t) = 1 := hker _ (fun i hi => by
      rw [map_sub, map_sub, (h i hi).1, (h i hi).2, sub_self, sub_self]; exact ⟨rfl, rfl⟩)
    have h2 := hadd t (s - t)
    rw [h1, mul_one, add_sub_cancel] at h2
    exact h2
  choose σ hσ using hsurj
  have hsum : ∀ (A : Finset ι) (f : ι → S), χ (∑ i ∈ A, f i) = ∏ i ∈ A, χ (f i) := by
    intro A f
    induction A using Finset.induction_on with
    | empty => simpa using h0
    | insert a A ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  let c₁ : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun x => χ (σ (Pi.single i x) 0)
      map_zero_eq_one' := hker _ (fun j hj => by
        rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]; simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd]
        refine hdep _ _ (fun j hj => ?_)
        rw [map_add, map_add, (hσ _ _ j hj).1, (hσ _ _ j hj).2, (hσ _ _ j hj).1, (hσ _ _ j hj).2,
          (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.single_add]
        simp }
  let c₂ : ∀ i, AddChar (k i) ℂ := fun i =>
    { toFun := fun x => χ (σ 0 (Pi.single i x))
      map_zero_eq_one' := hker _ (fun j hj => by
        rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]; simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd]
        refine hdep _ _ (fun j hj => ?_)
        rw [map_add, map_add, (hσ _ _ j hj).1, (hσ _ _ j hj).2, (hσ _ _ j hj).1, (hσ _ _ j hj).2,
          (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.single_add]
        simp }
  have hc₁ : ∀ i x, c₁ i x = χ (σ (Pi.single i x) 0) := fun _ _ => rfl
  have hc₂ : ∀ i x, c₂ i x = χ (σ 0 (Pi.single i x)) := fun _ _ => rfl
  have e₁ : ∀ i, ∃ a : k i, i ∈ Pg → ∀ x, c₁ i x = ψ i (a * x) := fun i => by
    by_cases hi : i ∈ Pg
    · obtain ⟨a, ha⟩ := hψ i hi (c₁ i); exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hi⟩
  have e₂ : ∀ i, ∃ a : k i, i ∈ Pg → ∀ x, c₂ i x = ψ i (a * x) := fun i => by
    by_cases hi : i ∈ Pg
    · obtain ⟨a, ha⟩ := hψ i hi (c₂ i); exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose a₁ ha₁ using e₁
  choose a₂ ha₂ using e₂
  refine ⟨a₁, a₂, fun i hi => ⟨fun h => ?_, fun h => ?_⟩, fun s => ?_⟩
  · obtain ⟨s, hs, hne⟩ := (hposition i hi).1
    apply hne
    have h1 := ha₁ i hi (p i s)
    rw [h, zero_mul, AddChar.map_zero_eq_one, hc₁] at h1
    rw [← h1]
    refine hdep _ _ (fun j hj => ?_)
    rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]
    refine ⟨?_, (hs j hj).2⟩
    by_cases hji : j = i
    · subst hji; simp
    · rw [(hs j hj).1 hji, Pi.single_eq_of_ne hji]
  · obtain ⟨s, hs, hne⟩ := (hposition i hi).2
    apply hne
    have h1 := ha₂ i hi (p' i s)
    rw [h, zero_mul, AddChar.map_zero_eq_one, hc₂] at h1
    rw [← h1]
    refine hdep _ _ (fun j hj => ?_)
    rw [(hσ _ _ j hj).1, (hσ _ _ j hj).2]
    refine ⟨(hs j hj).1, ?_⟩
    by_cases hji : j = i
    · subst hji; simp
    · rw [(hs j hj).2 hji, Pi.single_eq_of_ne hji]
  · have h1 : χ s = χ (∑ i ∈ Pg, (σ (Pi.single i (p i s)) 0 + σ 0 (Pi.single i (p' i s)))) := by
      refine hdep _ _ (fun j hj => ?_)
      simp only [map_sum, map_add, (hσ _ _ j hj).1, (hσ _ _ j hj).2, Pi.zero_apply, add_zero,
        zero_add]
      constructor
      · rw [Finset.sum_eq_single j (fun b _ hb => Pi.single_eq_of_ne (Ne.symm hb) _)
          (fun h => absurd hj h), Pi.single_eq_same]
      · rw [Finset.sum_eq_single j (fun b _ hb => Pi.single_eq_of_ne (Ne.symm hb) _)
          (fun h => absurd hj h), Pi.single_eq_same]
    rw [h1, hsum]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [hadd, ← hc₁, ← hc₂, ha₁ i hi, ha₂ i hi, AddChar.map_add_eq_mul]

theorem char_eq_prod_shift : ∀ (E : Type) [Field E] [NumberField E] (S : Type) [CommRing S] (Pg : Finset (Pl E)) (p p' : ∀ PP : Pl E, S →+* kP PP) (χ : S → ℂ) (ψ0 : ∀ PP : Pl E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ0 → (∀ s t, χ (s + t) = χ s * χ t) → (∀ s, (∀ PP ∈ Pg, p PP s = 0 ∧ p' PP s = 0) → χ s = 1) → (∀ u u' : ∀ PP : Pl E, kP PP, ∃ s, ∀ PP ∈ Pg, p PP s = u PP ∧ p' PP s = u' PP) → (∀ PP ∈ Pg, (∃ s, (∀ PP' ∈ Pg, (PP' ≠ PP → p PP' s = 0) ∧ p' PP' s = 0) ∧ χ s ≠ 1) ∧ ∃ s, (∀ PP' ∈ Pg, p PP' s = 0 ∧ (PP' ≠ PP → p' PP' s = 0)) ∧ χ s ≠ 1) → ∃ a₁ a₂ : ∀ PP : Pl E, kP PP, (∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0) ∧ ∀ s, χ s = ∏ PP ∈ Pg, ψ0 PP (a₁ PP * p PP s + a₂ PP * p' PP s) := by
  intro E _ _ S _ Pg p p' χ ψ0 hψ hadd hker hsurj hposition
  refine prod_shift (fun PP : Pl E => kP PP) Pg p p' χ ψ0 (fun PP hPP χ' => ?_) hadd hker hsurj hposition
  have : PP.asIdeal.IsMaximal := PP.isMaximal
  let : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  exact exists_shift (F := kP PP) (ψ0 PP) (hψ PP hPP) χ'

end GlobalTheory.LeviBlockCharacter
