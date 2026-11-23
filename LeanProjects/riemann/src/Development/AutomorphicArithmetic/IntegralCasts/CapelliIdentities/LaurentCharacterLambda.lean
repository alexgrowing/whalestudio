import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ), IsUnit (↑q : S) → IsUnit ((Int.castRingHom S : ℤ → S) (↑q : ℤ)) := by
  intro S _ q hq
  rwa [map_natCast]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.lam :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → Localization.Away (↑q : ℤ) →+* S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      IsLocalization.Away.lift (↑q : ℤ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.aux3 q hq)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 :
    ∀ (S : Type) [inst : CommRing S], LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : LaurentPolynomial S) := by
  intro S _
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tU :
    (S : Type) → [inst : CommRing S] → (LaurentPolynomial S)ˣ :=
    fun (S : Type) [CommRing S] ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 S,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 S : (LaurentPolynomial S)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.iot :
    {S : Type} → [inst : CommRing S] → (q : ℕ) → IsUnit (↑q : S) → UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* LaurentPolynomial S :=
    fun {S : Type} [CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) ↦
      LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.lam q hq)) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tU S)

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 :
    ∀ (q : ℕ), LaurentPolynomial.T (1 : ℤ) * LaurentPolynomial.T (-1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux5 _

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one :
    ∀ (q : ℕ), LaurentPolynomial.T (-1 : ℤ) * LaurentPolynomial.T (1 : ℤ) = (1 : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q) := by
  intro q
  exact UpperTheory.Reformulated.B.LaurentCharacterLambda.aux6 _

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.tR :
    (q : ℕ) → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ :=
    fun (q : ℕ) ↦
      { val := LaurentPolynomial.T (1 : ℤ), inv := LaurentPolynomial.T (-1 : ℤ), val_inv := UpperTheory.Reformulated.B.LaurentCharacterLambda.aux9 q,
        inv_val := UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_T_neg_one_mul_T_one q : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ }

noncomputable def UpperTheory.Reformulated.B.LaurentCharacterLambda.chi :
    {S : Type} →
      [inst : CommRing S] →
        (q : ℕ) →
          {R : Type} → [inst_1 : CommRing R] → (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) → (S →+* R) → LaurentPolynomial S →+* R :=
    fun {S : Type} [CommRing S] (q : ℕ) {R : Type} [CommRing R] (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) ↦
      LaurentPolynomial.eval₂ ψ
        ((Units.map (↑φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →* R) : (UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q)ˣ → Rˣ) (UpperTheory.Reformulated.B.LaurentCharacterLambda.tR q))

private theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext {S R : Type} [CommRing S] [CommRing R]
    (f g : LaurentPolynomial S →+* R)
    (hC : ∀ a : S, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial S))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT

theorem UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq :
    ∀ {S : Type} [inst : CommRing S] (q : ℕ) (hq : IsUnit (↑q : S)) {R : Type} [inst_1 : CommRing R]
      (φ : UpperTheory.Reformulated.B.LaurentCharacterLambda.LqR q →+* R) (ψ : S →+* R) (χ : LaurentPolynomial S →+* R),
      χ.comp (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq) = φ → χ.comp LaurentPolynomial.C = ψ → χ = UpperTheory.Reformulated.B.LaurentCharacterLambda.chi q φ ψ := by
  intro S _ q hq R _ φ ψ χ h1 h2
  apply UpperTheory.Reformulated.B.LaurentCharacterLambda.laurent_hom_ext
  · intro a
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_C, ← h2, RingHom.comp_apply]
  · rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.chi, LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, ← h1]
    change _ = χ (UpperTheory.Reformulated.B.LaurentCharacterLambda.iot q hq (LaurentPolynomial.T 1))
    rw [UpperTheory.Reformulated.B.LaurentCharacterLambda.iot, LaurentPolynomial.eval₂_T, zpow_one]
    rfl
