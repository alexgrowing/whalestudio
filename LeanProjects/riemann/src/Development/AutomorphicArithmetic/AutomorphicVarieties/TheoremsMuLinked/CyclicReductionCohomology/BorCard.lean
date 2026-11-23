import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem card_lt' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n.choose 2 := by
  rw [Fintype.card_subtype]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  simpa using this

private theorem card_le' (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 ≤ p.2} = n + n.choose 2 := by
  rw [← card_lt' n]
  have e : {p : Fin n × Fin n // p.1 ≤ p.2} ≃ Fin n ⊕ {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun p => if h : p.1.1 < p.1.2 then .inr ⟨p.1, h⟩ else .inl p.1.1
      invFun := Sum.elim (fun i => ⟨(i, i), le_rfl⟩) fun p => ⟨p.1, p.2.le⟩
      left_inv := fun p => by
        by_cases h : p.1.1 < p.1.2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inl]
          exact Subtype.ext (Prod.ext rfl (le_antisymm p.2 (not_lt.1 h)))
      right_inv := by
        rintro (i | p)
        · simp
        · simp [p.2] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

private theorem card_up (X : Type) [Zero X] (n : ℕ) :
    Nat.card {Z : Matrix (Fin n) (Fin n) X // ∀ i j, j < i → Z i j = 0} = Nat.card X ^ (n + n.choose 2) := by
  rw [← card_le', ← Nat.card_eq_fintype_card, ← Nat.card_fun]
  exact Nat.card_congr
    { toFun := fun Z p => Z.1 p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0, fun i j h => by simp [not_le.2 h]⟩
      left_inv := fun Z => Subtype.ext (Matrix.ext fun i j => by
        by_cases h : i ≤ j
        · simp [h]
        · simp [h, Z.2 i j (not_le.1 h)])
      right_inv := fun f => funext fun p => by simp [p.2] }

theorem UpperTheory.V.Th.borCard :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (v : L.Vl), Nat.card (bor y m v) = Nat.card (ResidueField O) ^ (m * (n + n.choose 2)) := by
  intro l _ L G0 O _ _ _ _ _ n y m v
  have i1 : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.w v : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.inv_mul, red_one]
  have i2 : red m (y.w v : Matrix (Fin n) (Fin n) O) * red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← red_mul, Units.mul_inv, red_one]
  rw [pow_mul, ← ((omFacts l O).2 m).2.1, ← card_up]
  generalize hw : red m (y.w v : Matrix (Fin n) (Fin n) O) = w at i1 i2
  generalize hwi : red m (((y.w v)⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = wi at i1 i2
  have hm : ∀ Z, Z ∈ bor y m v ↔ ∀ i j, j < i → (wi * Z * w) i j = 0 := fun Z => by rw [← hw, ← hwi]; rfl
  exact Nat.card_congr
    { toFun := fun Z => ⟨wi * Z.1 * w, (hm _).1 Z.2⟩
      invFun := fun U => ⟨w * U.1 * wi, (hm _).2 (by
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]; exact U.2)⟩
      left_inv := fun Z => Subtype.ext (by
        show w * (wi * Z.1 * w) * wi = Z.1
        rw [← mul_assoc, ← mul_assoc, i2, one_mul, mul_assoc, i2, mul_one])
      right_inv := fun U => Subtype.ext (by
        show wi * (w * U.1 * wi) * w = U.1
        rw [← mul_assoc, ← mul_assoc, i1, one_mul, mul_assoc, i1, mul_one]) }
