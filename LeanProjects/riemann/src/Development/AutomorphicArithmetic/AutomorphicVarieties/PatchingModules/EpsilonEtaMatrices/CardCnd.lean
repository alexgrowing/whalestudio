import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def Cnd (lo same : Prop) (d : DD X g) : Prop :=
  (lo → d = 0) ∧ d.ep' = 0 ∧ d.eta = 0 ∧ (same → d.ep = 0) ∧ (¬ same → d.a = 0)

private theorem card_cnd (lo same : Prop) [Decidable lo] [Decidable same] :
    Nat.card {d : DD X g // Cnd lo same d} = Nat.card X ^ (if lo then 0 else if same then 1 else g) := by
  by_cases hlo : lo
  · rw [if_pos hlo, pow_zero, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩, fun d => Subtype.ext (d.2.1 hlo)⟩
  · by_cases hs : same
    · rw [if_neg hlo, if_pos hs, pow_one]
      exact Nat.card_congr
        { toFun := fun d => d.1.a
          invFun := fun y => ⟨⟨y, 0, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun _ => rfl, fun h => absurd hs h⟩
          left_inv := fun d => Subtype.ext (DD.ext rfl (d.2.2.2.2.1 hs).symm d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun y => rfl }
    · rw [if_neg hlo, if_neg hs]
      have e : {d : DD X g // Cnd lo same d} ≃ (Fin g → X) :=
        { toFun := fun d => d.1.ep
          invFun := fun f => ⟨⟨0, f, 0, 0⟩, fun h => absurd h hlo, rfl, rfl, fun h => absurd h hs, fun _ => rfl⟩
          left_inv := fun d => Subtype.ext (DD.ext (d.2.2.2.2.2 hs).symm rfl d.2.2.1.symm d.2.2.2.1.symm)
          right_inv := fun f => rfl }
      rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin]

private theorem sum_exp (ty : Fin n → Bool) :
    (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      n + ((Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 = ty p.2).card +
        g * (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ ty p.1 ≠ ty p.2).card) := by
  have h : ∀ p : Fin n × Fin n, (if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) =
      (if p.1 = p.2 then 1 else 0) + ((if p.1 < p.2 ∧ ty p.1 = ty p.2 then 1 else 0) +
        g * (if p.1 < p.2 ∧ ty p.1 ≠ ty p.2 then 1 else 0)) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with hp | hp | hp
    · have h1 : ¬ p.2 < p.1 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne
      by_cases ht : ty p.1 = ty p.2 <;> simp [hp, h1, h2, ht]
    · simp [hp]
    · have h1 : ¬ p.1 < p.2 := not_lt.2 hp.le
      have h2 : p.1 ≠ p.2 := hp.ne'
      simp [hp, h1, h2]
  rw [Finset.sum_congr rfl fun p _ => h p, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_boole, Nat.cast_id]
  congr 1
  have hd : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) = Finset.diag Finset.univ := by
    ext p
    simp [Finset.mem_diag]
  rw [hd, Finset.diag_card, Finset.card_univ, Fintype.card_fin]

private theorem card_pat (ty : Fin n → Bool) :
    Nat.card {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} =
      Nat.card X ^ (∑ p : Fin n × Fin n, if p.2 < p.1 then 0 else if ty p.1 = ty p.2 then 1 else g) := by
  have e : {Z : Matrix (Fin n) (Fin n) (DD X g) // ∀ i j, Cnd (j < i) (ty i = ty j) (Z i j)} ≃
      ((p : Fin n × Fin n) → {d : DD X g // Cnd (p.2 < p.1) (ty p.1 = ty p.2) d}) :=
    { toFun := fun Z p => ⟨Z.1 p.1 p.2, Z.2 _ _⟩
      invFun := fun f => ⟨fun i j => (f (i, j)).1, fun i j => (f (i, j)).2⟩
      left_inv := fun Z => Subtype.ext rfl
      right_inv := fun f => funext fun p => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact card_cnd _ _

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.bCard :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl), Nat.card (k.b1 (x.Am m) v) = Nat.card x.K ^ (m * (n + nu n x.a k.g)) := by
  intro l _ F n x k m v
  obtain ⟨_, hK, -⟩ := finAm l F n x m k.g
  obtain ⟨-, hnu, -⟩ := tyCard l F n x v k.g
  obtain ⟨hw, hw'⟩ := (rho1 l F n x k (x.Am m)).2.2.2.1 v
  have hM := (tri l F n x k (x.Am m) v).2
  have c1 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw, Matrix.mul_one, ← Matrix.mul_assoc, hw, Matrix.one_mul]
  have c2 : ∀ Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g),
      k.w1 (x.Am m) v * (k.wi1 (x.Am m) v * Y * k.w1 (x.Am m) v) * k.wi1 (x.Am m) v = Y := by
    intro Y
    simp only [Matrix.mul_assoc]
    rw [hw', Matrix.mul_one, ← Matrix.mul_assoc, hw', Matrix.one_mul]
  have e : k.b1 (x.Am m) v ≃ {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) //
      ∀ i j, Cnd (j < i) (x.ty v i = x.ty v j) (Y i j)} :=
    { toFun := fun Z => ⟨k.wi1 (x.Am m) v * Z.1.1 * k.w1 (x.Am m) v, fun i j =>
        have hT := (hM Z.1.1).1 Z.1.2 i j
        ⟨Z.2 i j, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩⟩
      invFun := fun Y => ⟨⟨k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v, (hM _).2 (by
          rw [c1]
          intro i j
          have hc := Y.2 i j
          exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩)⟩, by
          intro i j hij
          show (k.wi1 (x.Am m) v * (k.w1 (x.Am m) v * Y.1 * k.wi1 (x.Am m) v) * k.w1 (x.Am m) v) i j = 0
          rw [c1]
          exact (Y.2 i j).1 hij⟩
      left_inv := fun Z => Subtype.ext (Subtype.ext (c2 _))
      right_inv := fun Y => Subtype.ext (c1 _) }
  rw [Nat.card_congr e, card_pat, sum_exp, hnu, hK, ← pow_mul]
