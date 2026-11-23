import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PairOLin

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cases_c {l : ℕ} [Fact l.Prime] (F : GFrame l) (γ : F.Γ) :
    (∃ g : F.G₀, γ = g) ∨ ∃ g : F.G₀, γ = g * F.c := by
  by_cases h : γ ∈ F.η.ker
  · exact Or.inl ⟨⟨γ, h⟩, rfl⟩
  · refine Or.inr ⟨⟨γ * F.c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker] at h ⊢
      rw [map_mul, F.η_c, (Int.units_eq_one_or (F.η γ)).resolve_left h]
      simp
    · show γ = γ * F.c * F.c
      rw [mul_assoc, F.c_sq, mul_one]

private theorem tr_c {R : Type} [CommRing R] {n : ℕ} (P Q X Y A B : Matrix (Fin n) (Fin n) R) (e : R) (h1 : Q * P = 1) (h2 : P * Q = 1)
    (hA : P * A = -((1 : R) • (Xᵀ * P))) (hB : P * B = -(e • (Yᵀ * P))) : (A * B).trace = e * (X * Y).trace := by
  have a : A = -(Q * Xᵀ * P) := by
    rw [← Matrix.one_mul A, ← h1, Matrix.mul_assoc, hA, one_smul, Matrix.mul_neg, Matrix.mul_assoc]
  have b : B = -(e • (Q * Yᵀ * P)) := by
    rw [← Matrix.one_mul B, ← h1, Matrix.mul_assoc, hB, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_assoc]
  have c : Q * Xᵀ * P * (Q * Yᵀ * P) = Q * (Xᵀ * Yᵀ * P) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Q, h2, Matrix.one_mul]
  rw [a, b, neg_mul_neg, Matrix.mul_smul, c, trace_smul, smul_eq_mul, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one,
    ← transpose_mul, trace_transpose, trace_mul_comm]

private theorem tr_g {R : Type} [CommRing R] {n : ℕ} (a a' X Y : Matrix (Fin n) (Fin n) R) (e : R) (h1 : a' * a = 1) :
    (((1 : R) • (a * X * a')) * (e • (a * Y * a'))).trace = e * (X * Y).trace := by
  have c : a * X * a' * (a * Y * a') = a * (X * Y * a') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc a' a, h1, Matrix.one_mul]
  rw [one_smul, Matrix.mul_smul, c, trace_smul, smul_eq_mul, trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) : red m (1 : Matrix (Fin n) (Fin n) O) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.pairP :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), G.ε G.c = -1 → ∃ (k : ℕ) (b : Mm O n m →+ Mm O n m →+ ZMod (l ^ k)), 0 < k ∧ ∀ rep rep', IsAd0 h y m rep → IsAd1 h y m rep' → DualPair k G.ε rep rep' b := by
  intro l _ L G G0 h O _ _ _ _ _ n y m hc
  obtain ⟨k, τ, hk, hnd, hlin⟩ := pairO l O m
  let b : Mm O n m →+ Mm O n m →+ ZMod (l ^ k) :=
    { toFun := fun X =>
        { toFun := fun Y => τ (X * Y).trace
          map_zero' := by simp
          map_add' := fun Y Y' => by rw [Matrix.mul_add, trace_add, map_add] }
      map_zero' := by ext Y; simp
      map_add' := fun X X' => by ext Y; simp [Matrix.add_mul] }
  have hb : ∀ X Y, b X Y = τ (X * Y).trace := fun _ _ => rfl
  have hl : ∀ X : Mm O n m, (∀ Y, b X Y = 0) → X = 0 := fun X hX => by
    ext i j
    refine hnd _ fun z => ?_
    have := hX (Matrix.single j i z)
    rw [hb, Matrix.trace_mul_single] at this
    simpa [mul_comm] using this
  refine ⟨k, b, hk, fun rep rep' hr hr' => ⟨hl, fun Y hY => hl Y fun X => by rw [hb, trace_mul_comm]; exact hY X, ?_⟩⟩
  have hg : ∀ (g : G.G₀) X Y, b (rep g X) (rep' g Y) = PadicInt.toZModPow k ((G.ε g : ℤ_[l]ˣ) : ℤ_[l]) * b X Y := by
    intro g X Y
    have e : y.ρm h m g⁻¹ * y.ρm h m g = 1 := by
      show red m _ * red m _ = 1
      rw [← red_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, red_one]
    rw [hb, hr.1 g X, hr'.1 g Y, tr_g _ _ _ _ _ e, hb]
    exact hlin _ _
  have hcc : ∀ X Y, b (rep G.c X) (rep' G.c Y) = PadicInt.toZModPow k ((G.ε G.c : ℤ_[l]ˣ) : ℤ_[l]) * b X Y := by
    intro X Y
    have e1 : red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (y.P : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, Units.inv_mul, red_one]
    have e2 : red m (y.P : Matrix (Fin n) (Fin n) O) * red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
      rw [← red_mul, Units.mul_inv, red_one]
    rw [hb, hb]
    exact (congrArg τ (tr_c _ _ X Y _ _ _ e1 e2 (hr.2 X) (hr'.2 Y))).trans (hlin _ _)
  intro γ X Y
  rcases cases_c G.frame γ with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact hg g X Y
  · show b (rep ((g : G.Γ) * G.c) X) (rep' ((g : G.Γ) * G.c) Y) = PadicInt.toZModPow k ((G.ε ((g : G.Γ) * G.c) : ℤ_[l]ˣ) : ℤ_[l]) * b X Y
    rw [map_mul rep, map_mul rep', Module.End.mul_apply, Module.End.mul_apply, hg, hcc, map_mul, Units.val_mul, map_mul, mul_assoc]
