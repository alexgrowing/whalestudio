import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Count

variable {R : Type} [CommRing R] {n : ℕ}

private abbrev UU (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

private theorem card_UU : Nat.card (UU n) = n.choose 2 := by
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))
  rw [Finset.card_univ, Fintype.card_fin, Finset.univ_product_univ] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← h]

private def upM (f : UU n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else 0

private theorem upM_inj (u : R) : Function.Injective fun f : UU n → R => upM f - u • (upM f)ᵀ := by
  intro f f' e
  funext ⟨⟨i, j⟩, h⟩
  have h : i < j := h
  have h' : ¬ j < i := not_lt.2 h.le
  have := congrFun (congrFun e i) j
  simpa [upM, h, h'] using this

private theorem count_fix [Finite R] {A B : Matrix (Fin n) (Fin n) R} (h1 : A * B = 1)
    (T : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R) (hT : ∀ Z, T Z = -(A * Zᵀ * B))
    (hTT : ∀ Z, T (T Z) = Z) : Nat.card R ^ n.choose 2 ≤ Nat.card {Z // T Z = Z} := by
  have h2 : B * A = 1 := mul_eq_one_comm.1 h1
  have k : ∀ Z, A * Bᵀ * Z * (Aᵀ * B) = Z := fun Z => by
    have := hTT Z
    rw [hT, hT] at this
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  have k1 : A * Bᵀ * (Aᵀ * B) = 1 := by simpa using k 1
  have k2 : Aᵀ * B * (A * Bᵀ) = 1 := mul_eq_one_comm.1 k1
  have k3 : ∀ Z, Z * (Aᵀ * B) = Aᵀ * B * Z := fun Z => by
    conv_rhs => rw [← k Z]
    rw [← Matrix.mul_assoc (Aᵀ * B), ← Matrix.mul_assoc (Aᵀ * B), k2, Matrix.one_mul]
  obtain ⟨u, hu⟩ : Aᵀ * B ∈ Set.range (Matrix.scalar (Fin n)) := by
    rw [← Matrix.center_eq_range]
    exact Semigroup.mem_center_iff.2 k3
  have hu' : Aᵀ * B = u • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← hu, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have a1 : Aᵀ = u • A := by
    calc Aᵀ = Aᵀ * B * A := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = u • A := by rw [hu', Matrix.smul_mul, Matrix.one_mul]
  have a2 : u • u • A = A := by
    have := congrArg Matrix.transpose a1
    rw [Matrix.transpose_transpose, Matrix.transpose_smul, a1] at this
    exact this.symm
  have a3 : ∀ X : Matrix (Fin n) (Fin n) R, u • u • X = X := fun X => by
    calc u • u • X = (u • u • A) * (B * X) := by
          rw [Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = X := by rw [a2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  let F : (UU n → R) → {Z // T Z = Z} := fun f =>
    ⟨A * (upM f - u • (upM f)ᵀ), by
      rw [hT, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hu', Matrix.mul_smul, Matrix.mul_one,
        ← Matrix.mul_neg, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_transpose, smul_sub, a3,
        neg_sub]⟩
  have hF : Function.Injective F := by
    intro f f' e
    have e' : A * (upM f - u • (upM f)ᵀ) = A * (upM f' - u • (upM f')ᵀ) := congrArg Subtype.val e
    have e'' := congrArg (B * ·) e'
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul] at e''
    exact upM_inj u e''
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fun, card_UU] at this

end Count

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (X Y : Matrix (Fin n) (Fin n) O) :
    red m X * red m Y = red m (X * Y) := (Matrix.map_mul (f := Ideal.Quotient.mk (maximalIdeal O ^ m))).symm

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

private theorem red_inv {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (X : GL (Fin n) O) :
    red m (X : Matrix (Fin n) (Fin n) O) * red m ((X⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
  rw [red_mul, Units.mul_inv, red_one]

theorem UpperTheory.V.Th.pow_choose_two_le_card_fixed_ad0_of_odd_involution :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)) (c' : G.Γ), l ≠ 2 → IsAd0 h y m rep → c' * c' = 1 → G.η c' = -1 → Nat.card (ResidueField O) ^ (m * n.choose 2) ≤ Nat.card {Z : Mm O n m // rep c' Z = Z} := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep c' _ hA hc hη
  obtain ⟨f1, f2, -⟩ := (UpperTheory.V.Th.omFacts l O).2 m
  haveI := f1
  let g : G.G₀ := ⟨c' * G.c⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_inv, hη, G.η_c, mul_inv_cancel]⟩
  have hg : c' = (g : G.Γ) * G.c := by simp [g]
  have p1 := red_inv m y.P
  have p2 := mul_eq_one_comm.1 p1
  have r1 : y.ρm h m g * y.ρm h m g⁻¹ = 1 := by
    have := red_inv m (y.ρ (h.p₀ g))
    rw [← map_inv, ← map_inv] at this
    exact this
  rw [pow_mul, ← f2]
  refine count_fix (A := y.ρm h m g * red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O))
    (B := red m y.P * y.ρm h m g⁻¹) ?_ (rep c') (fun Z => ?_) fun Z => ?_
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (y.ρm h m g⁻¹), p2, Matrix.one_mul, r1]
  · have a1 := hA.1 g (rep G.c Z)
    have a2 := hA.2 Z
    rw [one_smul] at a1 a2
    have a3 : rep G.c Z = -(red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (Zᵀ * red m y.P)) := by
      rw [← Matrix.mul_neg, ← a2, ← Matrix.mul_assoc, p2, Matrix.one_mul]
    conv_lhs => rw [hg, map_mul, Module.End.mul_apply]
    refine a1.trans ?_
    rw [a3]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rw [← Module.End.mul_apply, ← map_mul, hc, map_one, Module.End.one_apply]
