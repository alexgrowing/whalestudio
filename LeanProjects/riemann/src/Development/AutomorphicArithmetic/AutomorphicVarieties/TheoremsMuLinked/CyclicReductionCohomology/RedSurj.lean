import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_surj {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Y : Mm O n m) : ∃ Y', red m Y' = Y := by
  choose Y' hY' using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  exact ⟨Matrix.of Y', by ext i j; exact hY' i j⟩

private theorem red_add' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A + B) = red m A + red m B := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0GO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n), l ≠ 2 → ∃ C : ℕ, ∀ m, {Y : Mm O n m | red m y.P * Y = -(Yᵀ * red m y.P) ∧ ∀ g, y.ρ0 m g * Y * y.ρ0 m g⁻¹ = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ hO _ n y hl
  have h2u : IsUnit (2 : O) := (omFacts l O).1 hl
  let Φ : Option G0.G₀ → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s => s.elim
    (LinearMap.mulLeft O (y.P : Matrix (Fin n) (Fin n) O) + (LinearMap.mulRight O (y.P : Matrix (Fin n) (Fin n) O)).comp
      (Matrix.transposeLinearEquiv (Fin n) (Fin n) O O).toLinearMap)
    fun g => (LinearMap.mulRight O (mat y.ρ g⁻¹)).comp (LinearMap.mulLeft O (mat y.ρ g)) - LinearMap.id
  have hΦ0 : ∀ Y, Φ none Y = (y.P : Matrix (Fin n) (Fin n) O) * Y + Yᵀ * y.P := fun _ => rfl
  have hΦ : ∀ g Y, Φ (some g) Y = mat y.ρ g * Y * mat y.ρ g⁻¹ - Y := fun _ _ => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n _ Φ
  have hk : (⨅ g, LinearMap.ker (Φ g) : Submodule O (Matrix (Fin n) (Fin n) O)) = ⊥ := by
    refine eq_bot_iff.2 fun Y hY => ?_
    obtain ⟨c, hc, hsp⟩ := y.span
    have h1 : ∀ Z ∈ Submodule.span O (Set.range (mat y.ρ)), Z * Y = Y * Z := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hZ =>
        obtain ⟨g, rfl⟩ := hZ
        have h1 : Φ (some g) Y = 0 := (Submodule.mem_iInf _).mp hY (some g)
        rw [hΦ, sub_eq_zero] at h1
        have h2 := congrArg (· * mat y.ρ g) h1
        simpa only [Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one] using h2
      | zero => simp
      | add a b _ _ ha hb => rw [Matrix.add_mul, Matrix.mul_add, ha, hb]
      | smul a b _ hb => rw [Matrix.smul_mul, Matrix.mul_smul, hb]
    have h2 : ∀ Z, Z * Y = Y * Z := fun Z => by
      have := h1 _ (hsp Z)
      rw [Matrix.smul_mul, Matrix.mul_smul] at this
      exact smul_right_injective _ hc this
    obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_single (M := Y) fun i j _ => h2 _
    have h3 : Φ none Y = 0 := (Submodule.mem_iInf _).mp hY none
    have hs : Y = a • (1 : Matrix (Fin n) (Fin n) O) := by
      rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have ht : Yᵀ = Y := by rw [hs, Matrix.transpose_smul, Matrix.transpose_one]
    rw [hΦ0, ht, h2, ← two_smul O, h2u.smul_eq_zero] at h3
    exact (Units.mul_left_eq_zero y.P).1 h3
  refine ⟨C, fun m => ?_⟩
  have := hC m
  rw [hk, finrank_bot, mul_zero, zero_add] at this
  refine le_trans (le_of_eq (congrArg Set.ncard ?_)) this
  have ht : ∀ Y : Matrix (Fin n) (Fin n) O, red m Yᵀ = (red m Y)ᵀ := fun _ => rfl
  ext Y
  constructor
  · rintro ⟨h0, hY⟩
    obtain ⟨Y', e⟩ := red_surj m Y
    refine ⟨Y', e, ?_⟩
    rintro (_ | g)
    · rw [hΦ0, red_add', red_mul', red_mul', ht, e, h0, neg_add_cancel]
    · rw [hΦ, red_sub', red_mul', red_mul', e]
      exact sub_eq_zero.mpr (hY g)
  · rintro ⟨Y', e, h⟩
    refine ⟨?_, fun g => ?_⟩
    · have h1 := h none
      rw [hΦ0, red_add', red_mul', red_mul', ht, e] at h1
      exact eq_neg_of_add_eq_zero_left h1
    · have h1 := h (some g)
      rw [hΦ, red_sub', red_mul', red_mul', e] at h1
      exact sub_eq_zero.mp h1
