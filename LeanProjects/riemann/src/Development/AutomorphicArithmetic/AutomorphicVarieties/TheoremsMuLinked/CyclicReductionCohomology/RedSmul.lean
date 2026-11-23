import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FixCnt

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem red_mul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_sub' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A - B) = red m A - red m B := by
  ext i j
  simp [red]

private theorem red_smul' {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (a : O) (A : Matrix (Fin n) (Fin n) O) :
    red m (a • A) = algebraMap O (Om O m) a • red m A := by
  ext i j
  simp [red]

theorem UpperTheory.V.Th.h0v0O :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (D : Subgroup G0.G₀), y.N4 D → ∃ C : ℕ, ∀ m, {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y}.ncard ≤ Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ _ _ n y D hN
  let M : G0.G₀ → Matrix (Fin n) (Fin n) O := fun g => mat y.ρ g
  let e : G0.G₀ → O := fun g => algebraMap ℤ_[l] O (G0.ε (g : G0.Γ))
  let Φ : D → Matrix (Fin n) (Fin n) O →ₗ[O] Matrix (Fin n) (Fin n) O := fun s =>
    e s • LinearMap.mulLeft O (M s) - LinearMap.mulRight O (M s)
  have hΦ : ∀ s Z, Φ s Z = e s • (M s * Z) - Z * M s := fun s Z => rfl
  obtain ⟨C, hC⟩ := fixCnt l O n D Φ
  have hker : (⨅ s, (Φ s).ker) = ⊥ := by
    rw [eq_bot_iff]
    intro Z hZ
    rw [Submodule.mem_iInf] at hZ
    rw [Submodule.mem_bot]
    apply hN Z
    intro g hg
    have h1 := hZ ⟨g, hg⟩
    rw [LinearMap.mem_ker, hΦ, sub_eq_zero] at h1
    exact h1
  have hfin : Module.finrank O ↥(⨅ s, (Φ s).ker) = 0 := by
    rw [hker]
    exact finrank_bot O _
  refine ⟨C, fun m => ?_⟩
  have hone : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := by
    unfold red
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hinv : ∀ g : G0.G₀, y.ρ0 m g * y.ρ0 m g⁻¹ = 1 ∧ y.ρ0 m g⁻¹ * y.ρ0 m g = 1 := by
    intro g
    simp only [Pt.ρ0, ← red_mul', ← map_mul, mul_inv_cancel, inv_mul_cancel, map_one, hone, and_self]
  have hred : ∀ (g : G0.G₀) (Z : Matrix (Fin n) (Fin n) O),
      red m (e g • (M g * Z) - Z * M g) = epsm O G0 m g • (y.ρ0 m g * red m Z) - red m Z * y.ρ0 m g := by
    intro g Z
    rw [red_sub', red_smul', red_mul', red_mul']
    rfl
  have hset : {Y : Mm O n m | ∀ g ∈ D, epsm O G0 m (g : G0.G₀) • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) = Y} =
      {Y : Mm O n m | ∃ Y' : Matrix (Fin n) (Fin n) O, red m Y' = Y ∧ ∀ s, red m (Φ s Y') = 0} := by
    ext Y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨Y.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_, fun s => ?_⟩
      · ext i j
        simp [red, Function.surjInv_eq]
      · have hY : red m (Y.map (Function.surjInv Ideal.Quotient.mk_surjective)) = Y := by
          ext i j
          simp [red, Function.surjInv_eq]
        rw [hΦ, hred, hY, sub_eq_zero]
        have h1 := h s s.2
        calc epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y)
            = (epsm O G0 m (s : G0.G₀) • (y.ρ0 m s * Y * y.ρ0 m (s : G0.G₀)⁻¹)) * y.ρ0 m s := by
              rw [Matrix.smul_mul, mul_assoc (y.ρ0 m s * Y), (hinv s).2, mul_one]
          _ = Y * y.ρ0 m s := by rw [h1]
    · rintro ⟨Y', rfl, h⟩ g hg
      have h1 := h ⟨g, hg⟩
      rw [hΦ, hred, sub_eq_zero] at h1
      calc epsm O G0 m g • (y.ρ0 m g * red m Y' * y.ρ0 m g⁻¹)
          = (epsm O G0 m g • (y.ρ0 m g * red m Y')) * y.ρ0 m g⁻¹ := by rw [Matrix.smul_mul]
        _ = red m Y' * y.ρ0 m g * y.ρ0 m g⁻¹ := by rw [h1]
        _ = red m Y' := by rw [mul_assoc, (hinv g).1, mul_one]
  rw [hset]
  have h2 := hC m
  rw [hfin, mul_zero, zero_add] at h2
  exact h2
