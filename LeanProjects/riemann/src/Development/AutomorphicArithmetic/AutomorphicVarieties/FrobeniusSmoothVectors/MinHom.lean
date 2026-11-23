import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Mathlib.RingTheory.GradedAlgebra.Radical

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (η : Ideal A) (hη : η ∈ minimalPrimes A) :
    η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j} := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { }
  have hp : η.IsPrime := hη.1.1
  have hc : (η.homogeneousCore 𝒜).toIdeal.IsPrime := Ideal.IsPrime.homogeneousCore hp
  have hle : (η.homogeneousCore 𝒜).toIdeal ≤ η := Ideal.toIdeal_homogeneousCore_le 𝒜 η
  have hge : η ≤ (η.homogeneousCore 𝒜).toIdeal := hη.2 ⟨hc, bot_le⟩ hle
  apply le_antisymm
  · refine hge.trans ?_
    show Ideal.homogeneousCore' 𝒜 η ≤ _
    unfold Ideal.homogeneousCore'
    apply Ideal.span_mono
    rintro _ ⟨⟨x, hx⟩, hx', rfl⟩
    exact ⟨hx', hx⟩
  · exact Ideal.span_le.2 fun x hx => hx.1

theorem UpperTheory.V.Fr.min_hom :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η ∈ minimalPrimes S.A, S.IsHom η := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hη
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Fr.gr_A hF hn S
  exact aux S.gr h1 h2 η hη
