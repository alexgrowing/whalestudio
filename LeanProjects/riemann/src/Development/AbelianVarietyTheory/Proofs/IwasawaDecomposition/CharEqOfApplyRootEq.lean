import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharacterIndependentUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameRepConjugateInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
namespace GlobalTheory.TameTau

theorem char_eq_of_apply_root_eq : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ A P hP O _ _ _ _ _ hO χ hχ m hm hmP hχm ϖ hϖP hϖ2 π hπ σ hσ σ' hσ' heq
  have hm0 : m ≠ 0 := hm.ne'
  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hP]
    simpa using h
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨σ₀, hσ₀, hσ₀π⟩ := GlobalTheory.T.inertia_acts_on_tame_root A P hP m hm hmP ϖ hϖP hϖ2 π hπ ζ hζ.pow_eq_one
  have J := fun τ hτ => GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator A γ hγ hO χ hχ m hm hvm hχm (ϖ : E) π hπ0 hπ τ hτ
  obtain ⟨k, -, hk⟩ := J σ₀ hσ₀
  obtain ⟨n, hn1, hn2⟩ := J σ hσ
  obtain ⟨n', hn1', hn2'⟩ := J σ' hσ'
  set θ := γ π / π with hθ
  rw [hσ₀π, mul_div_cancel_right₀ _ hπ0] at hk
  have hθn : θ ^ n = θ ^ n' := by rw [← hn2, ← hn2', heq]
  have hζn : ζ ^ n = ζ ^ n' := by rw [hk, ← pow_mul, ← pow_mul, mul_comm k n, mul_comm k n', pow_mul, pow_mul, hθn]
  have hmod : n ≡ n' [MOD m] := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
    have hu : (Units.mk0 ζ hζ0) ^ n = (Units.mk0 ζ hζ0) ^ n' := Units.ext (by simpa using hζn)
    rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hζ.eq_orderOf] at hu
    exact hu
  have hγI : γ ∈ Ine (F := E) A := hγ.1
  have hord : orderOf (χ γ) ∣ m := orderOf_dvd_of_pow_eq_one (hχm γ hγI)
  rw [hn1, hn1', pow_eq_pow_iff_modEq]
  exact Nat.ModEq.of_dvd hord hmod

end GlobalTheory.TameTau
