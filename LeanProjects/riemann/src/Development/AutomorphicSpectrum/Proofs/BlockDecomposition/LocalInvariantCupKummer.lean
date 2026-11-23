import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import ReciprocityTheory.GaloisValuations.GlobalE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupFrobeniusFactorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerFixesRootUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZeroStatement
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open ValuativeRel

namespace GlobalTheory.CompanionTheory.KapChi

theorem pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζ : ζ ^ N = 1) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) N, pow_add, pow_mul, hζ, one_pow, one_mul]

def addHom {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k) :
    D →* Multiplicative (ZMod N) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (χ g)) (fun g k => by rw [h]; rfl)

theorem chi_decomp {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k)
    (φ t i : D) (a : ℕ) (hφ : χ φ = 1) (hi : χ i = 0) : χ (φ ^ a * t ^ N * i) = a := by
  have hp : ∀ (x : D) (n : ℕ), χ (x ^ n) = n * χ x := fun x n => by
    have := map_pow (addHom χ h) x n
    have e : Multiplicative.toAdd (addHom χ h (x ^ n)) = χ (x ^ n) := rfl
    rw [← e, this, toAdd_pow]
    simp [addHom]
  rw [h, h, hi, hp, hp, hφ]
  simp

section Dec

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}

theorem chi_unique (hA : IsPlaceOver A v) (hN : 0 < N) {χ χ' : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    (ha' : ∀ g h, χ' (g * h) = χ' g + χ' h)
    (hI' : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0)
    (hF' : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) :
    χ = χ' := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  funext g
  obtain ⟨a, -, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), chi_decomp χ' ha' φ t i a (hF' φ hφ₁) (hI' i hi)]

theorem chi_eq_zero_of_fix (hA : IsPlaceOver A v) (hN : 0 < N) {χ : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    {ξ : Ω} (hξ : IsPrimitiveRoot ξ (normV v ^ N - 1)) (g : Dec (F := F) A)
    (hg : (g : G F Ω) ξ = ξ) : χ g = 0 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  obtain ⟨a, haN, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  have h0 := GlobalTheory.T.frobenius_power_fixes_root_unique F Ω A v hA φ hφ₁ N hN ξ hξ a t i haN hi hg
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), h0, Nat.cast_zero]

end Dec

section Core

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem apply_eq_pow_cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) {ζ : Ω} (hζ : ζ ^ l ^ r = 1) :
    g ζ = ζ ^ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ

theorem exists_cochain_cup (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) {ϖ ϖ' : 𝓞 F} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2)
    (h1' : ϖ' ∈ v.asIdeal) (h2' : ϖ' ∉ v.asIdeal ^ 2) {t : Ω}
    (ht : t ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F))
    {κt χ : Dec (F := F) A → ZMod (l ^ r)}
    (hκ : ∀ g : Dec (F := F) A, (g : G F Ω) t = ζ ^ (κt g).val * t)
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) :
    ∃ c : Dec (F := F) A → ZMod (l ^ r), Continuous c ∧ ∀ g h : Dec (F := F) A,
      ((cycMod F Ω l r (g : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c h - c (g * h) + c g =
        κt g * χ h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hN : 0 < l ^ r := pow_pos hl r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  obtain ⟨θ, hθ, hθ', hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v hA ι hι
  have hlift' : ∀ (σ : GlobalTheory.LocDict.GalLoc v) (x : Ω), σ (ι x) = ι ((θ.symm σ : G F Ω) x) := fun σ x => by
    have := hlift (θ.symm σ) x
    rwa [MulEquiv.apply_symm_apply] at this

  have hq : 1 < normV v := ReciprocityTheory.Gal.one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, n = normV v ^ l ^ r - 1 := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  rw [hn] at hξ
  have hξv : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion F] ^ l ^ r - 1) := by
    rw [GlobalTheory.T.residue_field_card_eq_norm F v]
    exact hξ.map_of_injective ι.toRingHom.injective
  let ψ : GlobalTheory.LocDict.GalLoc v →* Multiplicative (ZMod (l ^ r)) :=
    (addHom χ ha).comp θ.symm.toMonoidHom
  have hfix : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ξ) = ι ξ → ψ σ = 1 := fun σ hσ => by
    rw [hlift'] at hσ
    have e := chi_eq_zero_of_fix hA hN ha hI hF hξ (θ.symm σ) (ι.toRingHom.injective hσ)
    show Multiplicative.ofAdd (χ (θ.symm σ)) = 1
    rw [e]
    rfl
  have ho : IsOpen (ψ.ker : Set (GlobalTheory.LocDict.GalLoc v)) := by
    have : FiniteDimensional (v.adicCompletion F) (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}).fixingSubgroup)
      (fun σ hσ => hfix σ ?_) (IntermediateField.fixingSubgroup_isOpen _)
    exact hσ ⟨ι ξ, IntermediateField.mem_adjoin_simple_self _ _⟩

  have hϖ0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hϖ0' : algebraMap F (v.adicCompletion F) (ϖ' : F) ≠ 0 := by
    intro h
    have h0 : (ϖ' : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ' = 0 := by exact_mod_cast h0
    exact h2' (h0' ▸ Ideal.zero_mem _)
  let U : (v.adicCompletion F)ˣ := Units.mk0
    (algebraMap F (v.adicCompletion F) (ϖ' : F) / algebraMap F (v.adicCompletion F) (ϖ : F))
    (div_ne_zero hϖ0' hϖ0)
  have hU : (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) =
      algebraMap F (v.adicCompletion F) (ϖ' : F) := div_mul_cancel₀ _ hϖ0
  have hord := GlobalTheory.T.uniformizer_ratio_valuation_zero F v ϖ ϖ' h1 h2 h1' h2' U hU
  have hnorm := GlobalTheory.T.norm_from_kummer_unramified_unit (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN.ne' (ι ξ) hξv ψ ho hfix U hord
  have hcomm : ∀ x : F, ι (algebraMap F Ω x) =
      algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (algebraMap F (v.adicCompletion F) x) := fun x => by
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]
  have hT : ι t ^ l ^ r = algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (U : v.adicCompletion F) := by
    have e := congrArg ι ht
    rw [map_mul, map_pow, hcomm, hcomm, ← hU, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero _).2 hϖ0) e
  have hc0 : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ζ) = ι ζ ^
      ((cycMod F Ω l r (θ.symm σ : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := fun σ => by
    rw [hlift', apply_eq_pow_cycMod l r _ hζ.pow_eq_one, map_pow]
  have hκ' : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι t) = ι ζ ^ (κt (θ.symm σ)).val * ι t := fun σ => by
    rw [hlift', hκ, map_mul, map_pow]
  obtain ⟨c, hc, hc2⟩ := GlobalTheory.T.kummer_cocycle_norm_criterion (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN (ι ζ)
    (hζ.map_of_injective ι.toRingHom.injective) _ hc0 ψ ho U hnorm (ι t) (fun σ => κt (θ.symm σ)) hT hκ'
  refine ⟨fun g => c (θ g), hc.continuous.comp hθ, fun g h => ?_⟩
  have e := hc2 (θ g) (θ h)
  have hψ : Multiplicative.toAdd (ψ (θ h)) = χ h := by
    show χ (θ.symm (θ h)) = χ h
    rw [MulEquiv.symm_apply_apply]
  simp only [MulEquiv.symm_apply_apply, ← map_mul] at e
  rw [hψ] at e
  exact e

end Core

theorem cup_class_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 hy hκ hχa hχI hχF hz ϖ' y' κ' χ' z' h1' h2' hy'
    hκ' hχa' hχI' hχF' hz'
  have hN : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  obtain rfl : χ = χ' := chi_unique hA hN hχa hχI hχF hχa' hχI' hχF'
  have hϖ0 : algebraMap F Ω (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hy
    exact hϖ0 hy.symm
  have ht : (y' / y) ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F) := by
    rw [div_pow, hy, hy', div_mul_cancel₀ _ hϖ0]
  have hκt : ∀ g : Dec (F := F) A, (g : G F Ω) (y' / y) = ζ ^ (κ' g - κ g).val * (y' / y) := fun g => by
    have e := pow_val_add hζ.pow_eq_one (κ' g - κ g) (κ g)
    rw [sub_add_cancel] at e
    have hgy : ζ ^ (κ g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [map_div₀, hκ, hκ', e]
    field_simp
  obtain ⟨c, hc, hc2⟩ := exists_cochain_cup l r hr hζ hA h1 h2 h1' h2' ht hκt hχa hχI hχF
  refine ((Submodule.Quotient.eq _).2 ?_).symm
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  have e := hc2 g h
  rw [sub_mul] at e
  show _ = z'.1 (g, h) - z.1 (g, h)
  rw [hz, hz', ← e]
  rfl

end GlobalTheory.CompanionTheory.KapChi
