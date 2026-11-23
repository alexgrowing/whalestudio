import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowCharPowEqSelf
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.KummerCupInv

attribute [local instance 2000] Rep.hV2

theorem pow_identity {F : Type} [Field F] {n m p q r s : ℕ} {ζ y : F} (hy : y ≠ 0) (hζ : ζ ^ n = 1)
    (h : s + q = n * m + r) :
    (ζ ^ p * y) ^ q / y ^ r * y ^ s = ζ ^ ((p * q) % n) * (y ^ n) ^ m := by
  have e : y ^ s * y ^ q = (y ^ n) ^ m * y ^ r := by
    rw [← pow_add, ← pow_mul, ← pow_add, h]
  rw [mul_pow, ← pow_mul, ← pow_eq_pow_mod _ hζ]
  have hr : y ^ r ≠ 0 := pow_ne_zero _ hy
  field_simp
  linear_combination (ζ ^ (p * q)) * e

theorem kummer_key {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n m p q r s k : ℕ} (ζ y u : Ωˣ)
    (g : Ω ≃ₐ[K] Ω) (hζ : ζ ^ n = 1) (hu : (u : Ω) = (y : Ω) ^ n)
    (hg : g (y : Ω) = (ζ : Ω) ^ p * y) (hk : k = (p * q) % n) (h : s + q = n * m + r) :
    (Additive.ofMul (ζ ^ k) + (m : ℤ) • Additive.ofMul u : Additive Ωˣ) =
      Additive.ofMul (galUnitsHom K Ω g (y ^ q)) - Additive.ofMul (y ^ r) +
        Additive.ofMul (y ^ s) := by
  apply Additive.toMul.injective
  simp only [natCast_zsmul, toMul_nsmul, toMul_add, toMul_sub, toMul_ofMul]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_div_eq_div_val,
    coe_galUnitsHom_apply, map_pow, hg]
  rw [hu, pow_identity y.ne_zero (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]) h, hk]

theorem unramifiedDegree_liftNormal_localArtinMap {K Ω : Type} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]
    {a : Kˣ} (ha : ord (a : K) = 1) :
    unramifiedDegree K Ω ((localArtinMap K Ω a).liftNormal Ω) = Multiplicative.ofAdd 1 := by
  rw [← restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff]
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes ((localArtinMap K Ω a).liftNormal Ω)
    (maximalUnramifiedExtension K Ω) y
  have h2 := AlgEquiv.liftNormal_commutes (localArtinMap K Ω a) Ω
    ⟨(y : Ω), maximalUnramifiedExtension_le_maximalAbelianExtension y.2⟩
  have h3 := localArtinMap_uniformizer_apply (Ω := Ω) ha y.2
  simp only [IntermediateField.algebraMap_apply] at h1 h2
  rw [h1, h2]
  exact h3

theorem inv_kummerCup : ∀ (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (ζ y : Ωˣ) (a : Kˣ), ζ ^ n = 1 → ord (a : K) = 1 → (y : Ω) ^ n = algebraMap K Ω a → ∀ (κ χ : Gal(Ω/K) → ZMod n), (∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → Continuous χ → (∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1) → ∀ x : cocycles (galUnits.{0} K Ω) 2, (∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = Additive.ofMul (ζ ^ (κ (s 0) * χ (s 1)).val)) → brauerInv K Ω (cohomologyπ _ 2 x) = - zmodToQZ n 1 := by
  intro K Ω _ _ _ _ _ _ _ _ _ _ _ n _ ζ y a hζ hord hy κ χ hκ hadd hcont hdeg x hx
  have hlc : IsLocallyConstant χ := (IsLocallyConstant.iff_continuous χ).2 hcont
  let ψ : Additive Gal(Ω/K) →ₜ+ QZ :=
    { toFun := fun σ => zmodToQZ n (χ (Additive.toMul σ))
      map_zero' := by
        have h1 : χ 1 = 0 := by simpa using hadd 1 1
        simp [h1]
      map_add' := fun σ τ => by simp [hadd]
      continuous_toFun :=
        ((hlc.comp_continuous continuous_toMul).comp (zmodToQZ n)).continuous }
  let z : cocycles (galUnitsZ K Ω) 2 := cocyclesULiftInt (galUnits.{0} K Ω) x
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω a)
  let f : Gal(Ω/K) → galUnitsZ K Ω := fun g => Additive.ofMul (y ^ (χ g).val)
  have hf : IsLocallyConstant f := hlc.comp fun c : ZMod n => (Additive.ofMul (y ^ c.val) : galUnitsZ K Ω)
  have hz : cohomologyπ (galUnitsZ K Ω) 2 (z + w) = 0 := by
    refine (cohomologyπ_two_eq_zero_iff _ _).2 ⟨f, hf, fun g h => ?_⟩
    have ez : cochainOf (galUnitsZ K Ω) (cocycleι _ 2 z) ![g, h] =
        Additive.ofMul (ζ ^ (κ g * χ h).val) :=
      (congrFun (cochainOf_cocycleι_cocyclesULiftInt (galUnits.{0} K Ω) x) ![g, h]).trans (hx _)
    set m : ℕ := ((χ g).val + (χ h).val) / n with hm
    have em : charCocycle (charAdd ψ) ((![g, h] : Fin 2 → Gal(Ω/K)) 0, (![g, h] : Fin 2 → Gal(Ω/K)) 1) =
        (m : ℤ) :=
      charCocycle_eq_bockInt χ (charAdd ψ) (fun _ => rfl) g h
    have hsum : (χ g).val + (χ h).val = n * m + (χ (g * h)).val := by
      rw [hadd, ZMod.val_add]
      exact (Nat.div_add_mod _ _).symm
    let u : Ωˣ := Units.map (algebraMap K Ω : K →* Ω) a
    have key := kummer_key ζ y u g hζ (show (u : Ω) = (y : Ω) ^ n from hy.symm) (hκ g)
      (show (κ g * χ h).val = ((κ g).val * (χ h).val) % n from ZMod.val_mul _ _) hsum
    rw [map_add, cochainOf_add, Pi.add_apply, ez, hwc, em]
    exact key
  have e1 : cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2 (cohomologyπ _ 2 x) =
      cohomologyπ (galUnitsZ K Ω) 2 z :=
    cohomologyULiftIntAddEquiv_cohomologyπ' _ x
  have e2 : brauerInv K Ω (cohomologyπ _ 2 x) = brauerInvZ K Ω (cohomologyπ (galUnitsZ K Ω) 2 z) := by
    rw [← e1, brauerInvZ_cohomologyULiftIntAddEquiv]
  have e3 : cohomologyπ (galUnitsZ K Ω) 2 z + galCupClass K Ω ψ a = 0 := by
    rw [galCupClass, ← hw, ← map_add]
    exact hz
  have e4 := brauerInvZ_galCupClass_liftNormal ψ a
  have e5 : ψ (Additive.ofMul ((localArtinMap K Ω a).liftNormal Ω)) = zmodToQZ n 1 := by
    change zmodToQZ n (χ ((localArtinMap K Ω a).liftNormal Ω)) = _
    rw [hdeg _ (unramifiedDegree_liftNormal_localArtinMap hord)]
  have e6 := congrArg (brauerInvZ K Ω) e3
  rw [map_add, map_zero, e4, e5] at e6
  rw [e2]
  exact eq_neg_of_add_eq_zero_left e6

end GlobalTheory.CompanionTheory.KummerCupInv
