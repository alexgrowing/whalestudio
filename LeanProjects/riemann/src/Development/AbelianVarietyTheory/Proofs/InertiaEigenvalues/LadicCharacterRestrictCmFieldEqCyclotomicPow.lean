import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DegreeOnePrimeCMFieldOverSplitMaxRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharRestrictMaxRealValEqProdAboveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocalEqOneOfTrivialOnNormsSplitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfieldStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.PolCharRes

theorem val_below_of_degree_one (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E) (s : ℝ)
    (hν : ν.IsAbsPow s) (χ : Formalism.L2.Host.HChar (maximalRealSubfield E))
    (hχ : compNorm E χ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) ∧
      ((χ.val (w.under (𝓞 (maximalRealSubfield E))) : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(2 * s : ℂ)) := by
  have hr : compNorm E (GlobalTheory.PolChar.resReal ν) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    change ν.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
      ν.1 x * ((ν.1 (Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom x))⁻¹)⁻¹
    rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, GlobalTheory.PolChar.ideleConj_eq, inv_inv]
  set ε := χ * (GlobalTheory.PolChar.resReal ν)⁻¹ with hε
  have hεc : compNorm E ε = 1 := by rw [hε, map_mul, map_inv, hχ, hr, mul_inv_cancel]
  have hχe : χ = GlobalTheory.PolChar.resReal ν * ε := by rw [hε, mul_comm χ, mul_inv_cancel_left]
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (maximalRealSubfield E) E).eventually
    (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)] with w hu hf he
  obtain ⟨hsp, hcard, hw'⟩ := GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield E w hf he
  refine ⟨hu, ?_⟩
  have hεv : ε.val (w.under (𝓞 (maximalRealSubfield E))) = 1 := GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split E ε hεc _ hsp _
  rw [hχe, Formalism.L2.Host.HChar.val_mul, hεv, mul_one, GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above E ν _ (fun w' h => ⟨hν.1 w', (hw' w' h).2⟩),
    Units.coe_prod, Finset.prod_congr rfl (fun w' h => by rw [hν.2.1 w', (hw' w' h).1]), Finset.prod_const, hcard,
    ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem restrict_eq_cycBar_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  intro E Ω _ _ _ _ _ _ l _ ι ν s hν ψ hψ k μ hμ m hm
  obtain ⟨hμc, art, n, hart, -, hlad⟩ := hμ
  have hχ : compNorm E (ψ * quadChar E ^ k) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, hψ]
  have hcyc : Continuous (cycBar E Ω l) :=
    (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (ReciprocityTheory.Gal.continuous_cycZ E Ω l)
  rw [← div_eq_one]
  refine GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius E Ω l _ ((hμc.comp (GlobalTheory.T.continuous_restrictScalarsHom_maximalRealSubfield E Ω)).div' (hcyc.zpow m)) ?_
  filter_upwards [val_below_of_degree_one E ν s hν _ hχ, GlobalTheory.HeightCounting.eventually_natCast_notMem E l] with w h1 hl hf he A σ hA hσ
  obtain ⟨hu, hv⟩ := h1 hf he
  set F := maximalRealSubfield E
  have hA' : IsPlaceOver (F := F) A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hσ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (AlgEquiv.restrictScalarsHom F σ) := by
    rw [GlobalTheory.T.absNorm_under_eq_of_inertiaDeg_one F E w hf]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hl (by
    have := (Ideal.mem_comap).1 h
    simpa using this)
  have e1 := hlad.frob_unr hart (Or.inl hl') hu hA' hσ'
  have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ
  rw [MonoidHom.div_apply, div_eq_one]
  apply Units.ext
  rw [MonoidHom.comp_apply, e1, hv]
  have hN : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmC : (-(2 * (s : ℂ))) = (((-m : ℤ)) : ℂ) := by
    have : (2 * (s : ℂ)) = ((m : ℝ) : ℂ) := by rw [hm]; push_cast; ring
    rw [this]; push_cast; ring
  have e3 : ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
    rw [e2]; simp
  rw [hN, hmC, Complex.cpow_intCast, map_zpow₀, map_natCast, ← zpow_neg, neg_neg]
  change _ = (((cycBar E Ω l σ) ^ m : (Qbar l)ˣ) : Qbar l)
  rw [Units.val_zpow_eq_zpow_val, e3]

end GlobalTheory.PolCharRes

end
