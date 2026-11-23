import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
import GroundTheory.LocalFields.LocalArtinBaseChange
import GroundTheory.LocalFields.ExplicitQp
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTNorm

variable {l : ℕ} [Fact l.Prime]

attribute [-instance] GroundTheory.PAdicHodge.subfield_valuativeRel GroundTheory.PAdicHodge.subfield_compatible GroundTheory.PAdicHodge.subfield_isValuativeTopology GroundTheory.PAdicHodge.subfield_isNontrivial GroundTheory.PAdicHodge.isNonarchimedeanLocalField_intermediateField GroundTheory.PAdicHodge.isNonarchimedeanLocalField_tower GroundTheory.PAdicHodge.valuativeExtension_padic GroundTheory.PAdicHodge.valuativeExtension_intermediateField GroundTheory.PAdicHodge.subfield_isUltrametricDist

theorem unramifiedDegree_eq_one_of_fix (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (g : Om l ≃ₐ[↥K.1] Om l)
    (h : ∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) :
    unramifiedDegree ↥K.1 (Om l) g = 1 := by
  rw [unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, GlobalTheory.CompanionTheory.LTLink.natCast_residue_eq_zero (l := l) (F := ↥K.1), zero_mul]
  exact h _ (GroundTheory.PAdicHodge.mem_unramifiedClosure_of_pow_eq_one (Nat.pos_of_ne_zero hm0)
    (((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hcop).symm) hζm)

theorem exists_norm_unit (K : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (u : 𝒪[↥K.1]ˣ) :
    ∃ v : ℤ_[l]ˣ, ((v : ℤ_[l]) : ℚ_[l]) = Algebra.norm ℚ_[l] ((u : 𝒪[↥K.1]) : ↥K.1) := by
  have hint : ∀ a : 𝒪[↥K.1], ∃ y : ℤ_[l], (y : ℚ_[l]) = Algebra.norm ℚ_[l] (a : ↥K.1) := by
    intro a
    have h1 : IsIntegral ℤ_[l] (a : ↥K.1) :=
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr
        ((GlobalTheory.CompanionTheory.LTHodge.UnitAct.valuation_le_one_iff (a : ↥K.1)).mp a.2)
    have h2 : IsIntegral ℤ_[l] (Algebra.norm ℚ_[l] (a : ↥K.1)) := Algebra.isIntegral_norm ℚ_[l] h1
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    exact ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hint (u : 𝒪[↥K.1])
  obtain ⟨y', hy'⟩ := hint ((u⁻¹ : 𝒪[↥K.1]ˣ) : 𝒪[↥K.1])
  have hm : ((y * y' : ℤ_[l]) : ℚ_[l]) = 1 := by
    rw [PadicInt.coe_mul, hy, hy', ← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]
    simp
  have hm1 : y * y' = 1 := by
    apply Subtype.ext
    exact hm
  exact ⟨⟨y, y', hm1, by rw [mul_comm]; exact hm1⟩, hy⟩

theorem toZModPow_eq_of_pow (a b : ℤ_[l])
    (h : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 →
      ζ ^ (PadicInt.toZModPow n a).val = ζ ^ (PadicInt.toZModPow n b).val) : a = b := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have hl : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hl.ne'⟩
  have : NeZero ((l ^ n : ℕ) : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  obtain ⟨ζ, hζ⟩ : ∃ z : Om l, IsPrimitiveRoot z (l ^ n) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n)
  have h1 := h n ζ hζ.pow_eq_one
  have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
  exact ZMod.val_injective _ h2

theorem mem_maximalAbelian {n : ℕ} {ζ : Om l} (hζ : ζ ^ l ^ n = 1) :
    ζ ∈ maximalAbelianExtension ℚ_[l] (Om l) := by
  rw [GroundTheory.LocalField.Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity l (Om l)]
  exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, hζ⟩

theorem norm_eq_cyclo : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ), IsLTChar K χ →
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  intro l _ K χ hχ _ g hg hfix
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hR : Set.range (algebraMap ↥K.1 (Om l)) = (K.1 : Set (Om l)) := Subtype.range_coe
  obtain ⟨π, hπ, hmain⟩ := GlobalTheory.CompanionTheory.LTHodge.UnitAct.main hχ (F := ↥K.1) hR
  let g' : ↥(GK K) := ⟨g, hg⟩
  let τ : Om l ≃ₐ[↥K.1] Om l := GlobalTheory.CompanionTheory.LTHodge.CharEx.gal K g'
  obtain ⟨u, huχ, hact⟩ := hmain τ g' (fun y => rfl)
  have hdeg : unramifiedDegree ↥K.1 (Om l) τ = 1 := unramifiedDegree_eq_one_of_fix K τ hfix
  have hart := GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia hπ (isLubinTateSeries_ltPoly π) u τ hdeg hact
  obtain ⟨v, hv⟩ := exists_norm_unit K u
  have hχu : ((χ g' : (↥K.1)ˣ) : ↥K.1) = ((u : 𝒪[↥K.1]) : ↥K.1) := Subtype.ext huχ.symm
  change Algebra.norm ℚ_[l] ((χ g' : (↥K.1)ˣ) : ↥K.1) = _
  rw [hχu, ← hv]

  let x : (↥K.1)ˣ := unitsIncl ↥K.1 u⁻¹
  let w : ℚ_[l]ˣ := normUnits ℚ_[l] ↥K.1 x
  have hw : (w : ℚ_[l]) = (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * (l : ℚ_[l]) ^ (0 : ℤ) := by
    have e1 : (w : ℚ_[l]) = Algebra.norm ℚ_[l] ((x : (↥K.1)ˣ) : ↥K.1) := coe_normUnits x
    have e2 : ((x : (↥K.1)ˣ) : ↥K.1) * ((u : 𝒪[↥K.1]) : ↥K.1) = 1 := by
      have h := congrArg (fun c : 𝒪[↥K.1] => (c : ↥K.1)) (Units.inv_mul u)
      simpa [x, unitsIncl] using h
    have e3 : (w : ℚ_[l]) * ((v : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [e1, hv, ← map_mul, e2, map_one]
    have e4 : ((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = 1 := by
      rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
    rw [zpow_zero, mul_one]
    calc (w : ℚ_[l]) = (w : ℚ_[l]) * (((v : ℤ_[l]) : ℚ_[l]) * (((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) := by
          rw [e4, mul_one]
      _ = _ := by rw [← mul_assoc, e3, one_mul]
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (localReciprocityLimit ℚ_[l] (Om l) w)
  have key : ∀ (n : ℕ) (ζ : Om l), ζ ^ l ^ n = 1 → g ζ = σ ζ := by
    intro n ζ hζ
    have hy := mem_maximalAbelian hζ
    have h1 := hart ζ (maximalAbelianExtension_le_restrictScalars K.1 hy)
    have h2 := localArtinMap_apply_of_mem K.1 x hy
    have h3 : localArtinMap ℚ_[l] (Om l) (normUnits ℚ_[l] ↥K.1 x) =
        topologicalAbelianizationEquiv ℚ_[l] (Om l) (σ : TopologicalAbelianization (Om l ≃ₐ[ℚ_[l]] Om l)) := by
      rw [localArtinMap_apply]
      exact congrArg _ hσ.symm
    rw [h3, topologicalAbelianizationEquiv_mk_apply] at h2
    exact h1.symm.trans h2
  have hfin : (v : ℤ_[l]) = ((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) := by
    refine toZModPow_eq_of_pow _ _ fun n ζ hζ => ?_
    have h1 := GroundTheory.PAdicHodge.cycloChar_spec (K := ⊥) (Formalism.Per6.toBot g) hζ
    have h2 := GroundTheory.LocalField.Padic.apply_of_pow_eq_one_of_prime_pow l w v⁻¹ 0 hw hσ hζ
    rw [inv_inv] at h2
    rw [← h2, ← key n ζ hζ]
    exact h1
  rw [hfin]

end GlobalTheory.CompanionTheory.LTNorm
