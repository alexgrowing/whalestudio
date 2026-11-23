import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassField
import GroundTheory.GlobalFields.ComplexMultiplication.IdeleActionQuotient
import GroundTheory.GlobalFields.ComplexMultiplication.HilbertClassFieldArtin
import GroundTheory.GlobalFields.WeilGroups.SignSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IntermediateField IdeleGroup WithZero
open GroundTheory.LocalField (restrictAb le_maximalAbelianExtension maximalAbelianExtension)
open scoped nonZeroDivisors NumberField.AdeleRing

noncomputable section

variable {K : Type} [Field K] [NumberField K]

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

namespace Modulus

def ofNat (m : ℕ) (hm : m ≠ 0) : Modulus K where
  ideal := Ideal.span {(m : 𝓞 K)}
  ideal_ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  real := ∅

theorem ofNat_ideal (m : ℕ) (hm : m ≠ 0) :
    (ofNat (K := K) m hm).ideal = Ideal.span {(m : 𝓞 K)} :=
  rfl

theorem asIdeal_dvd_ofNat_iff (m : ℕ) (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ (ofNat (K := K) m hm).ideal ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [ofNat_ideal, Ideal.dvd_span_singleton]

theorem valued_natCast (m : ℕ) (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((m : K) : v.adicCompletion K) = exp (-((ofNat (K := K) m hm).exponent v : ℤ)) := by
  have hm' : (m : 𝓞 K) ≠ 0 := by exact_mod_cast hm
  rw [valuedAdicCompletion_eq_valuation', show (m : K) = algebraMap (𝓞 K) K (m : 𝓞 K) by simp,
    valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity _ hm']
  rfl

end Modulus

section Symbol

variable [Algebra K ℂ]

theorem ideleSymbol_apply_eq_of_artinMap (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (M : IntermediateField K ℂ) [FiniteDimensional K M] [IsAbelianGalois K M] (z : M) :
    ((ideleSymbol K M s z : M) : ℂ) = σ (z : ℂ) := by
  have hM : M ≤ algebraicClosure K ℂ := le_algebraicClosure K ℂ M
  let e : M ≃ₐ[K] restrict hM := restrictAlgEquiv hM
  have : FiniteDimensional K (restrict hM) := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : IsAbelianGalois K (restrict hM) := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have he : ∀ w : M, (((e w : restrict hM) : algebraicClosure K ℂ) : ℂ) = (w : ℂ) := fun w ↦ rfl
  have h1 := artinMap_apply (restrict hM) (IdeleClassGroup.mk K s) (e z)
  rw [reciprocityMap_mk, ideleSymbol_apply_algEquiv e] at h1
  have h2 := hs ⟨((e z : restrict hM) : algebraicClosure K ℂ), le_maximalAbelianExtension _ (e z).2⟩
  rw [h1] at h2
  rw [← he, h2, he]

end Symbol

section Decomposition

variable [Algebra K ℂ]

theorem exists_eq_diagonal_mul_mul_finiteEmbedding (m : ℕ) (hm : m ≠ 0) (σ : ℂ ≃ₐ[K] ℂ)
    (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hL : (Modulus.ofNat m hm).rayClassField ℂ ≤ L)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    (h𝔓 : IsArithFrobAt (𝓞 K) (σ.restrictNormal L) 𝔓.asIdeal) :
    ∃ (x : Kˣ) (u : IdeleGroup K) (π : (𝔭.adicCompletion K)ˣ),
      u ∈ (Modulus.ofNat m hm).congruenceSubgroup ∧
      toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭 ∧
      s = diagonal K x * u * finiteEmbedding 𝔭 π := by
  classical
  set 𝔪 := Modulus.ofNat (K := K) m hm
  set M := 𝔪.rayClassField ℂ
  have hv : ¬ 𝔭.asIdeal ∣ 𝔪.ideal := by rwa [Modulus.asIdeal_dvd_ofNat_iff]
  set τ : L ≃ₐ[K] L := σ.restrictNormal L
  obtain ⟨w, hw, hfrob⟩ := Elliptic.exists_isArithFrobAt_galRestrict hL 𝔭 𝔓 τ h𝔓
  have : w.asIdeal.LiesOver 𝔭.asIdeal := hw
  have hram := 𝔪.ramificationIdx_rayClassField_eq_one ℂ hv w
  have hI : w.asIdeal.inertia (M ≃ₐ[K] M) = ⊥ := by
    rw [← Subgroup.card_eq_one, natCard_inertia 𝔭 w, hram]
  obtain ⟨π, hπ, -, hπI⟩ := 𝔪.exists_uniformizer_finiteEmbedding_mem_idelesOneMod hv
  have hsym : ideleSymbol K M s = ideleSymbol K M (finiteEmbedding 𝔭 π) := by
    rw [ideleSymbol_finiteEmbedding_eq_arithFrobAt 𝔭 w hram hπ]
    refine IsArithFrobAt.eq_of_inertia_eq_bot hI ?_ (IsArithFrobAt.arithFrobAt _ _ _)
    convert hfrob using 1
    refine AlgEquiv.ext fun z ↦ Subtype.ext ?_
    rw [ideleSymbol_apply_eq_of_artinMap σ s hs M z, Elliptic.galRestrict_apply]
    exact (AlgEquiv.restrictNormal_commutes σ L (inclusion hL z)).symm
  have hker : IdeleClassGroup.mk K (s * (finiteEmbedding 𝔭 π)⁻¹) ∈ (ideleClassNorm K M).range := by
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk, map_mul, map_inv, hsym,
      mul_inv_cancel]
  rw [𝔪.range_ideleClassNorm_rayClassField ℂ] at hker
  obtain ⟨u, hu, huq⟩ := hker
  obtain ⟨x, hx⟩ : u⁻¹ * (s * (finiteEmbedding 𝔭 π)⁻¹) ∈ (diagonal K).range :=
    QuotientGroup.eq.1 huq
  refine ⟨x, u, π, hu, hπI, ?_⟩
  rw [hx, mul_comm (u⁻¹ * _) u, ← mul_assoc u u⁻¹, mul_inv_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one]

variable {m : ℕ} {hm : m ≠ 0} {s : IdeleGroup K} {x : Kˣ} {u : IdeleGroup K}
  {𝔭 : HeightOneSpectrum (𝓞 K)} {π : (𝔭.adicCompletion K)ˣ}

omit [Algebra K ℂ] in

theorem inv_smul_eq_of_eq (hu : u ∈ (Modulus.ofNat m hm).congruenceSubgroup)
    (hπ : toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭)
    (hs : s = diagonal K x * u * finiteEmbedding 𝔭 π) (𝔞 : 𝓘) :
    s⁻¹ • 𝔞 = diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) := by
  have hu' : u⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) = (primeIdealUnit 𝔭)⁻¹ * 𝔞 :=
    smul_eq_self_iff.2 (inv_mem (Modulus.congruenceSubgroup_le_standardOpenSubgroup _ hu))
  have hπ' : (finiteEmbedding 𝔭 π)⁻¹ • 𝔞 = (primeIdealUnit 𝔭)⁻¹ * 𝔞 := by
    rw [IdeleGroup.smul_def, map_inv, hπ]
  rw [hs, mul_inv, mul_inv, mul_smul, mul_smul, hπ', hu', map_inv]

omit [Algebra K ℂ] in

theorem smulQuotient_inv_mk_of_eq (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (hu : u ∈ (Modulus.ofNat m hm).congruenceSubgroup)
    (hπ : toFractionalIdeal (finiteEmbedding 𝔭 π) = primeIdealUnit 𝔭)
    (hs : s = diagonal K x * u * finiteEmbedding 𝔭 π) (𝔞 : 𝓘) {t : K}
    (ht : (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk ((x⁻¹ : K) * t) := by
  classical
  rw [smulQuotient_mk_eq_mk_iff]
  intro v
  rw [localIdeal_smul]
  set S : v.adicCompletion K := (finiteProj v s : v.adicCompletion K) with hSdef
  set W : v.adicCompletion K := (finiteProj v (u * finiteEmbedding 𝔭 π) : v.adicCompletion K) with hWdef
  set X : v.adicCompletion K := ((x : K) : v.adicCompletion K) with hXdef
  have hX0 : X ≠ 0 := by
    refine (Valuation.ne_zero_iff (Valued.v (R := v.adicCompletion K))).1 ?_
    rw [hXdef, valuedAdicCompletion_eq_valuation']
    exact (Valuation.ne_zero_iff _).2 x.ne_zero
  have hW0 : W ≠ 0 := (finiteProj v (u * finiteEmbedding 𝔭 π)).ne_zero
  have hSXW : S = X * W := by
    rw [hSdef, hs, mul_assoc, map_mul, Units.val_mul, coe_finiteProj_diagonal]
  have hc : ((s⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = S⁻¹ := by
    rw [← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]
  refine ⟨(t : v.adicCompletion K) * (1 - W), ?_, ?_⟩
  ·
    have hmv := Modulus.valued_natCast (K := K) m hm v
    have huv := (Modulus.mem_congruenceSubgroup _).1 hu
    have hW : Valued.v (1 - W) ≤ Valued.v ((m : K) : v.adicCompletion K) := by
      rw [hmv]
      by_cases hv : v = 𝔭
      · subst hv
        have he : (Modulus.ofNat (K := K) m hm).exponent v = 0 :=
          ((Modulus.ofNat m hm).exponent_eq_zero_iff v).2
            (by rwa [Modulus.asIdeal_dvd_ofNat_iff])
        rw [he, Nat.cast_zero, neg_zero, exp_zero]
        have hu1 : Valued.v ((finiteProj v u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
          (huv.1 v).1
        have hπ1 : Valued.v (π : v.adicCompletion K) ≤ 1 := by
          have hord : ord v (finiteEmbedding v π) = 1 := by
            rw [← count_toFractionalIdeal, hπ, count_primeIdealUnit, if_pos rfl]
          have := valued_eq_exp_neg_ord v (finiteEmbedding v π)
          rw [hord, ← coe_finiteProj, finiteProj_finiteEmbedding] at this
          rw [this]
          exact exp_le_exp.2 (by norm_num)
        refine (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) ?_)
        rw [hWdef, map_mul, Units.val_mul, map_mul, hu1, one_mul, finiteProj_finiteEmbedding]
        exact hπ1
      · rw [hWdef, map_mul, finiteProj_finiteEmbedding_of_ne hv, mul_one, Valuation.map_sub_swap]
        exact (huv.1 v).2
    rw [SetLike.mem_coe, mem_localIdeal_iff 𝔞.ne_zero, map_mul]
    have hmt : Valued.v (((m : K) * t : K) : v.adicCompletion K) ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (mem_localIdeal_iff 𝔞.ne_zero v).1 (coe_mem_localIdeal v ht)
    rw [adicCompletion.coe_mul, map_mul] at hmt
    calc Valued.v (t : v.adicCompletion K) * Valued.v (1 - W)
        ≤ Valued.v (t : v.adicCompletion K) * Valued.v ((m : K) : v.adicCompletion K) :=
          mul_le_mul_right hW _
      _ = Valued.v ((m : K) : v.adicCompletion K) * Valued.v (t : v.adicCompletion K) := mul_comm _ _
      _ ≤ exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) := hmt
  · have hc' : ((finiteProj v s⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = S⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    have hXi : ((((x : K)⁻¹ : K)) : v.adicCompletion K) = X⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [hXdef, ← adicCompletion.coe_mul, inv_mul_cancel₀ x.ne_zero, adicCompletion.coe_one]
    rw [LinearMap.mulLeft_apply, hc, hc', adicCompletion.coe_mul, hXi, hSXW]
    field_simp

end Decomposition

section Main

variable [Algebra K ℂ]

theorem exists_diagonal_of_isArithFrobAt (m : ℕ) (hm : m ≠ 0) (σ : ℂ ≃ₐ[K] ℂ) (s : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : (m : 𝓞 K) ∉ 𝔭.asIdeal)
    (L : IntermediateField K ℂ) [FiniteDimensional K L] [IsGalois K L]
    (hL : (Modulus.ofNat m hm).rayClassField ℂ ≤ L)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    (h𝔓 : IsArithFrobAt (𝓞 K) (σ.restrictNormal L) 𝔓.asIdeal) :
    ∃ x : Kˣ, ∀ 𝔞 : 𝓘, s⁻¹ • 𝔞 = diagonal K x⁻¹ • ((primeIdealUnit 𝔭)⁻¹ * 𝔞) ∧
      ∀ t : K, (m : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) →
        smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk ((x⁻¹ : K) * t) := by
  obtain ⟨x, u, π, hu, hπ, hsx⟩ :=
    exists_eq_diagonal_mul_mul_finiteEmbedding m hm σ s hs 𝔭 h𝔭 L hL 𝔓 h𝔓
  exact ⟨x, fun 𝔞 ↦ ⟨inv_smul_eq_of_eq hu hπ hsx 𝔞,
    fun t ht ↦ smulQuotient_inv_mk_of_eq h𝔭 hu hπ hsx 𝔞 ht⟩⟩

end Main

theorem mem_diagonal_smul_iff (a : Kˣ) (J : 𝓘) (k : K) :
    k ∈ ((diagonal K a • J : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) ↔
      (a⁻¹ : K) * k ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_diagonal_smul, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, inv_mul_cancel₀ a.ne_zero, one_mul]
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]⟩

@[simp]
theorem coe_primeIdealUnit_inv_mul (𝔭 : HeightOneSpectrum (𝓞 K)) (𝔞 : 𝓘) :
    (((primeIdealUnit 𝔭)⁻¹ * 𝔞 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * 𝔞 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, coe_primeIdealUnit]

end

end GroundTheory.Global
