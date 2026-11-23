import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import GroundTheory.GlobalFields.ComplexMultiplication.JugendtraumGalois
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Imports
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept

set_option autoImplicit false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField Module IsDedekindDomain IntermediateField WeierstrassCurve GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Global.IdeleGroup GroundTheory.Arith.Abelian
open GroundTheory.LocalField (maximalAbelianExtension)
open GlobalTheory.FieldSize IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.WeberRay

variable {K : Type} [Field K] [NumberField K]

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem idealLattice_one [Algebra K ℂ] (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) :
    idealLattice (algebraMap K ℂ) (((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K)) = L.lattice := by
  ext z
  rw [mem_idealLattice, hL, Units.val_one]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩, rfl⟩

theorem isShortForm_curve (L : PeriodPair) : IsShortForm (weierstrassCurve L) := ⟨rfl, rfl, rfl⟩

theorem isShortForm_map {W : WeierstrassCurve ℂ} (h : IsShortForm W) (φ : ℂ →+* ℂ) : IsShortForm (W.map φ) :=
  ⟨by simp [h.a₁_eq], by simp [h.a₂_eq], by simp [h.a₃_eq]⟩

theorem weberValue_curve (L : PeriodPair) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (x : ℂ) :
    weberValue (weierstrassCurve L) x = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * x := by
  rw [weberValue_of_ne_zero (by simpa using h2) (by simpa using h3), weierstrassCurve_Δ]
  simp only [ShortWeierstrass.g₂, ShortWeierstrass.g₃, weierstrassCurve_a₄, weierstrassCurve_a₆, Elliptic.discr]
  congr 2 <;> ring

theorem j_curve (L : PeriodPair) :
    (weierstrassCurve L).j = 1728 * (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', weierstrassCurve_Δ, Elliptic.discr]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, weierstrassCurve_a₁, weierstrassCurve_a₂,
    weierstrassCurve_a₃, weierstrassCurve_a₄]
  ring

theorem weberFunction_toPointHom (L : PeriodPair) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) {z : ℂ} (hz : z ∉ L.lattice) :
    weberFunction (weierstrassCurve L) (toPointHom L z) =
      OnePoint.some (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP z) := by
  change weberFunction (weierstrassCurve L) (toPoint L z) = _
  rw [toPoint_of_notMem hz, weberFunction_some, weberValue_curve L h2 h3]

theorem weberFunction_transport (L : PeriodPair) (φ : ℂ →+* ℂ)
    {f' : ℂ →+ ((weierstrassCurve L).map φ).toAffine.Point}
    (hf' : IsAnalyticUniformization L.lattice f') (t y : ℂ)
    (h : f' y = pointMapRing φ (weierstrassCurve L) (toPointHom L t)) :
    weberFunction (weierstrassCurve L) (toPointHom L y) =
      OnePoint.map φ (weberFunction (weierstrassCurve L) (toPointHom L t)) := by
  rw [← weberFunction_eq_of_isAnalyticUniformization (isShortForm_curve L)
    (isShortForm_map (isShortForm_curve L) φ) (isAnalyticUniformization_toPointHom L) hf' y, h,
    pointMapRing_eq_pointMapOfRingHom, weberFunction_pointMapOfRingHom]

theorem smulQuotient_inv_mk_eq_self {n : ℕ} {hn : n ≠ 0} {u : IdeleGroup K}
    (hu : u ∈ (Modulus.ofNat (K := K) n hn).congruenceSubgroup) (𝔞 : 𝓘) {t : K}
    (ht : (n : K) * t ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :
    smulQuotient u⁻¹ 𝔞 (Submodule.Quotient.mk t) = Submodule.Quotient.mk t := by
  classical
  rw [smulQuotient_mk_eq_mk_iff]
  intro v
  rw [localIdeal_smul]
  set S : v.adicCompletion K := (finiteProj v u : v.adicCompletion K) with hSdef
  have hS0 : S ≠ 0 := (finiteProj v u).ne_zero
  have hc : ((u⁻¹ : IdeleGroup K) : 𝔸[K]).2 v = S⁻¹ := by
    rw [← coe_finiteProj, map_inv, Units.val_inv_eq_inv_val]
  refine ⟨(t : v.adicCompletion K) * (1 - S), ?_, ?_⟩
  · have hmv := Modulus.valued_natCast (K := K) n hn v
    have huv := (Modulus.mem_congruenceSubgroup _).1 hu
    have hW : Valued.v (1 - S) ≤ Valued.v ((n : K) : v.adicCompletion K) := by
      rw [hmv, Valuation.map_sub_swap]
      exact (huv.1 v).2
    rw [SetLike.mem_coe, mem_localIdeal_iff 𝔞.ne_zero, map_mul]
    have hmt : Valued.v (((n : K) * t : K) : v.adicCompletion K) ≤ WithZero.exp (-FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (mem_localIdeal_iff 𝔞.ne_zero v).1 (coe_mem_localIdeal v ht)
    rw [adicCompletion.coe_mul, map_mul] at hmt
    calc Valued.v (t : v.adicCompletion K) * Valued.v (1 - S)
        ≤ Valued.v (t : v.adicCompletion K) * Valued.v ((n : K) : v.adicCompletion K) :=
          mul_le_mul_right hW _
      _ = Valued.v ((n : K) : v.adicCompletion K) * Valued.v (t : v.adicCompletion K) := mul_comm _ _
      _ ≤ _ := hmt
  · have hc' : ((finiteProj v u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = S⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [LinearMap.mulLeft_apply, hc, hc']
    field_simp

theorem diagonal_mul_mem_congruenceSubgroup {n : ℕ} (hn : n ≠ 0) {u : IdeleGroup K}
    (hu : u ∈ standardOpenSubgroup K) (ε : (𝓞 K)ˣ) {y : K}
    (h : smulQuotient u⁻¹ (1 : 𝓘) (Submodule.Quotient.mk (n : K)⁻¹) = Submodule.Quotient.mk y)
    (hy : y - algebraMap (𝓞 K) K ε * (n : K)⁻¹ ∈ ((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K)) :
    diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε) * u ∈ (Modulus.ofNat (K := K) n hn).congruenceSubgroup := by
  classical
  have hu1 : u⁻¹ • (1 : 𝓘) = 1 := smul_eq_self_iff.2 (inv_mem hu)
  rw [smulQuotient_mk_eq_mk_iff] at h
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  have hone : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      x ∈ localIdeal (((1 : 𝓘)) : FractionalIdeal (𝓞 K)⁰ K) v ↔ Valued.v x ≤ 1 := fun v x => by
    rw [mem_localIdeal_iff (Units.ne_zero _), Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  rw [Modulus.mem_congruenceSubgroup]
  refine ⟨fun v => ?_, fun w hw => absurd hw (Set.notMem_empty _)⟩
  have huv : Valued.v ((finiteProj v u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
    (((Modulus.mem_congruenceSubgroup _).1 (Modulus.congruenceSubgroup_one (K := K) ▸ hu)).1 v).1
  have h1 := h v
  rw [hu1, hone] at h1
  have h2 := (hone v _).1 (coe_mem_localIdeal v hy)
  have hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k := fun k ↦ by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  set S : v.adicCompletion K := (finiteProj v u : v.adicCompletion K) with hSdef
  set E : v.adicCompletion K := algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K ε) with hEdef
  set N : v.adicCompletion K := algebraMap K (v.adicCompletion K) (n : K) with hNdef
  have hS0 : S ≠ 0 := (finiteProj v u).ne_zero
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    exact (map_ne_zero _).2 hn'
  have hE : Valued.v E = 1 := by
    rw [hEdef, ← hc, valuedAdicCompletion_eq_valuation']
    have a := v.valuation_le_one (K := K) (ε : 𝓞 K)
    have b := v.valuation_le_one (K := K) ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
    have c : v.valuation K (algebraMap (𝓞 K) K ε) * v.valuation K (algebraMap (𝓞 K) K ((ε⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    exact le_antisymm a (by
      calc (1 : WithZero (Multiplicative ℤ)) = _ := c.symm
        _ ≤ v.valuation K (algebraMap (𝓞 K) K ε) * 1 := mul_le_mul_right b _
        _ = _ := mul_one _)
  have hNv : Valued.v N = WithZero.exp (-((Modulus.ofNat (K := K) n hn).exponent v : ℤ)) := by
    rw [hNdef, ← hc]
    exact Modulus.valued_natCast (K := K) n hn v
  have hfin : ((finiteProj v u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = S⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [hfin, hc, hc, map_inv₀] at h1
  rw [hc, map_sub, map_mul, map_inv₀] at h2
  have h3 : Valued.v ((S⁻¹ - E) * N⁻¹) ≤ 1 := by
    have e : (S⁻¹ - E) * N⁻¹ = (S⁻¹ * N⁻¹ - algebraMap K (v.adicCompletion K) y) +
        (algebraMap K (v.adicCompletion K) y - E * N⁻¹) := by ring
    rw [e]
    exact Valuation.map_add_le _ h1 h2
  have h4 : Valued.v (S⁻¹ - E) ≤ Valued.v N := by
    rw [map_mul, map_inv₀] at h3
    have hNv0 : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).2 hN0
    calc Valued.v (S⁻¹ - E) = Valued.v (S⁻¹ - E) * (Valued.v N)⁻¹ * Valued.v N := by
          rw [mul_assoc, inv_mul_cancel₀ hNv0, mul_one]
      _ ≤ 1 * Valued.v N := mul_le_mul_left h3 _
      _ = _ := one_mul _
  have hx : ((finiteProj v (diagonal K (Units.map (algebraMap (𝓞 K) K).toMonoidHom ε) * u) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = E * S := by
    rw [map_mul, Units.val_mul, coe_finiteProj_diagonal, hc]
    rfl
  rw [mem_unitsLevel, hx, map_mul, hE, huv, one_mul]
  refine ⟨rfl, ?_⟩
  have e : E * S - 1 = -S * (S⁻¹ - E) := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, huv, one_mul, ← hNv]
  exact h4

theorem isCyclotomic_of_root {k F : Type} [Field k] [Field F] [Algebra k F] (h2 : Module.finrank k F = 2) {n : ℕ}
    [NeZero n] (hirr : Irreducible (Polynomial.cyclotomic n k))
    (hn : n.totient = 2) {ζ : F} (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} k F := by
  have : FiniteDimensional k F := Module.finite_of_finrank_eq_succ h2
  have h := hζ.intermediateField_adjoin_isCyclotomicExtension k
  have e : IntermediateField.adjoin k {ζ} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IsCyclotomicExtension.finrank (n := n) _ hirr, hn,
      IntermediateField.finrank_top', h2]
  exact IsCyclotomicExtension.equiv _ _ _ ((IntermediateField.equivOfEq e).trans IntermediateField.topEquiv)

theorem mem_of_invariant [Algebra K ℂ] (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z)
    (m : ℂ) (hm0 : m ≠ 0) (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) :
    ∃ a : K, algebraMap K ℂ a = m := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨1, by simp⟩)
  rw [e, _root_.mul_one, hL] at this
  obtain ⟨s, rfl⟩ := this
  exact ⟨_, rfl⟩

theorem g_ne_zero [Algebra K ℂ] (hK : finrank ℚ K = 2) (hd : NumberField.discr K < -4) (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) : L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 := by
  constructor
  · intro h
    have hz := Complex.isPrimitiveRoot_exp 3 (by norm_num)
    obtain ⟨a, ha⟩ := mem_of_invariant L hL _ (hz.ne_zero (by norm_num)) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, hz.pow_eq_one]; simp)
    rw [← ha] at hz
    have hz' : IsPrimitiveRoot a 3 := IsPrimitiveRoot.of_map_of_injective (f := algebraMap K ℂ) hz
      (algebraMap K ℂ).injective
    have := isCyclotomic_of_root hK (n := 3) (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by decide) hz'
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have e := IsCyclotomicExtension.Rat.discr_prime 3 K
    norm_num at e
    omega
  · intro h
    have hz := Complex.isPrimitiveRoot_exp 4 (by norm_num)
    obtain ⟨a, ha⟩ := mem_of_invariant L hL _ (hz.ne_zero (by norm_num))
      (by rw [hz.pow_eq_one]; simp) (by simp [h])
    rw [← ha] at hz
    have hz' : IsPrimitiveRoot a (2 ^ 2) := IsPrimitiveRoot.of_map_of_injective (f := algebraMap K ℂ) hz
      (algebraMap K ℂ).injective
    have := isCyclotomic_of_root hK (n := 2 ^ 2) (Polynomial.cyclotomic.irreducible_rat (by norm_num)) (by decide) hz'
    have e := IsCyclotomicExtension.Rat.discr_prime_pow_succ 2 1 K
    norm_num at e
    omega
section Main

variable [Algebra K ℂ] [IsTotallyComplex K] (hK : finrank ℚ K = 2)

include hK in

theorem weberSet_fixed (hd : NumberField.discr K < -4) (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) {n : ℕ} (hn : n ≠ 0)
    (σ : ℂ ≃ₐ[K] ℂ) (u : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K u) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (hu : u ∈ (Modulus.ofNat (K := K) n hn).congruenceSubgroup) : ∀ w ∈ weberSet L n, σ w = w := by
  classical
  obtain ⟨h2, h3⟩ := g_ne_zero hK hd L hL
  have hone := idealLattice_one L hL
  have hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K))
      (toPointHom L) := by rw [hone]; exact isAnalyticUniformization_toPointHom L
  obtain ⟨f', ⟨hf', hp⟩, -⟩ := main_theorem_complexMultiplication hK σ u hs 1 hf
  have hu1 : u⁻¹ • (1 : 𝓘) = 1 :=
    smul_eq_self_iff.2 (inv_mem (Modulus.congruenceSubgroup_le_standardOpenSubgroup _ hu))
  rw [hu1, hone] at hf'
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  rintro w (rfl | ⟨z, hz, hzn, rfl⟩)
  · have hj := j_eq_of_isAnalyticUniformization (isAnalyticUniformization_toPointHom L) hf'
    rw [map_j, j_curve] at hj
    have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
    have e1 : ((σ : ℂ →+* ℂ)) (1728 : ℂ) = 1728 := map_ofNat _ _
    rw [map_mul, e1] at hj
    exact mul_left_cancel₀ h1728 hj
  · obtain ⟨a, rfl⟩ := (hL z).1 hz
    set t : K := (a : K) / n with ht
    have hzt : algebraMap K ℂ (a : K) / n = algebraMap K ℂ t := by simp [ht]
    rw [hzt] at hzn ⊢
    have hq := smulQuotient_inv_mk_eq_self hu (1 : 𝓘) (t := t) (by
      rw [ht, mul_div_cancel₀ _ hn', Units.val_one]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    have e := weberFunction_transport L (σ : ℂ →+* ℂ) hf' _ _ (hp t t hq)
    rw [weberFunction_toPointHom L h2 h3 hzn] at e
    exact (Option.some_injective _ e).symm

include hK in

theorem mk_mem_of_fixed (hd : NumberField.discr K < -4) (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) {n : ℕ} (hn : n ≠ 0)
    (σ : ℂ ≃ₐ[K] ℂ) (u : IdeleGroup K)
    (hs : ∀ x : maximalAbelianExtension K (algebraicClosure K ℂ),
      ((artinMap K (algebraicClosure K ℂ) (IdeleClassGroup.mk K u) x : algebraicClosure K ℂ) : ℂ) =
        σ ((x : algebraicClosure K ℂ) : ℂ))
    (hu : u ∈ standardOpenSubgroup K) (hw : ∀ w ∈ weberSet L n, σ w = w) :
    IdeleClassGroup.mk K u ∈ (Modulus.ofNat (K := K) n hn).congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  classical
  obtain ⟨h2, h3⟩ := g_ne_zero hK hd L hL
  have hone := idealLattice_one L hL
  have hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K))
      (toPointHom L) := by rw [hone]; exact isAnalyticUniformization_toPointHom L
  obtain ⟨f', ⟨hf', hp⟩, -⟩ := main_theorem_complexMultiplication hK σ u hs 1 hf
  have hu1 : u⁻¹ • (1 : 𝓘) = 1 := smul_eq_self_iff.2 (inv_mem hu)
  rw [hu1, hone] at hf'
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (smulQuotient u⁻¹ (1 : 𝓘) (Submodule.Quotient.mk (n : K)⁻¹))
  have e := weberFunction_transport L (σ : ℂ →+* ℂ) hf' _ _ (hp _ y hy.symm)
  have hfix : OnePoint.map (σ : ℂ →+* ℂ) (weberFunction (weierstrassCurve L) (toPointHom L (algebraMap K ℂ (n : K)⁻¹))) =
      weberFunction (weierstrassCurve L) (toPointHom L (algebraMap K ℂ (n : K)⁻¹)) := by
    by_cases hm : algebraMap K ℂ (n : K)⁻¹ ∈ L.lattice
    · have : toPointHom L (algebraMap K ℂ (n : K)⁻¹) = 0 := by
        change toPoint L _ = 0
        exact toPoint_of_mem hm
      rw [this]
      rfl
    · have hz1 : (1 : ℂ) ∈ L.lattice := (hL 1).2 ⟨1, by simp⟩
      have hv : algebraMap K ℂ (n : K)⁻¹ = 1 / (n : ℂ) := by simp
      rw [weberFunction_toPointHom L h2 h3 hm]
      have hw' := hw _ (Or.inr ⟨1, hz1, hv ▸ hm, rfl⟩)
      rw [← hv] at hw'
      exact congrArg OnePoint.some hw'
  rw [hfix] at e
  obtain ⟨ξ, hξ⟩ := (weberFunction_eq_iff (isShortForm_curve L) _ _).1 e.symm
  obtain ⟨ε, hε⟩ := exists_unit_automorphismPoint_eq hK 1 hf ξ
  rw [hε] at hξ
  have hmem : y - algebraMap (𝓞 K) K ε * (n : K)⁻¹ ∈ ((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) := by
    apply mem_of_map_mem_idealLattice (algebraMap K ℂ)
    rw [← hf.map_eq_zero_iff, map_sub (algebraMap K ℂ), map_mul (algebraMap K ℂ), map_sub (toPointHom L), hξ, sub_self]
  refine ⟨_, diagonal_mul_mem_congruenceSubgroup hn hu ε hy.symm hmem, ?_⟩
  refine QuotientGroup.eq.2 ⟨(Units.map (algebraMap (𝓞 K) K).toMonoidHom ε)⁻¹, ?_⟩
  rw [mul_inv, mul_assoc, inv_mul_cancel, mul_one, map_inv]

end Main

section Final

variable [Algebra K ℂ] [IsTotallyComplex K] (hK : finrank ℚ K = 2)

include hK in

theorem adjoin_weberSet_eq_rayClassField (hd : NumberField.discr K < -4) (L : PeriodPair)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) {n : ℕ} (hn : n ≠ 0) :
    IntermediateField.adjoin K (weberSet L n) = (Modulus.ofNat (K := K) n hn).rayClassField ℂ := by
  refine eq_of_forall_algEquiv fun σ => ?_
  obtain ⟨s, hs⟩ := exists_idele_artinMap_eq σ
  have hone := idealLattice_one L hL
  have hf : IsAnalyticUniformization (idealLattice (algebraMap K ℂ) ((1 : 𝓘) : FractionalIdeal (𝓞 K)⁰ K))
      (toPointHom L) := by rw [hone]; exact isAnalyticUniformization_toPointHom L
  constructor
  · intro h
    have hW : ∀ w ∈ weberSet L n, σ w = w := fun w hw => h w (IntermediateField.subset_adjoin K _ hw)
    have hj : σ (weierstrassCurve L).j = (weierstrassCurve L).j := by
      rw [j_curve, map_mul, map_ofNat, hW _ (Or.inl rfl)]
    obtain ⟨u, hu, e⟩ := mk_mem_map_standardOpenSubgroup_of_apply_j_eq hK σ s hs 1 hf hj
    rw [forall_rayClassField_apply_eq_iff σ s hs, ← e]
    exact mk_mem_of_fixed hK hd L hL hn σ u (by rw [e]; exact hs) hu hW
  · intro h
    obtain ⟨u, hu, e⟩ := (forall_rayClassField_apply_eq_iff σ s hs _).1 h
    exact forall_adjoin_apply_eq σ (weberSet_fixed hK hd L hL hn σ u (by rw [e]; exact hs) hu)

end Final

theorem valuation_natCast (n : ℕ) (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (n : K) = WithZero.exp (-((Modulus.ofNat (K := K) n hn).exponent v : ℤ)) := by
  rw [← Modulus.valued_natCast (K := K) n hn v, valuedAdicCompletion_eq_valuation']

theorem primeClass_eq_one_iff (n : ℕ) (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ (Modulus.ofNat (K := K) n hn).ideal) :
    (Modulus.ofNat (K := K) n hn).primeClass hv = 1 ↔
      ∃ π : 𝓞 K, v.asIdeal = Ideal.span {π} ∧ π - 1 ∈ Ideal.span {(n : 𝓞 K)} := by
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  rw [Modulus.primeClass, QuotientGroup.eq_one_iff, Modulus.mem_principalRay]
  constructor
  · rintro ⟨a, ha, e⟩
    have e' : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      have := congrArg (Units.val) e
      rwa [coe_toPrincipalIdeal, coe_primeIdealUnit] at this
    have hmem : (a : K) ∈ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← e']
      exact FractionalIdeal.mem_spanSingleton_self _ _
    obtain ⟨π, -, hπ⟩ := (FractionalIdeal.mem_coeIdeal _).1 hmem
    refine ⟨π, ?_, ?_⟩
    · apply FractionalIdeal.coeIdeal_injective (K := K)
      show (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {π} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [← e', FractionalIdeal.coeIdeal_span_singleton, hπ]
    · have hint : ((π : K) - 1) / n ∈ (algebraMap (𝓞 K) K).range := by
        refine HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun w => ?_
        have h1 : w.valuation K ((π : K) - 1) ≤ WithZero.exp (-((Modulus.ofNat (K := K) n hn).exponent w : ℤ)) := by
          by_cases hw : w.asIdeal ∣ (Modulus.ofNat (K := K) n hn).ideal
          · have := ((Modulus.ofNat (K := K) n hn).mem_rayUnits.1 ha).1 w hw
            rwa [← hπ] at this
          · rw [((Modulus.ofNat (K := K) n hn).exponent_eq_zero_iff w).2 hw]
            simpa using (w.valuation_le_one (K := K) (π - 1))
        rw [map_div₀, valuation_natCast n hn w]
        exact div_le_one_of_le₀ h1 zero_le'
      obtain ⟨b, hb⟩ := hint
      rw [Ideal.mem_span_singleton']
      refine ⟨b, RingOfIntegers.coe_injective ?_⟩
      have : (b : K) * n = (π : K) - 1 := by
        change algebraMap (𝓞 K) K b * n = _
        rw [hb]
        field_simp
      simpa using this
  · rintro ⟨π, hp, hc⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hc
    have hπ0 : (π : K) ≠ 0 := by
      intro h0
      have : π = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this] at hp
      exact v.ne_bot (by simpa using hp)
    refine ⟨Units.mk0 (π : K) hπ0, ?_, ?_⟩
    · refine (Modulus.ofNat (K := K) n hn).mem_rayUnits.2 ⟨fun w _ => ?_, fun w hw => absurd hw (Set.notMem_empty _)⟩
      have e : ((Units.mk0 (π : K) hπ0 : Kˣ) : K) - 1 = (c : K) * n := by
        rw [Units.val_mk0]
        have := congrArg (algebraMap (𝓞 K) K) hc
        simpa using this.symm
      rw [e, map_mul, valuation_natCast n hn w]
      exact mul_le_of_le_one_left' (w.valuation_le_one (K := K) c)
    · apply Units.ext
      rw [coe_toPrincipalIdeal]
      show _ = ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      rw [coe_primeIdealUnit, hp, FractionalIdeal.coeIdeal_span_singleton]
      rfl

theorem finite_mem {a : 𝓞 K} (ha : a ≠ 0) : {𝔭 : HeightOneSpectrum (𝓞 K) | a ∈ 𝔭.asIdeal}.Finite := by
  have h : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  refine (Ideal.finite_factors h).subset ?_
  intro 𝔭 h𝔭
  exact Ideal.dvd_span_singleton.2 h𝔭

section Bridge

variable [Algebra K ℂ]

theorem ncard_rayClassField_iff (n : ℕ) (hn : n ≠ 0) (𝔭 : HeightOneSpectrum (𝓞 K)) (hp : (n : 𝓞 K) ∉ 𝔭.asIdeal) :
    {Q : HeightOneSpectrum (𝓞 ((Modulus.ofNat (K := K) n hn).rayClassField ℂ)) |
        Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 ((Modulus.ofNat (K := K) n hn).rayClassField ℂ))) = 𝔭.asIdeal}.ncard =
      Module.finrank K ((Modulus.ofNat (K := K) n hn).rayClassField ℂ) ↔
    ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ Ideal.span {(n : 𝓞 K)} := by
  have hv : ¬ 𝔭.asIdeal ∣ (Modulus.ofNat (K := K) n hn).ideal := by
    rwa [Modulus.asIdeal_dvd_ofNat_iff]
  rw [GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver, ← splitsCompletely_iff_ncard_primesOver,
    (Modulus.ofNat (K := K) n hn).splitsCompletely_rayClassField_iff ℂ hv, primeClass_eq_one_iff]

theorem isRay_of_eq {M N : IntermediateField K ℂ} (h : M = N) [NumberField M] [NumberField N] {𝔮 : Ideal (𝓞 K)}
    (hM : IsRay M 𝔮) : IsRay N 𝔮 := by
  subst h
  exact hM

theorem isRay_rayClassField [IsTotallyComplex K] (n : ℕ) (hn : n ≠ 0) :
    IsRay ((Modulus.ofNat (K := K) n hn).rayClassField ℂ) (Ideal.span {(n : 𝓞 K)}) := by
  have hn0 : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hR : GlobalTheory.NT.RayField :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt GlobalTheory.CompanionTheory.Hypotheses₂.globalArtinReciprocity
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K _ hq
  have := hM.1
  let f : M →ₐ[K] ℂ := IsAlgClosed.lift
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  have := h.1
  have hIsRay : IsRay f.fieldRange (Ideal.span {(n : 𝓞 K)}) := h.2
  have hiff : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal →
      ({Q : HeightOneSpectrum (𝓞 f.fieldRange) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 f.fieldRange)) = 𝔭.asIdeal}.ncard =
          Module.finrank K f.fieldRange ↔
        {Q : HeightOneSpectrum (𝓞 ((Modulus.ofNat (K := K) n hn).rayClassField ℂ)) |
          Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 ((Modulus.ofNat (K := K) n hn).rayClassField ℂ))) = 𝔭.asIdeal}.ncard =
          Module.finrank K ((Modulus.ofNat (K := K) n hn).rayClassField ℂ)) := fun 𝔭 hp => by
    rw [ncard_rayClassField_iff n hn 𝔭 hp,
      GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff K f.fieldRange n (Nat.pos_of_ne_zero hn) hIsRay 𝔭 hp]
  have hEq : f.fieldRange = (Modulus.ofNat (K := K) n hn).rayClassField ℂ := by
    apply le_antisymm
    · refine GlobalTheory.Bauer.le_of_finite_split_not_split K ℂ _ _ ((finite_mem hn0).subset ?_)
      rintro 𝔭 ⟨-, h1, h2⟩
      by_contra hp
      exact h2 ((hiff 𝔭 hp).2 h1)
    · refine GlobalTheory.Bauer.le_of_finite_split_not_split K ℂ _ _ ((finite_mem hn0).subset ?_)
      rintro 𝔭 ⟨-, h1, h2⟩
      by_contra hp
      exact h2 ((hiff 𝔭 hp).1 h1)
  exact isRay_of_eq hEq hIsRay

end Bridge

theorem weberRayField : GlobalTheory.Published.WeberRayFieldSt := by
  intro K _ _ _ _ h2 hd L hL n hn
  rw [adjoin_weberSet_eq_rayClassField h2 hd L hL hn.ne']
  exact ⟨inferInstance, inferInstance, isRay_rayClassField n hn.ne'⟩

end GlobalTheory.CompanionTheory.WeberRay
