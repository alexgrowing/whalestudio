import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GSEqZeroOfLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussUnitsNormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL

noncomputable section

namespace GlobalTheory.GaussDiv

section Finite

theorem exists_int_of_pow_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : 0 < n)
    (hz : z ^ n = 1) (h : z ∈ Set.range σ) : ∃ g : NumberField.RingOfIntegers K, σ g = z := by
  obtain ⟨x, rfl⟩ := h
  have hx : x ^ n = 1 := σ.injective (by rw [map_pow, hz, map_one])
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)
  exact ⟨⟨x, hi⟩, rfl⟩

theorem exists_int_gauss {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] [Fintype Rˣ] (m : Ideal R) (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (χ : Rˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) (t₀ : Rˣ)
    (ht₀ : ∀ x ∈ m, ((t₀ : R) - 1) * x = 0) (hχt₀ : χ t₀ ≠ 1) (hr : ∀ u, χ u ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ Fintype.card R = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = ∑ u : Rˣ, (χ u)⁻¹ * ψ u ∧
      g * g' = (Fintype.card R : NumberField.RingOfIntegers K) := by
  have hN := GlobalTheory.gauss_units_norm_sq m hm ψ hψ χ (map_mul χ) hχ t₀ ht₀ hχt₀
  have h1 : ∀ u, ∃ g : NumberField.RingOfIntegers K, σ g = χ u := fun u =>
    exists_int_of_pow_eq_one σ (Fintype.card_pos (α := Rˣ)) (by rw [← map_pow, pow_card_eq_one, map_one]) (hr u)
  have h2 : ∀ y, ∃ g : NumberField.RingOfIntegers K, σ g = ψ y := fun y => by
    have : ψ y ^ Fintype.card R = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    exact exists_int_of_pow_eq_one σ (Fintype.card_pos (α := R)) this (hζ _ this)
  choose a ha using h1
  choose b hb using h2
  have hinv : ∀ u, χ u⁻¹ = (χ u)⁻¹ := fun u =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hg : σ ((∑ u : Rˣ, a u⁻¹ * b u : NumberField.RingOfIntegers K) : K) = ∑ u : Rˣ, (χ u)⁻¹ * ψ u := by
    simp only [map_sum, map_mul, ha, hb, hinv]
  have hg' : σ ((∑ u : Rˣ, a u * b (-u) : NumberField.RingOfIntegers K) : K) =
      starRingEnd ℂ (∑ u : Rˣ, (χ u)⁻¹ * ψ u) := by
    simp only [map_sum, map_mul, ha, hb]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.inv_eq_conj (hχ z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  refine ⟨_, ∑ u : Rˣ, a u * b (-u), hg, ?_⟩
  apply NumberField.RingOfIntegers.ext
  apply σ.injective
  have e : ∀ x y : NumberField.RingOfIntegers K, σ ((x * y : NumberField.RingOfIntegers K) : K) = σ x * σ y :=
    fun x y => by simp only [map_mul]
  rw [e, hg, hg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  simp

end Finite

section Local

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_res (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem val_rep_sub {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (y : Res k c) (a : 𝒪[k])
    (h : y = Ideal.Quotient.mk _ a) : valuation k (rep y - a) ≤ valuation k (ϖ : k) ^ c :=
  (mk_eq_mk_iff hϖ c (Quotient.out y) a).1 (by rw [Ideal.Quotient.mk_out, h])

open Classical in

theorem exists_int_gS {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ψl : k → ℂ}
    (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
    (hcond : ∀ x : k, (∀ y : k, valuation k y ≤ 1 → ψl (x * y) = 1) → valuation k x ≤ 1)
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
    (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) (hun : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (hr : ∀ x : kˣ, valuation k (x : k) = 1 → (ν x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (resCard k ^ c) = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = gS ψl ν hϖ hc1 1 ∧
      g * g' = (resCard k : NumberField.RingOfIntegers K) ^ c := by
  have hdiv : ∀ a b : k, valuation k (a - b) ≤ valuation k (ϖ : k) ^ c →
      ψl (a / (ϖ : k) ^ c) = ψl (b / (ϖ : k) ^ c) := fun a b h => by
    apply psi_congr hadd hO
    rw [← sub_div, map_div₀, map_pow]
    exact div_le_one_of_le₀ h zero_le'
  have hmul : ∀ x y : Res k c, valuation k (rep (x * y) - rep x * rep y) ≤ valuation k (ϖ : k) ^ c := fun x y =>
    val_rep_sub hϖ (x * y) (Quotient.out x * Quotient.out y)
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])
  let Ψ : AddChar (Res k c) ℂ :=
    { toFun := fun y => ψl (rep y / (ϖ : k) ^ c)
      map_zero_eq_one' := by
        rw [hdiv _ 0 (val_rep_sub hϖ (0 : Res k c) 0 (map_zero _).symm), zero_div]
        exact hO 0 (by simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd, ← add_div]
        exact hdiv _ _ (val_rep_sub hϖ (x + y) (Quotient.out x + Quotient.out y)
          (by rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])) }
  let χ : (Res k c)ˣ →* ℂ :=
    { toFun := fun u => ν (uRep hϖ hc1 u)
      map_one' := by
        rw [nu_congr hϖ hc1 hc (b := 1) (by simp) (val_rep_sub hϖ (1 : Res k c) 1 (map_one _).symm)]
        simp
      map_mul' := fun u w => by
        rw [nu_congr hϖ hc1 hc (b := uRep hϖ hc1 u * uRep hϖ hc1 w)
          (by simp [val_rep_unit hϖ hc1]) (hmul u w)]
        simp }
  have hΨ : ∀ d : Res k c, (∀ x, Ψ (d * x) = 1) → d = 0 := fun d hd => by
    have h3 := hcond (rep d / (ϖ : k) ^ c) fun a ha => by
      rw [← hd (Ideal.Quotient.mk _ ⟨a, ha⟩), div_mul_eq_mul_div]
      exact (hdiv _ _ (val_rep_sub hϖ _ (Quotient.out d * ⟨a, ha⟩) (by rw [map_mul, Ideal.Quotient.mk_out]))).symm
    rw [← Ideal.Quotient.mk_out d, ← map_zero (Ideal.Quotient.mk _)]
    apply (mk_eq_mk_iff hϖ c _ _).2
    have e2 : rep d = rep d / (ϖ : k) ^ c * (ϖ : k) ^ c := by field_simp
    change valuation k (rep d - 0) ≤ _
    rw [sub_zero, e2, map_mul, map_pow]
    exact mul_le_of_le_one_left' h3
  haveI : Nontrivial (Res k c) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (by omega))))
  haveI : IsLocalRing (Res k c) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨u, ⟨hu1, hu2⟩, hν⟩ := hmin
  have hu' : IsUnit (⟨u, hu1.le⟩ : 𝒪[k]) :=
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hu1
  set ub : (Res k c)ˣ := (hu'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).unit with hub_def
  have hub : (ub : Res k c) = Ideal.Quotient.mk _ ⟨u, hu1.le⟩ := rfl
  have ht₀ : ∀ x ∈ IsLocalRing.maximalIdeal (Res k c), ((ub : Res k c) - 1) * x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 fun h => hx
      (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h).map _)
    have hx' : valuation k (a : k) ≤ valuation k (ϖ : k) := by rw [hϖ]; exact le_uniformizer_iff.2 ha
    have hu2' : valuation k ((u : k) - 1) ≤ valuation k (ϖ : k) ^ (c - 1) := by
      simpa [Units.val_pow_eq_pow_val] using hu2
    rw [hub, ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)), ← map_sub, ← map_mul,
      ← map_zero (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))]
    apply (mk_eq_mk_iff hϖ c _ _).2
    change valuation k (((u : k) - 1) * a - 0) ≤ _
    rw [sub_zero, map_mul]
    calc valuation k ((u : k) - 1) * valuation k (a : k) ≤ valuation k (ϖ : k) ^ (c - 1) * valuation k (ϖ : k) :=
          mul_le_mul' hu2' hx'
      _ = valuation k (ϖ : k) ^ c := by rw [← pow_succ]; congr 1; omega
  have hχt₀ : χ ub ≠ 1 := by
    change ((ν (uRep hϖ hc1 ub) : ℂˣ) : ℂ) ≠ 1
    rw [nu_congr hϖ hc1 hc (b := u) hu1 (val_rep_sub hϖ _ _ hub)]
    exact fun h => hν (Units.ext h)
  obtain ⟨g, g', h1, h2⟩ := exists_int_gauss σ (IsLocalRing.maximalIdeal (Res k c))
    (fun x => by simp [IsLocalRing.mem_maximalIdeal]) Ψ hΨ χ (fun u => hun _) ub ht₀ hχt₀
    (fun u => hr _ (val_rep_unit hϖ hc1 u)) (by rwa [card_res])
  refine ⟨g, g', ?_, by rw [h2, card_res, Nat.cast_pow]⟩
  rw [h1]
  unfold gS
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [one_mul, Units.val_inv_eq_inv_val]
  rfl

end Local

end GlobalTheory.GaussDiv

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem GlobalTheory.GaussDiv.gauss_dvd_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  intro F _ _ K _ _ σ ψ v ν hψ hcont hun hc1 hr hζ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hadd : ∀ x y, psiLoc ψ v (x + y) = psiLoc ψ v x * psiLoc ψ v y := fun x y => by
    simp only [psiLoc, map_add]
    exact AddChar.map_add_eq_mul ψ _ _
  have hO : ∀ x : Fv F v, valuation (Fv F v) x ≤ 1 → psiLoc ψ v x = 1 := fun x hx => by
    have := ((hψ 1).2 ((val_le_one_iff v 1).1 (by simp))) x ((val_le_one_iff v x).1 hx)
    rwa [one_mul] at this
  have hcond : ∀ x : Fv F v, (∀ y : Fv F v, valuation (Fv F v) y ≤ 1 → psiLoc ψ v (x * y) = 1) →
      valuation (Fv F v) x ≤ 1 := fun x h =>
    (val_le_one_iff v x).2 ((hψ x).1 fun y hy => h y ((val_le_one_iff v y).2 hy))
  have hne : {c | CondLE (unifAt v) c ν}.Nonempty := exists_condLE hϖ ν hcont
  have hmem : CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) ν := Nat.sInf_mem hne
  have hmin : ∃ u ∈ unitCong (unifAt v ^ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1)), ν u ≠ 1 := by
    have hlt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < sInf {c | CondLE (unifAt v) c ν} := by
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν
      omega
    have h : ¬ CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1) ν := Nat.notMem_of_lt_sInf hlt
    simpa [CondLE] using h
  have hq : GlobalTheory.SplitWeil.resCard (Fv F v) = Ideal.absNorm v.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨g, g', h1, h2⟩ := GlobalTheory.GaussDiv.exists_int_gS σ hadd hO hcond hϖ hc1 hmem hmin hun
    (fun x hx => hr x ((val_le_one_iff v _).1 hx.le)
      ((val_le_one_iff v _).1 (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])))
    (by rwa [hq])
  refine ⟨g, g', ?_, by rw [h2, hq]⟩
  rw [h1]
  unfold gauss gS
  refine Finset.sum_congr rfl fun y _ => ?_
  have hr := rep_ne_zero hϖ hc1 y
  unfold rep at hr
  rw [dif_neg hr, one_mul]
  rfl
