import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInfMaximalUnramifiedExtension

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup GlobalTheory.PZ.LTExist

namespace GlobalTheory.PMC.LTCont

section Abstract

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem pow_dvd_sub_one {π : 𝒪[K]} (hπ : Irreducible π) {z : ℕ → Ω} (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0)
    (hz : ∀ n, algebraMap K Ω (π : K) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[K] = z n)
    {a : 𝒪[K]} {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : PowerSeries.coeff 1 φ = a)
    (h2 : PowerSeries.C π * φ + φ ^ Nat.card 𝓀[K] =
      PowerSeries.subst (PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] :
        PowerSeries 𝒪[K]) φ) (n : ℕ)
    (h3 : HasSum (fun k => algebraMap K Ω ((PowerSeries.coeff k φ : 𝒪[K]) : K) * z n ^ k) (z n)) :
    π ^ n ∣ a - 1 := by
  have hf := isLubinTateSeries_ltPoly π
  have hit : ∀ m n, Polynomial.aeval (z (n + m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] K)) = z n := by
    intro m
    induction m with
    | zero => intro n; simp [ltPolyIter_zero]
    | succ m ih =>
      intro n
      rw [ltPolyIter_succ, Polynomial.map_comp, Polynomial.aeval_comp,
        show n + (m + 1) = (n + 1) + m by ring, ih, aeval_ltPoly, hz]
  have hroot : ∀ n, Polynomial.aeval (z n) ((ltPolyIter π n).map (algebraMap 𝒪[K] K)) = 0 := by
    intro n
    have := hit n 0
    rwa [zero_add, hz0] at this
  have hval : ∀ n, valuation Ω (z n) < 1 := fun n =>
    valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ n (hroot n)
  have hpoly : ((ltPoly π : Polynomial 𝒪[K]) : PowerSeries 𝒪[K]) =
      PowerSeries.C π * PowerSeries.X + PowerSeries.X ^ Nat.card 𝓀[K] := by
    simp [ltPoly, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow]
  have hφ : φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
    refine eq_lubinTateHom_toPowerSeries hπ hf hf a h0 h1 ?_
    have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h0
    rw [hpoly, ← h2, PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs,
      powerSeries_subst_C_mul_X hs]
    rfl
  have := t2Space_of_isValuativeTopology Ω
  let x : ℕ → IdealPoint Ω (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hval n)
  have hx : ∀ n, π • x (n + 1) = x n := fun n => by
    apply IdealPoint.ext
    rw [lubinTate_uniformizer_smul_val, psEval_polynomial, aeval_ltPoly]
    exact hz n
  have hxp : ∀ m n, π ^ m • x (n + m) = x n := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih => intro n; rw [pow_succ, mul_smul, ← add_assoc, hx, ih]
  have hax : a • x n = x n := by
    apply IdealPoint.ext
    rw [lubinTate_smul_val, ← hφ]
    change psEval φ (fun _ => z n) = z n
    have h4 := hasSum_psEval' (K := K) (σ := Unit) φ (fun _ => z n) (fun _ => hval n)
    let ι : ℕ ≃ (Unit →₀ ℕ) := (Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)).symm
    rw [← ι.hasSum_iff] at h4
    refine h4.unique ?_
    convert h3 using 1
    funext k
    have hk : ι k = Finsupp.single () k := by
      ext
      simp [ι]
    simp only [Function.comp, psTerm, hk, Finsupp.prod_single_index, pow_zero]
    rfl
  by_cases ha : a - 1 = 0
  · rw [ha]; exact dvd_zero _
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  by_cases hm : n ≤ m
  · rw [hu]; exact Dvd.dvd.mul_left (pow_dvd_pow _ hm) _
  exfalso
  have h5 : (a - 1) • x n = 0 := by rw [sub_smul, hax, one_smul, sub_self]
  have h6 : π ^ m • x n = 0 := by
    have : π ^ m = (↑u⁻¹ : 𝒪[K]) * (a - 1) := by rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, mul_smul, h5, smul_zero]
  obtain ⟨r, rfl⟩ : ∃ r, n = 1 + (r + m) := ⟨n - 1 - m, by omega⟩
  have h7 := hxp (r + m) 1
  rw [pow_add, mul_smul, h6, smul_zero] at h7
  exact hz1 (congrArg IdealPoint.val h7).symm

end Abstract

section Padic

variable {l : ℕ} [Fact l.Prime]

attribute [local instance] omRel om_isValuativeTopology om_valuativeExtension finExt_finiteDimensional

theorem norm_sub_one_le {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ} {π : ↥(OL K)} {z : ℕ → Om l}
    (h : LTData K χ π z) (n : ℕ) (g : ↥(GK K)) (hg : (g : GQ l) (z n) = z n) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l) - 1‖ ≤ ‖((π : ↥K.1) : Om l)‖ ^ n := by
  obtain ⟨hπ, hz0, hz1, hz, hact⟩ := h
  obtain ⟨a, ha, φ, ⟨h0, h1, h2⟩, h3⟩ := hact g
  have h3 := h3 n
  rw [hg] at h3
  have hπ' : Irreducible ((intEquiv K).symm π) := (MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ
  obtain ⟨k0, k1, k2⟩ := map_endo (intEquiv K).symm.toRingHom
    (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) h0 h1 h2
  have hd := pow_dvd_sub_one (Ω := Om l) hπ' hz0 hz1 (by rw [card_residueField_eq]; exact hz) k0 k1
    (by rw [card_residueField_eq]; exact k2) n (by simp only [PowerSeries.coeff_map]; exact h3)
  obtain ⟨c, hc⟩ := hd
  have hc' := congrArg (fun y : 𝒪[↥K.1] => ((y : ↥K.1) : Om l)) hc
  have hcn : ‖((c : ↥K.1) : Om l)‖ ≤ 1 :=
    (GlobalTheory.EmbThroughCompletion.mem_OL_iff K _).mp ((mem_integer_iff K _).mp c.2)
  have e : (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l) - 1 = ((π : ↥K.1) : Om l) ^ n * ((c : ↥K.1) : Om l) := by
    rw [← ha]
    push_cast at hc'
    exact hc'
  rw [e, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) hcn

theorem norm_lt_one {K : FinExt l} {π : ↥(OL K)} (hπ : Irreducible π) : ‖((π : ↥K.1) : Om l)‖ < 1 := by
  have hπ' : Irreducible ((intEquiv K).symm π) := (MulEquiv.irreducible_iff (intEquiv K).symm).mpr hπ
  have h := valuation_algebraMap_lt_one_of_irreducible (L := Om l) hπ'
  rw [← map_one (valuation (Om l)), ← (valuation (Om l)).vlt_iff_lt] at h
  have h' : ¬ ((1 : Om l) ≤ᵥ ((π : ↥K.1) : Om l)) := h
  rw [om_vle_iff, norm_one] at h'
  exact not_le.mp h'

theorem continuous_char {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ} {π : ↥(OL K)} {z : ℕ → Om l}
    (h : LTData K χ π z) : Continuous (fun g : ↥(GK K) => ((χ g : (↥K.1)ˣ) : ↥K.1)) := by
  refine continuous_of_continuousAt_one ((Units.coeHom ↥K.1).comp χ) ?_
  rw [ContinuousAt, map_one, Topology.IsInducing.subtypeVal.tendsto_nhds_iff, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_lt_one h.1)
  let E := IntermediateField.adjoin ℚ_[l] ({z n} : Set (Om l))
  have : FiniteDimensional ℚ_[l] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (z n)).isIntegral
  have hopen : IsOpen ((fun g : ↥(GK K) => (g : GQ l)) ⁻¹' (E.fixingSubgroup : Set (GQ l))) :=
    E.fixingSubgroup_isOpen.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds (show (1 : ↥(GK K)) ∈ _ from E.fixingSubgroup.one_mem)] with g hg
  have hfix : (g : GQ l) (z n) = z n :=
    (IntermediateField.mem_fixingSubgroup_iff E _).mp hg _ (IntermediateField.mem_adjoin_simple_self _ _)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (norm_sub_one_le h n g hfix) hn

end Padic

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      Continuous (fun g : ↥(GK K) => ((χ g : (↥K.1)ˣ) : ↥K.1)) ∧
        Continuous (fun g : ↥(GK K) => ((ltChar τ₀ χ g : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ K LL χ π z h τ₀
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  refine ⟨continuous_char h, ?_⟩
  have hτ : Continuous τ₀ := τ₀.toLinearMap.continuous_of_finiteDimensional
  exact hτ.comp (continuous_char h)

end GlobalTheory.PMC.LTCont

end
