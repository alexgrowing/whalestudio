import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogCoordsUnitValueTwoVariableIntegralExpansionStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.SiegLog

theorem supp_fin {R : Type} [Ring R] (θ : ℤ → ℤ) (f : ℤ → R) (h : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k = 0) :
    (Function.support (fun k : ℤ => (θ k : R) * f k)).Finite := by
  obtain ⟨B, hB⟩ := h
  refine (Set.finite_Icc (-(B : ℤ)) B).subset fun k hk => ?_
  by_contra hc
  apply hk
  have : (B : ℤ) < |k| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  simp [hB k this]

end GlobalTheory.SiegLog

namespace GlobalTheory.SiegLog

theorem siegel_logCoords : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (L : ℕ) (ψ : O0 p →+* Ωl) (io : KT X (p ^ L) →+* Ωl), 1 ≤ L → IsReb T L ψ → IsIo X A T j L ψ io → ∀ ι : On p L →ₐ[O0 p] Ωl, IsEmb T L ι →
  ∀ (N c : ℕ) (A₁ a₂ g : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∀ y : KT X (p ^ L), (y : X.K) = sgN X c N (N * p ^ L) (A₁, a₂) →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = io y ∧ Ev ψ (fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0) z z' ∧
    Cong p L (ι α) (-(A₁ : Ωl) * z) ∧ Cong p L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro Ω _ _ _ ε X hj p _ hp2 A hpA Ωl _ _ hclo T j hcusp L ψ io hL hreb hio ι hemb N c A₁ a₂ g ha₂ hNa hN hNp hc hc6 hNA y hy
  obtain ⟨θ, hB, hr0, hcong, hexp, hder, hsm, hunit⟩ := GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion ε X hj p hp2 L N c A₁ a₂ g hL ha₂ hNa hN hNp hc hc6 hNA
  rw [← hy] at hexp hder hunit
  have hζ : j (zt ε p L) = T.ζ L := hcusp.root L
  have hzA : zt ε p L ∈ A := (hcusp.int _).2 (by rw [hζ]; exact GlobalTheory.KumDlog.int_zeta T L)
  have hzA' : (zt ε p L)⁻¹ ∈ A := (hcusp.int _).2 (by rw [map_inv₀, hζ]; exact GlobalTheory.KumDlog.int_zeta_inv T L)
  have hzpow : ∀ m : ℤ, zt ε p L ^ m ∈ A := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem hzA m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem hzA' _
  have hpL : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hcoef : ∀ s : ℚ, (X.exp (y : X.K)).coeff s ∈ A ∧
      (X.exp (y : X.K)).coeff s ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω) := by
    intro s
    by_cases hs : (X.exp (y : X.K)).coeff s = 0
    · rw [hs]; exact ⟨zero_mem _, zero_mem _⟩
    have hden := ((KTExp.mem_KT_iff ε X (p ^ L) hpL (y : X.K)).1 y.2) s hs
    have hsr : s = (((s * ((p ^ L : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ L := by
      have e := Rat.coe_int_num_of_den_eq_one hden
      have hp0 : (p : ℚ) ^ L ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      rw [e, Nat.cast_pow, mul_div_assoc, div_self hp0, mul_one]
    rw [hsr, hexp]
    constructor
    · refine finsum_induction (· ∈ A) (zero_mem _) (fun _ _ => add_mem) fun k => ?_
      exact mul_mem (intCast_mem _ _) (hzpow _)
    · refine finsum_induction (· ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω)) (zero_mem _)
        (fun _ _ => add_mem) fun k => ?_
      refine mul_mem (intCast_mem _ _) (zpow_mem (IntermediateField.subset_adjoin _ _ ?_) _)
      simp
  obtain ⟨x', hEv⟩ := hio.ev y {zt ε p L} hcoef
  obtain ⟨r0, hr0'⟩ := hr0
  set cU : ℤ → Ωl := fun r => j ((X.exp (y : X.K)).coeff ((r : ℚ) / (p : ℚ) ^ L)) with hcU
  set cE : ℤ → Ωl := fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0 with hcE
  have hjexp : ∀ r, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k) := by
    intro r
    simp only [hcU, hexp r]
    rw [map_finsum j (supp_fin (fun k => θ k r) (fun k => zt ε p L ^ (g * k)) (hB r))]
    simp only [map_mul, map_intCast, map_zpow₀, hζ]
  have hcE0 : ∀ r : ℤ, r < 0 → cE r = 0 := by
    intro r hr
    simp [hcE, not_le.2 hr]
  have hcEmem : ∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L} := by
    intro r
    simp only [hcE]
    split_ifs
    · have h1 : j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) ∈ (Subring.closure {zt ε p L}).map j := Subring.mem_map.2 ⟨_, hsm r.toNat, rfl⟩
      rwa [RingHom.map_closure, Set.image_singleton, hζ] at h1
    · exact zero_mem _
  have hjder : ∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := by
    intro r
    have hfin : (Function.support (fun i : ℤ => (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (y : X.K)).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L))).Finite := by
      refine (Set.finite_Icc 0 (r - r0)).subset fun i hi => ?_
      rw [Function.mem_support] at hi
      constructor
      · by_contra h0
        apply hi
        rw [if_neg h0, zero_mul]
      · by_contra h1
        apply hi
        have h2 : ∀ k, θ k (r - i) = 0 := fun k => hr0' k _ (by omega)
        rw [hexp (r - i)]
        simp [h2]
    have hB' : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → k * θ k r = 0 := by
      obtain ⟨B, hb⟩ := hB r
      exact ⟨B, fun k hk => by rw [hb k hk, mul_zero]⟩
    have h := congrArg j (hder r)
    rw [map_neg, map_finsum j (supp_fin (fun k => k * θ k r) (fun k => zt ε p L ^ (g * k)) hB'), map_finsum j hfin] at h
    simp only [map_mul, map_intCast, map_zpow₀, hζ] at h
    rw [h]
    congr 1
    refine finsum_congr fun i => ?_
    simp only [hcE, hcU]
    split_ifs <;> simp
  have hzi : ∀ m : ℤ, IsInt p ((T.ζ L) ^ m) := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta T L) m
    · rw [zpow_negSucc, ← inv_pow]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta_inv T L) _
  obtain ⟨r, m, hrm⟩ := hunit
  have hcu : cU r ≠ 0 ∧ IsInt p (cU r)⁻¹ := by
    have hz0 : (T.ζ L) ^ m ≠ 0 := zpow_ne_zero _ (GlobalTheory.KumDlog.zeta_ne T L)
    rcases hrm with hrm | hrm
    · simp only [hcU, hrm, map_zpow₀, hζ]
      exact ⟨hz0, by rw [← zpow_neg]; exact hzi _⟩
    · simp only [hcU, hrm, map_neg, map_zpow₀, hζ]
      exact ⟨neg_ne_zero.2 hz0, by rw [inv_neg, ← zpow_neg]; exact GlobalTheory.KumDlog.int_neg (hzi _)⟩
  obtain ⟨hx0, hxi⟩ := (GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ωl hclo T L ψ hreb 0 cU (io y) x' hEv).2 ⟨r, hcu.1, hcu.2⟩
  exact GlobalTheory.T.logCoords_unit_value_twoVariableIntegralExpansion p Ωl hclo T L ψ ι hL hreb hemb A₁ g θ cU cE (io y) x' hB ⟨r0, hr0'⟩ hcong hjexp hjder hcE0 hcEmem hEv hx0 hxi

end GlobalTheory.SiegLog
