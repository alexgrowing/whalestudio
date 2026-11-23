import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen

noncomputable section

open ValuativeRel Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace GlobalTheory.GaussNonvanish

section Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def rep {c : ℕ} (y : Res k c) : k := ((Quotient.out y : 𝒪[k]) : k)

theorem rep_le_one {c : ℕ} (y : Res k c) : valuation k (rep y) ≤ 1 := (Quotient.out y).2

theorem mk_eq_mk_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (c : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) a = Ideal.Quotient.mk _ b ↔
      valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd, ← map_pow]
  rfl

theorem val_pow_lt_one {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) : valuation k (ϖ : k) ^ c < 1 := by
  have h : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  exact pow_lt_one' h (by omega)

theorem val_rep_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    valuation k (rep (y : Res k c)) = 1 := by
  have h1 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c) - 1) ≤
      valuation k (ϖ : k) ^ c := by
    have := (mk_eq_mk_iff hϖ c (Quotient.out (y : Res k c) * Quotient.out ((y⁻¹ : (Res k c)ˣ) : Res k c)) 1).1
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Units.mul_inv, map_one])
    simpa [rep] using this
  have h2 : valuation k (rep (y : Res k c) * rep ((y⁻¹ : (Res k c)ˣ) : Res k c)) = 1 := by
    have := (valuation k).map_one_add_of_lt (h1.trans_lt (val_pow_lt_one hϖ hc))
    simpa using this
  rw [map_mul] at h2
  refine le_antisymm (rep_le_one _) ?_
  calc (1 : ValueGroupWithZero k) = _ := h2.symm
    _ ≤ _ := mul_le_of_le_one_right' (rep_le_one _)

theorem rep_ne_zero {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : rep (y : Res k c) ≠ 0 := by
  intro h
  have := val_rep_unit hϖ hc y
  rw [h, map_zero] at this
  exact zero_ne_one this

def uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) : kˣ := Units.mk0 _ (rep_ne_zero hϖ hc y)

@[simp] theorem coe_uRep {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (y : (Res k c)ˣ) :
    (uRep hϖ hc y : k) = rep (y : Res k c) := rfl

theorem psi_congr {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y)
    (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1) {a b : k} (h : valuation k (a - b) ≤ 1) : ψl a = ψl b := by
  rw [show a = b + (a - b) by ring, hadd, hO _ h, mul_one]

theorem nu_congr {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν) {a b : kˣ}
    (hb : valuation k (b : k) = 1) (h : valuation k ((a : k) - b) ≤ valuation k (ϖ : k) ^ c) : ν a = ν b := by
  have hlt : valuation k ((a : k) - b) < valuation k (b : k) := by
    rw [hb]; exact h.trans_lt (val_pow_lt_one hϖ hc1)
  have ha : valuation k (a : k) = 1 := ((valuation k).map_eq_of_sub_lt hlt).trans hb
  have hw : a * b⁻¹ ∈ unitCong (ϖ ^ c) := by
    refine ⟨by simp [ha, hb], ?_⟩
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ b.ne_zero]
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one, Units.val_pow_eq_pow_val, map_pow]
    exact h
  have := hc _ hw
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

end Generic
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open Classical in

def gS (ψl : k → ℂ) (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc : 1 ≤ c) (x : k) : ℂ :=
  ∑ y : (Res k c)ˣ, (((ν (uRep hϖ hc y))⁻¹ : ℂˣ) : ℂ) * ψl (x * rep (y : Res k c) / (ϖ : k) ^ c)

variable {ψl : k → ℂ} (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
  {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
include hadd hO hc

end Sums
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_condLE {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (hν : Continuous fun x : kˣ => (ν x : ℂ)) :
    ∃ e, CondLE ϖ e ν := by
  have hopen : IsOpen {x : kˣ | ‖(ν x : ℂ) - 1‖ < 1 / 2} := isOpen_lt (by fun_prop) continuous_const
  obtain ⟨V, hV, hV'⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.1 hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ Units.val ⁻¹' V := by rw [hV']; simp
    simpa using this
  have h2 : (fun z : k => z + 1) ⁻¹' V ∈ 𝓝 (0 : k) :=
    (hV.preimage (by fun_prop)).mem_nhds (by simpa using h1)
  obtain ⟨s, hs⟩ := exists_cball_subset h2
  obtain ⟨p, hp, hp'⟩ := GlobalTheory.LocLanglands.exists_unit_pow k (ord k s).toNat
  have hsmall : ∀ x ∈ unitCong (ϖ ^ (ord k s).toNat), ‖(ν x : ℂ) - 1‖ < 1 / 2 := fun x hx => by
    have h3 : (x : k) - 1 ∈ GlobalTheory.SplitWeil.cball s := by
      simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq]
      refine hx.2.trans ?_
      rw [Units.val_pow_eq_pow_val, map_pow, hϖ, ← hp, GlobalTheory.LocLanglands.valuation_le_iff_ord, hp']
      exact Int.self_le_toNat _
    have h4 : x ∈ Units.val ⁻¹' V := by simpa using hs h3
    rw [hV'] at h4
    exact h4
  refine ⟨(ord k s).toNat, fun x hx => Units.ext ?_⟩
  refine GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m => ?_
  have := hsmall (x ^ m) (pow_mem hx m)
  rw [map_pow, Units.val_pow_eq_pow_val] at this
  exact this.le

end Main
end GlobalTheory.GaussNonvanish

namespace GlobalTheory.GaussNonvanish
section Place

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldPl {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

theorem val_le_one_iff {F : Type} [Field F] [NumberField F] (v : Pl F) (x : Fv F v) :
    valuation (Fv F v) x ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

end Place
end GlobalTheory.GaussNonvanish
