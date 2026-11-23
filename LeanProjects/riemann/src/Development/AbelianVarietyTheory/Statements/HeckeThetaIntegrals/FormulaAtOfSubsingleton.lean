import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit
import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull

namespace GlobalTheory.RowClaim.Test

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D}

theorem pde_ne_q (h : HidaSetting large₂ R F) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

theorem guard (h : HidaSetting large₂ R F) : Guard R := guard_of_qGuard h.guard

theorem finite_of_tup (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) : Finite T := by
  classical
  have : (Set.univ : Set T) ⊆ insert A.μ0 (R.mu '' (R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((R.twPl).finite_toSet.image _).insert _).subset this)

theorem big_mono {Q Q' : ChP} (h : Big Q) (hQ : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → Q ch → Q' ch) : Big Q' := by
  obtain ⟨a, h⟩ := h
  refine ⟨a, fun ε CF hC => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hC
  exact ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => hQ ch i (h D large₂ e hx Γ Pl0 T A Ks R F s ch i j)⟩

variable {ch : Choice R} {κ κ' : ℂ} {ze ze' : T → D.what₂.LL}

set_option maxHeartbeats 1600000 in

theorem formulaAt_zero_iff : FormulaAt ch 0 (fun _ => 1) ↔ ∀ t (x : A.fam.amb.FR t), x ∈ (A.fam.R t).goodF A.fam.X → ∀ a,
    cTot ch t * psiK ch a (R.Th t (R.jX t x)) = 0 := by
  simp only [FormulaAt, map_one, one_mul, zero_mul, one_pow]
  exact and_iff_right fun _ => ⟨1, one_pos, trivial⟩

set_option maxHeartbeats 1600000 in

theorem formulaAt_of_subsingleton [Subsingleton R.HE.H] (ch : Choice R) : FormulaAt ch 0 fun _ => 1 :=
  formulaAt_zero_iff.2 fun t x _ a => by rw [Subsingleton.elim (R.Th t _) 0, psiK_zero, mul_zero]

set_option maxHeartbeats 1600000 in

theorem formulaAt_normalise (h : FormulaAt ch κ ze) :
    FormulaAt ch ((D.what₂.embLL (ze A.μ0))⁻¹ * κ) (fun t => (ze A.μ0)⁻¹ * ze t) ∧ (ze A.μ0)⁻¹ * ze A.μ0 = 1 := by
  obtain ⟨n, hn, e⟩ := h.1 A.μ0
  have hz : ze A.μ0 ≠ 0 := fun z => by
    rw [z, zero_pow hn.ne'] at e
    exact zero_ne_one e
  refine ⟨⟨fun t => ?_, fun t x hx a => ?_⟩, inv_mul_cancel₀ hz⟩
  · obtain ⟨k, hk, e'⟩ := h.1 t
    refine ⟨n * k, mul_pos hn hk, ?_⟩
    rw [mul_pow, inv_pow, pow_mul, e, one_pow, inv_one, one_mul, mul_comm, pow_mul, e', one_pow]
  · have := h.2 t x hx a
    rw [map_mul, map_inv₀, mul_assoc _ κ, ← this]
    ring

set_option maxHeartbeats 1600000 in

theorem norm_unique (h : FormulaAt ch κ ze) (h' : FormulaAt ch κ' ze') {t : T} {x : A.fam.amb.FR t}
    (hx : x ∈ (A.fam.R t).goodF A.fam.X) {a : Fin ch.n} (h0 : vK ch t x a ≠ 0) : ‖κ‖ = ‖κ'‖ := by
  have n1 : ∀ z : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ‖D.what₂.embLL z‖ = 1 := by
    rintro z ⟨n, hn, e⟩
    exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, e, map_one]) hn.ne'
  have e1 := congrArg norm (h.2 t x hx a)
  have e2 := congrArg norm (h'.2 t x hx a)
  simp only [norm_mul, n1 _ (h.1 t), n1 _ (h'.1 t)] at e1 e2
  exact mul_right_cancel₀ (norm_ne_zero_iff.2 h0) (e1.symm.trans e2)

set_option maxHeartbeats 1600000 in

theorem scalar_ne_zero (hI : InjK) (hC : ConstK) (hF : Formula2K) :
    Big fun {D} _ _ _ _ _ A _ _ _ _ R ch => ch.FieldOK → ∃ κ ze, FormulaAt ch κ ze ∧
      ((∃ t, ∃ x ∈ (A.fam.R t).goodF A.fam.X, R.Th t (R.jX t x) ≠ 0) → κ ≠ 0) := by
  refine big_mono ((hI.and hC).and hF) ?_
  rintro D Γ _ _ Pl0 T A Ks _ _ _ R ch - ⟨⟨h1, h2⟩, h3⟩ hf
  obtain ⟨κ, ze, h⟩ := h3 hf
  refine ⟨κ, ze, h, ?_⟩
  rintro ⟨t, x, hx, h0⟩
  obtain ⟨a, ha⟩ := not_forall.1 fun k => h0 (h1 _ k)
  exact h.ne_zero ((cTot_ne_zero_iff ch t).2 fun i j => (h2 i j t).2) hx ha

theorem ratio_mem (h : RatioK) :
    Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ch.FieldOK → ∀ t, ratio ch t ∈ Set.range D.what₂.embLL := by
  refine big_mono h ?_
  rintro D Γ _ _ Pl0 T A Ks _ _ _ R ch - h hf t
  rw [ratio_eq_prod]
  exact D.what₂.embLL.fieldRange.prod_mem fun i _ => D.what₂.embLL.fieldRange.prod_mem fun j _ => h hf i j t

end GlobalTheory.RowClaim.Test

end
