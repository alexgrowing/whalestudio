import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableDisjoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHighestWeightHarmonicMultiplicityOneCoverin
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFockAct1Diag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionRowCapelliFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliHighestWeightVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointHighestStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleKStableStatement

open scoped TensorProduct

namespace GlobalTheory.LowIrr
open MvPolynomial Formalism.BasicNotions.TH

theorem stable_of_rowOp {P Q R S : ℕ} (x : ℚ) (k k' : ℕ) (h1 : x - cPair R S = k) (h2 : x + cPair R S = k')
    (N : Submodule ℂ (Pol P Q R S)) (hNV : N ≤ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'))
    (hN : ∀ Z : Mat R S, IsKC Z → ∀ f ∈ N, fockAct2 P Q R S Z f ∈ N) :
    (∀ (c d : Fin R), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d w ∈ N) ∧
      ∀ (c d : Fin S), ∀ w ∈ N, GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d w ∈ N := by
  constructor
  · intro c d w hw
    have hp := (GlobalTheory.LowIrr.lowShape P Q R S x k k' h1 h2 w (hNV hw)).1
    have e := (GlobalTheory.T.fock_action_row_capelli_formula P Q R S w hp).1 c d
    have := hN _ (eab_isKC_inl (S := S) c d) w hw
    rw [e] at this
    simpa using N.sub_mem this (N.smul_mem (if c = d then (((P : ℂ) - Q) / 2) else 0) hw)
  · intro c d w hw
    have hp := (GlobalTheory.LowIrr.lowShape P Q R S x k k' h1 h2 w (hNV hw)).1
    have e := (GlobalTheory.T.fock_action_row_capelli_formula P Q R S w hp).2 c d
    have := hN _ (eab_isKC_inr (R := R) c d) w hw
    rw [e] at this
    simpa using N.sub_mem this (N.smul_mem (if c = d then (((Q : ℂ) - P) / 2) else 0) hw)

theorem lowOne_irreducible : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ N : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S), N ≤ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') → (∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z → ∀ f ∈ N, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ N) → N = ⊥ ∨ N = GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  intro P Q R S x k k' _ _ _ _ h1 h2 N hNV hN
  classical
  set V := GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') with hVdef
  have hVh : V ≤ homogeneousSubmodule (Ln P Q R S) ℂ (P * k + Q * k') := fun f hf =>
    (GlobalTheory.LowIrr.lowShape P Q R S x k k' h1 h2 f hf).2
  haveI : FiniteDimensional ℂ V := by
    haveI := GlobalTheory.CompactHarm.finite_homog (σ := Ln P Q R S) (P * k + Q * k')
    exact Submodule.finiteDimensional_of_le hVh
  obtain ⟨hVz, hVy⟩ := stable_of_rowOp x k k' h1 h2 V le_rfl (GlobalTheory.T.low_irreducible_k_stable P Q R S x k k' h1 h2)
  obtain ⟨hNz, hNy⟩ := stable_of_rowOp x k k' h1 h2 N hNV hN

  have hJ : ∀ v ∈ V, (∀ c d : Fin R, c < d → GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d v = 0) →
      (∃ α : Fin R → ℂ, ∀ c, GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c c v = α c • v) →
      (∀ c d : Fin S, c < d → GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d v = 0) →
      (∃ β : Fin S → ℂ, ∀ d, GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) d d v = β d • v) →
      ∃ α β, GlobalTheory.CompactHarm.JointTop (zR P Q R S) (yS P Q R S) (kap P Q k k') α β v := by
    intro v hv hz ⟨α, hα⟩ hy ⟨β, hβ⟩
    have hp := (GlobalTheory.LowIrr.lowShape P Q R S x k k' h1 h2 v hv).1
    obtain ⟨m1, m2, m3⟩ := GlobalTheory.T.capelli_highest_weight_vanishing P Q R S x k k' h1 h2 v ((GlobalTheory.KFixIrr.mem_lowOne x _ v).1 hv).1 hp
    exact ⟨α, β, m1, m2, hz, hα, hy, hβ, m3⟩
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.CompactHarm.jointTop_line (zR P Q R S) (yS P Q R S) (zR_inj P Q R S)
    (yS_inj P Q R S) (zR_ne_yS P Q R S) (zR_or_yS P Q R S) (kap P Q k k')
  by_contra hne
  push_neg at hne
  obtain ⟨hN0, hNV'⟩ := hne
  have hlt : N < V := lt_of_le_of_ne hNV hNV'
  set N' := V ⊓ GlobalTheory.GLDuality.Compl.orth N with hN'def
  have hN'0 : N' ≠ ⊥ := GlobalTheory.GLDuality.Compl.inf_orth_ne_bot V N hlt
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV
  haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le inf_le_left
  have hN'z : ∀ (c d : Fin R), ∀ w ∈ N', GlobalTheory.Capelli.rowOp ℂ (zR P Q R S) c d w ∈ N' := by
    intro c d w hw
    refine ⟨hVz c d w hw.1, GlobalTheory.GLDuality.Compl.mem_orth.2 fun m hm => ?_⟩
    rw [fockF_rowOp]
    exact GlobalTheory.GLDuality.Compl.mem_orth.1 hw.2 _ (hNz d c m hm)
  have hN'y : ∀ (c d : Fin S), ∀ w ∈ N', GlobalTheory.Capelli.rowOp ℂ (yS P Q R S) c d w ∈ N' := by
    intro c d w hw
    refine ⟨hVy c d w hw.1, GlobalTheory.GLDuality.Compl.mem_orth.2 fun m hm => ?_⟩
    rw [fockF_rowOp]
    exact GlobalTheory.GLDuality.Compl.mem_orth.1 hw.2 _ (hNy d c m hm)
  obtain ⟨v, hv, hv0, a1, a2, a3, a4⟩ := GlobalTheory.T.exists_highest_weight_vector_alt P Q R S N inferInstance hN0 hNz hNy
  obtain ⟨v', hv', hv'0, b1, b2, b3, b4⟩ := GlobalTheory.T.exists_highest_weight_vector_alt P Q R S N' inferInstance hN'0 hN'z hN'y
  obtain ⟨α, β, hJv⟩ := hJ v (hNV hv) a1 a2 a3 a4
  obtain ⟨α', β', hJv'⟩ := hJ v' hv'.1 b1 b2 b3 b4
  obtain ⟨r, hr⟩ := hQ₀ α β v hJv
  obtain ⟨r', hr'⟩ := hQ₀ α' β' v' hJv'
  have hr0 : r ≠ 0 := fun e => hv0 (by rw [hr, e, zero_smul])
  have hv'N : v' ∈ N := by
    have : v' = (r' / r) • v := by rw [hr', hr, smul_smul, div_mul_cancel₀ _ hr0]
    rw [this]
    exact N.smul_mem _ hv
  have h0 := GlobalTheory.GLDuality.Compl.mem_orth.1 hv'.2 v' hv'N
  have := (Formalism.GradedWeylDivisibility.fockPos _ v' hv'0).1
  rw [h0] at this
  simp at this

end GlobalTheory.LowIrr
