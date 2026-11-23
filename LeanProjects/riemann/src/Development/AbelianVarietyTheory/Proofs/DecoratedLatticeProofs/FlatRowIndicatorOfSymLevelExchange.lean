import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowMapEqRootExchangeOperatorTranslateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApplyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentMemSourceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharOfOneRowFirstBlockStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapRowEqZeroUnlessRowMemDualLatticeStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.LocFlat

theorem lam_rowE_symLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k,
      ∀ hm : rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J,
      ((S.T t).lev j (c + 1 + 1) (by omega)).lam ⟨_, hm⟩ = 1 := by
  intro k _ _ _ _ s κ S t _ _ j c H r hc u hm
  have hodd := S.odd
  have hsh := GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply k (Fin κ) t S.ϖ j (c + 1 + 1) (s + 1) (by omega) r (by omega) u
  obtain ⟨g, hg, hl⟩ := GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block k _ t S.P S.μ S.tame j (Sum.inr ⟨r, by omega⟩) ⟨_, hm⟩
    (fun a b ha => by
      have := hsh a b
      rw [if_neg ha, add_zero] at this
      exact this)
    (by
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r, by omega⟩
      simp only at e
      rw [e] at this
      simpa using this)
  have hsym : S.P.lam g = 1 := by
    refine GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row k S.ψ S.ϖ S.ρ κ (s + 1) S.P S.sym ⟨r, by omega⟩ g (fun a b ha => ?_) (fun i hi => ?_)
    · rw [hg, submatrix_apply]
      have := hsh (Sum.inl a) (Sum.inl b)
      rw [if_neg (fun e => ha (Sum.inl_injective e)), add_zero] at this
      exact this.trans (by simp [Matrix.one_apply])
    · have ei : i = ⟨r + 1, by omega⟩ := Fin.ext hi
      rw [hg, submatrix_apply, ei]
      have := hsh (Sum.inl (Sum.inr ⟨r, by omega⟩)) (Sum.inl (Sum.inr ⟨r + 1, by omega⟩))
      rw [if_pos rfl] at this
      have e := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1 + 1) (l := s + 1) (by omega) ⟨r + 1, by omega⟩
      simp only at e
      rw [e] at this
      exact this.trans (by simp [Matrix.one_apply])
  exact hl.trans hsym

theorem pureRow_of_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type)
    [Fintype t] [DecidableEq t], S.Pattern t → S.ExchangeAt t ν → GlobalTheory.LocFlat.PureRow S t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hP hE
  haveI := hν.1
  intro j c H r hc
  have hodd := S.odd
  obtain ⟨C, hC, hEq⟩ := hE j (c + 1) (by omega) (r + 1) (by omega) (by omega) (by omega)
  have HR : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  set Φ := (S.T t).Phi j (c + 1) (by omega) with hΦ
  set V := volNat ν ((S.T t).bas (j + 1) (c + 1) (by omega)) (Cgrp ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1)
    with hV
  have hVpos : 0 < V :=
    volNat_Cgrp_pos ν (HR.2.2 (j + 1) (c + 1) (by omega)).1 (HR.2.2 (j + 1) (c + 1) (by omega)).2.1 _ 1
  have hom1 : om ((S.T t).mu (j + 1)) 1 1 Φ = Φ := by
    funext z; simp [om, nabs]
  have hentry : ∀ x₀, (S.T t).entry S.ψ ν j c H 1 1 x₀ = ((V⁻¹ : ℝ) : ℂ) * opE S.ψ ν 1 Φ x₀ := by
    intro x₀
    simp only [Chain.entry, xi, flat]
    rw [hom1]
  refine ⟨C * V, mul_pos hC hVpos, fun x => ?_⟩
  by_cases hu : x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1))
  · rw [if_pos hu, mul_one, hentry]
    have hm := GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel k s κ S t hP j c H r hc _ hu
    have hl := lam_rowE_symLevel k s κ S t j c H r hc _ hm
    have hdet : Matrix.GeneralLinearGroup.det (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))) = 1 := by
      ext; simp [rowE, lowU, Matrix.det_fromBlocks_zero₁₂]
    have hT := (HL.1 j (c + 1) (by omega)).1 ⟨_, hm⟩
    rw [hl] at hT
    have hfun : (fun z => Φ (z * (rowE (c + 1 + 1) (r + 1) (x (Sum.inr ()))).val)) = Φ := by
      funext z
      have := congrFun hT z
      simpa [om, hdet, nabs] using this
    rw [GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate k S.ψ ν S.cond.continuous inferInstance (XIx (Fin κ) t (j + 1)) (XIx (Fin κ) t j) (c + 1)
      (r + 1) (by omega) (by omega) Φ (HR.1 j (c + 1) (by omega)) x]
    erw [hfun]
    rw [congrFun hEq]
    have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hVpos.ne'
    rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  · rw [if_neg hu, mul_zero, GlobalTheory.T.flatMapRow_eq_zero_unless_row_mem_dualLattice k ν s κ S t j c H r hc x hu]

end GlobalTheory.LocFlat
