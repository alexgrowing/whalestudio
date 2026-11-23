import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemValuationEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientFieldStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest.SumRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem natCast_cpow_half (N : ℕ) (n : ℤ) : (N : ℂ) ^ ((n : ℂ) / 2) = ((Real.sqrt N : ℝ) : ℂ) ^ n := by
  have h1 : (N : ℂ) = ((N : ℝ) : ℂ) := by simp
  rw [h1, show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem sAA_mem (ch : Choice R) (h : ch.FieldOK) : ch.S.sAA ∈ D.what₂.embLL.fieldRange := by
  classical
  unfold GridChoice.sAA
  refine Subfield.prod_mem _ fun w hw => ?_
  obtain ⟨n, hn, -⟩ := aaScalar_eq_pow ch.W w (hasConductor_psiAt_AA ch.W w)
  have hq : GlobalTheory.SplitWeil.resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨y, hy⟩ := h.sqrt w (Or.inl hw)
    exact ⟨y, hy⟩
  rw [hn, hq, natCast_cpow_half]
  exact zpow_mem hs n

theorem psiC_rat (ch : Choice R) (a : Fin ch.n) (g : FinPt ch.G (.top 0)) (m) :
    MvPolynomial.coeff m (psiC (ch.Psi a) g).1 ∈ Set.range D.what₂.embLL := by
  show MvPolynomial.coeff m ((GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) (ch.Psi a (finG (Xp ch.G) g))).1) ∈ _
  simp [GlobalTheory.CoefModel.mapVV, MvPolynomial.coeff_map]

theorem vK_mem (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ) (hS : HidaSetting large₂ R F) (hi : ch.Is)
    (hsc : ch.AtScale CF b) (hK : ch.FieldOK) (hO : ∀ t a, ch.S.SumOK t (ch.Phi a)) (t : T) (x : A.fam.amb.FR t)
    (a : Fin ch.n) : vK ch t x a ∈ D.what₂.embLL.fieldRange := by
  classical
  have hR : ∀ z, z ∈ Set.range D.what₂.embLL → z ∈ D.what₂.embLL.fieldRange := fun z ⟨y, hy⟩ => ⟨y, hy⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have h := hO t a
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ∃ τ, IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) τ :=
    fun β hβ => exists_cosetExpansion_expDepth hL ch.S.toGridChoice t (ch.Phi a) β (h.ex β hβ)
  let τf : CosFam ch.G t → PureDat ch.G t →₀ ℂ := fun β =>
    if hβ : β ∈ ch.S.supp t (ch.Phi a) then (hex β hβ).choose else 0
  have hτf : ∀ β (hβ : β ∈ ch.S.supp t (ch.Phi a)), IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) (τf β) := fun β hβ => by
    simp only [τf, dif_pos hβ]; exact (hex β hβ).choose_spec
  show ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) ∈ D.what₂.embLL.fieldRange
  refine mul_mem (sAA_mem ch hK) ?_
  rw [h.vCore_eq τf fun β hβ => (hτf β hβ).2.1]
  refine sum_mem fun β hβ' => ?_
  have hβ : β ∈ ch.S.supp t (ch.Phi a) := (Set.Finite.mem_toFinset _).1 hβ'
  refine mul_mem (prod_mem fun w _ => SubfieldClass.ratCast_mem _ _) ?_
  unfold GridChoice.classSum
  haveI := h.cls β
  haveI := Fintype.ofFinite (ch.S.Classes t (ch.Phi a) β)
  rw [finsum_eq_sum_of_fintype]
  refine sum_mem fun c _ => mul_mem ?_ ?_
  · unfold GridChoice.invGam
    exact mul_mem (prod_mem fun j _ => inv_mem (natCast_mem _ _)) (prod_mem fun i _ => inv_mem (natCast_mem _ _))
  · unfold GridChoice.pairAt
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    refine sum_mem fun d hd => mul_mem ?_ ?_
    · obtain ⟨X, Y, e⟩ := (hτf β hβ).coef_eq hd
      rw [e]
      exact prod_mem fun w _ => hR _ (GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField ch large₂ F CF b hS hi hsc hK t _ h β hβ w _ _)
    · have hU := GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _ (psiC_rat ch a (ch.S.ptTop c 0))
      have hV := GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _
        (GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField ch large₂ F hS hi hK t x (ch.S.ptRow c 0))
      exact hR _ (GlobalTheory.T.branchingPairing_mem_coefficientField ch large₂ F hS hi hK t _ h (ch.S.colMap d (ch.S.ptTop c) (psiC (ch.Psi a) (ch.S.ptTop c 0)))
        (ch.S.rowMap d (ch.S.ptRow c) (ch.S.formC t (R.jX t x) (ch.S.ptRow c 0))) hU hV)

end GlobalTheory.RowTest.SumRat

namespace GlobalTheory.RowTest

theorem sumRatK_of_sumOKK : SumOKK → SumRatK := by
  rintro ⟨CF0, h⟩
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx' Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc hK t x a => ?_⟩
  obtain ⟨y, hy⟩ := SumRat.vK_mem ch large₂ F CF large₂.sc.b s hi hsc hK (hx D large₂ e hx' Γ Pl0 T A Ks R F s ch hi hsc) t x a
  exact ⟨y, hy⟩

end GlobalTheory.RowTest

end
