import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

def sheetEquiv {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) :
    (Σ σ : k →+* ℂ, CxPts p σ) ≃ CxPts t τ where
  toFun s := sheet t τ s.2
  invFun y := ⟨emb p y, unsheet p y⟩
  left_inv := by
    rintro ⟨σ, y⟩
    have key : ∀ (σ' : k →+* ℂ) (_ : σ' = σ) (y' : CxPts p σ'), y'.1 = y.1 →
        (⟨σ', y'⟩ : Σ σ : k →+* ℂ, CxPts p σ) = ⟨σ, y⟩ := by
      rintro σ' rfl y' h
      rw [Subtype.ext h]
    exact key _ (emb_sheet t τ y) _ rfl
  right_inv y := sheet_unsheet p y

theorem finite_sigma_cxPts {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hX : IsArithVar p 0) : Finite (Σ σ : k →+* ℂ, CxPts p σ) := by
  have : Finite (X.residueField (genericPoint X) →+* ℂ) := by
    by_cases h : Nonempty (X.residueField (genericPoint X) →+* ℂ)
    · obtain ⟨f⟩ := h
      have := SmallSecHeight.numberField hX f.charZero
      infer_instance
    · have := not_nonempty_iff.1 h
      infer_instance
  exact .of_equiv _ (SmallSecHeight.ptsEquiv hX).symm

theorem sum_logNorm_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsArithVar p 0 → ∀ (M : HermLB p) (ν : Weight t τ M.B), WOver M.φ ν → ∀ (r : M.B.ι → X.functionFieldˣ), IsRatSec M.B r → ∑ᶠ y : CxPts t τ, logNorm ν r y = ∑ᶠ σ : k →+* ℂ, ∑ᶠ y : CxPts p σ, logNorm (M.φ σ) r y := by
  intro k _ X _ p t τ hX M ν hν r hr
  have hfin := finite_sigma_cxPts hX
  have (σ : k →+* ℂ) : Finite (CxPts p σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts p σ)
  have h₁ (σ : k →+* ℂ) (y : CxPts p σ) : logNorm ν r (sheet t τ y) = logNorm (M.φ σ) r y :=
    GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hν r hr σ y (mem_offSupp.2 (by
      rw [hX.under_eq_genericPoint]
      exact CartierDiv.genericPoint_notMem_supp _))
  rw [← finsum_comp_equiv (sheetEquiv p t τ)]
  simp only [finsum_eq_sum_of_fintype]
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun y _ => h₁ σ y

end GlobalTheory.CompanionTheory.Ar.BaseZ
