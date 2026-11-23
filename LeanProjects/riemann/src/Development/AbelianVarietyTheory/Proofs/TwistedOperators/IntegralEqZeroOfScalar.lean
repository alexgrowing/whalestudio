import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

theorem mapDomain_fst_apply {ι κ : Type} [DecidableEq ι] (k : ι × κ →₀ ℕ) (τ : ι) :
    Finsupp.mapDomain Prod.fst k τ = ∑ v ∈ k.support with v.1 = τ, k v := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.single_apply]

def Mon (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Set (FVar D m n →₀ ℕ) := {k | Finsupp.mapDomain Prod.fst k = d}

open Classical in
theorem mon_finite (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : (Mon D m n d).Finite :=
  (GlobalTheory.finite_monomials_of_placeDegree D m n (fun τ => d τ)).subset fun k hk τ => by
    have e := mapDomain_fst_apply k τ
    rw [show Finsupp.mapDomain Prod.fst k = d from hk] at e
    convert e.symm

noncomputable instance (D : D7) (m n : ℕ) (d : D.what₂.Tau →₀ ℕ) : Fintype (Mon D m n d) := (mon_finite D m n d).fintype

variable {D : D7}

def substMat (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g : GA D V) :
    Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ :=
  fun k' k => coeff k'.1 (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ))
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (monomial k.1 1))

open MvPolynomial

theorem substF_one {ι : Type} {N n : ℕ} (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P = P := by
  have key : GlobalTheory.CompactHowe.substF (ι := ι) (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ))
      (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [GlobalTheory.CompactHowe.substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

theorem eq_sum_mon {D : D7} {m n : ℕ} {d : D.what₂.Tau →₀ ℕ} (P : MvPolynomial (FVar D m n) ℂ)
    (hP : ∀ k', coeff k' P ≠ 0 → k' ∈ Mon D m n d) :
    P = ∑ k : Mon D m n d, coeff k.1 P • monomial k.1 (1 : ℂ) := by
  classical
  ext k'
  rw [coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k' ∈ Mon D m n d
  · rw [Finset.sum_eq_single ⟨k', hk⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Subtype.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra h; exact hk (hP k' h)
    · intro b _; rw [if_neg]; rintro rfl; exact hk b.2

variable {D : D7}

theorem substMat_one (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) : substMat θ V m d 1 = 1 := by
  classical
  ext k' k
  simp only [substMat, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, substF_one, coeff_monomial, Matrix.one_apply]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

theorem one_alg (m : ℕ) (i : D.what₂.Tau) (a b : Fin m) :
    IsAlgebraic ℚ ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) i a b) := by
  by_cases hab : a = b
  · subst hab; show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a a); rw [Matrix.one_apply_eq]; exact isAlgebraic_one
  · show IsAlgebraic ℚ ((1 : Matrix (Fin m) (Fin m) ℂ) a b); rw [Matrix.one_apply_ne hab]; exact isAlgebraic_zero

section Avg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem integral_expand (ρ : K → Matrix ι ι ℂ) (hρ : Continuous ρ) (Φ : ι → ℂ) (F : K → ℂ) (k : ι)
    (hF : ∀ g, F g = ∑ k', ρ g k' k * Φ k') : ∫ g, F g ∂κ = ∑ k', (∫ g, ρ g k' k ∂κ) * Φ k' := by
  simp_rw [hF]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun k' _ => integral_mul_const _ _
  · exact fun k' _ => (GlobalTheory.HaarAlg.integrable_of_continuous κ (hρ.matrix_elem k' k)).mul_const _

theorem integral_eq_zero_of_scalar [κ.IsMulLeftInvariant] (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (z : K) (c : ℂ)
    (hc : c ≠ 1) (hz : ρ z = c • 1) (a b : ι) : ∫ g, ρ g a b ∂κ = 0 := by
  classical
  have h := GlobalTheory.HaarAlg.rho_mul_avg κ ρ hρ z
  rw [hz, Matrix.smul_mul, Matrix.one_mul] at h
  have h3 := congrFun (congrFun h a) b
  simp only [Matrix.smul_apply, smul_eq_mul, GlobalTheory.HaarAlg.avg, Matrix.of_apply] at h3
  have h2 : (c - 1) * ∫ g, ρ g a b ∂κ = 0 := by rw [sub_mul, one_mul, h3, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc)

end Avg

end GlobalTheory.RealAvg
