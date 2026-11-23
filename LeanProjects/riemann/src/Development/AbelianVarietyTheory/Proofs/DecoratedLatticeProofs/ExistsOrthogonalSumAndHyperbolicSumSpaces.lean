import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthSumSp

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def col {V W : HSpace E} {k : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E) :
    Matrix (Fin (GlobalTheory.Doubling.hsum V W).rank) (Fin k) E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem col_gram {V W : HSpace E} {k l : ℕ} (X : Matrix (Fin V.rank) (Fin k) E) (Y : Matrix (Fin W.rank) (Fin k) E)
    (X' : Matrix (Fin V.rank) (Fin l) E) (Y' : Matrix (Fin W.rank) (Fin l) E) :
    (col X Y)ᴴ * (GlobalTheory.Doubling.hsum V W).gram * col X' Y' = Xᴴ * V.gram * X' + Yᴴ * W.gram * Y' := by
  rw [GlobalTheory.Doubling.gram_hsum, GlobalTheory.Doubling.blkMat, col, col, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp

def orthSumDec (D : D7) (A L : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A L) A L where
  iA := col 1 0
  iB := col 0 1
  isoA := by rw [col_gram]; simp
  isoB := by rw [col_gram]; simp
  orth := by rw [col_gram]; simp
  rank_add := rfl

@[reducible] def posSp (D : D7) (ρ : ℕ) : HSp D where
  V := Fin ρ → D.host.E
  hT := Formalism.BasicNotions.Examples₂.diagForm ρ (fun _ => false)
  herm := Formalism.BasicNotions.Examples₂.diagForm_isSymm ρ _
  nondeg := Formalism.BasicNotions.Examples₂.diagForm_nondeg ρ _
  rank := ρ
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := fun _ => (ρ, 0)
  L0 := Formalism.BasicNotions.Examples₂.stdLat ρ
  standardTuple_isLattice := Formalism.BasicNotions.Examples₂.stdLat_isLattice ρ
  baseLattice_isUnimodular := Formalism.BasicNotions.Examples₂.stdLat_unimod Formalism.BasicNotions.Examples₂.star_isIntegral ρ _

theorem posSp_sigOK (D : D7) (ρ : ℕ) : (posSp D ρ).SigOK :=
  Formalism.BasicNotions.Examples₂.posSpace_sigOK (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ

theorem posSp_gram (D : D7) (ρ : ℕ) : (posSp D ρ).gram = 1 := by
  funext i j
  rw [Matrix.one_apply]
  refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral ρ (fun _ => false) ρ 0 i j).trans ?_
  simp [Formalism.BasicNotions.Examples₂.sgn]

@[reducible] def hypSp (D : D7) (ρ : ℕ) : HSp D :=
  GlobalTheory.Doubling.hdbl (posSp D ρ)

theorem hypSp_sigOK (D : D7) (ρ : ℕ) : (hypSp D ρ).SigOK :=
  GlobalTheory.Doubling.sigOK_hdbl (posSp_sigOK D ρ)

theorem hypSp_sig (D : D7) (ρ : ℕ) (τ) : (hypSp D ρ).sig τ = (ρ, ρ) := by
  show (ρ, 0) + (0, ρ) = (ρ, ρ)
  simp

def hypSumDec (D : D7) (A : HSp D) (ρ : ℕ) : HypDec (GlobalTheory.Doubling.hsum A (hypSp D ρ)) A ρ where
  e := col 0 (col (1 : Matrix (Fin ρ) (Fin ρ) D.host.E) (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))
  e' := col 0 (col ((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E)) (-((2 : D.host.E)⁻¹ • (1 : Matrix (Fin ρ) (Fin ρ) D.host.E))))
  i₀ := col 1 0
  ee := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e' := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]; simp
  e'e := by
    rw [col_gram, col_gram, GlobalTheory.Doubling.gram_hneg, posSp_gram]
    simp [Matrix.smul_eq_diagonal_mul, ← two_mul]
  iso := by rw [col_gram]; simp
  i₀e := by rw [col_gram]; simp
  i₀e' := by rw [col_gram]; simp
  rank_add := by show A.rank + 2 * ρ = A.rank + (ρ + ρ); omega

theorem exists_orthSum_hypSum : ∀ (D : D7), (∀ A L : HSp D, A.SigOK → L.SigOK → ∃ (S : HSp D) (_ : OrthDec S A L), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + L.sig τ) ∧ ∀ (A : HSp D) (ρ : ℕ), A.SigOK → ∃ (S : HSp D) (_ : HypDec S A ρ), S.SigOK ∧ ∀ τ, S.sig τ = A.sig τ + (ρ, ρ) := by
  intro D
  refine ⟨fun A L hA hL => ⟨_, orthSumDec D A L, GlobalTheory.Doubling.sigOK_hsum hA hL, fun τ => rfl⟩,
    fun A ρ hA => ⟨_, hypSumDec D A ρ, GlobalTheory.Doubling.sigOK_hsum hA (hypSp_sigOK D ρ), fun τ => ?_⟩⟩
  show A.sig τ + (hypSp D ρ).sig τ = _
  rw [hypSp_sig]

end GlobalTheory.OrthSumSp
