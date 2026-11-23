import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientLeviEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralShiftHerm

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem jn_bl {a r : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (g : Mx D t t) :
    mm (jn hn w v) (bl hn 1 0 0 g) = jn hn w (mm v g) := by
  simp only [jn, bl, mm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp

theorem jn_c (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) : jn hn (c1 hn U) (c2 hn U) = U := by
  ext i j
  obtain ⟨k, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases k with k | k <;> simp [jn, c1, c2]

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c1 hn (jn hn w v) = w := by
  ext i j
  simp [jn, c1]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (w : Mx D a W.rank) (v : Mx D a t) : c2 hn (jn hn w v) = v := by
  ext i j
  simp [jn, c2]

theorem first_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c1 hn (mm U (bl hn 1 0 0 g)) = c1 hn U := by
  conv_lhs => rw [← jn_c hn U, jn_bl, first_columns_join_eq]

theorem second_columns_mul_block_diagonal (hn : W.rank + t = n) {a : ℕ} (U : Mx D a n) (g : Mx D t t) :
    c2 hn (mm U (bl hn 1 0 0 g)) = mm (c2 hn U) g := by
  conv_lhs => rw [← jn_c hn U, jn_bl, second_columns_join_eq]

theorem map_char {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (c : ℝ≥0) (hc0 : c ≠ 0)
    (hc : addEquivAddHaarChar φ = c) : μ.map φ = c⁻¹ • μ := by
  haveI : TopologicalSpace.PseudoMetrizableSpace A := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have h4 := addEquivAddHaarChar_smul_map μ φ
  rw [hc] at h4
  conv_rhs => rw [← h4]
  rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

set_option maxHeartbeats 1200000 in

theorem map_right (a b : ℕ) (μ : Measure (Mx D a b)) (hμ : μ.IsAddHaarMeasure) (g : GL (Fin b) (AE D)) :
    μ.map (fun y => mm y g.1) =
      ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ a : ℝ≥0) • μ := by
  haveI := hμ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D a b
  haveI : IsTopologicalAddGroup (Mx D a b) := i1
  haveI : LocallyCompactSpace (Mx D a b) := i2
  haveI : SecondCountableTopology (Mx D a b) := i3
  haveI : T2Space (Mx D a b) := i4
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g) = absA D (Matrix.GeneralLinearGroup.det g) ^ a := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a b
      (1 : GL (Fin a) (AE D)) g
    simpa using this
  have hA : absA D (Matrix.GeneralLinearGroup.det g) ≠ 0 := (GlobalTheory.CompanionTheory.IwaAd.absA_pos _).ne'
  have e : (fun y : Mx D a b => mm y g.1) = GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) g := by
    funext y
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
  rw [e, inv_pow]
  exact map_char μ _ _ (pow_ne_zero _ hA) hc

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
