import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

abbrev cA (θ : InfFam D) (x : Mx D a b) : D.what₂.Tau → Fin a → Fin b → ℂ := fun τ i j => compAt θ τ x i j

abbrev fP (x : Mx D a b) : Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E := fun i j => finPart D (x i j)

abbrev row (i : Fin a) (x : Mx D a b) : Mx D 1 b := x.submatrix (fun _ => i) id

theorem cA_idem (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) (x : Mx D a b) :
    cA θ (e • x) = cA θ x := by
  funext τ i j
  rw [cA, compAt_smul, infPart_idem he, map_one, one_smul]

theorem cv_sF (v : Pl D) (z : AE D) : cv D v (sF D * z) = cv D v z :=
  cv_congr v (by rw [map_mul, finPart_sF, one_mul])

theorem good_mul (θ : InfFam D) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e) {Φ : Mx D a b → ℂ}
    (hG : Good S e Φ) (q : (D.what₂.Tau → Fin a → Fin b → ℂ) → ℂ) : Good S e (fun x => q (cA θ x) * Φ x) := by
  intro x
  have h := hG x
  split_ifs at h ⊢ with hx
  · show q (cA θ x) * Φ x = q (cA θ (e • x)) * Φ (e • x)
    rw [h, cA_idem θ he]
  · show q (cA θ x) * Φ x = 0
    rw [h, mul_zero]

theorem re_im_mul {z w : ℂ} (hz : 0 ≤ z.re ∧ z.im = 0) (hw : 0 ≤ w.re ∧ w.im = 0) :
    0 ≤ (z * w).re ∧ (z * w).im = 0 := by
  rw [Complex.mul_re, Complex.mul_im, hz.2, hw.2]
  exact ⟨by simpa using mul_nonneg hz.1 hw.1, by simp⟩

theorem re_im_prod {ι : Type} (s : Finset ι) (u : ι → ℂ) (h : ∀ i, 0 ≤ (u i).re ∧ (u i).im = 0) :
    0 ≤ (∏ i ∈ s, u i).re ∧ (∏ i ∈ s, u i).im = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact re_im_mul (h i) ih

end PositivityTheory.Rg.Rsw.L.LMajor

end
