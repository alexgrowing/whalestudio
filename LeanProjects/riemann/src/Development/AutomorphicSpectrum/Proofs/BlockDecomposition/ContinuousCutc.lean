import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) :
    e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem intOff_jn (hn : r + t = n) {S : Finset (Pl D)} (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i j => ?_, fun w hw i j => ?_⟩
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
      simpa [jn] using this
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))
      simpa [jn] using this
  · rintro ⟨h1, h2⟩ w hw i j
    simp only [jn, Matrix.submatrix_apply, id]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
    · exact h1 w hw i j
    · exact h2 w hw i j

theorem continuous_jn (hn : r + t = n) : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
  · exact continuous_fst.matrix_elem i j
  · exact continuous_snd.matrix_elem i j

def cutc (hn : r + t = n) (X : Mx D a n) : Mx D a r × Mx D a t :=
  (X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inl j),
    X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))

theorem continuous_cutc (hn : r + t = n) : Continuous (cutc (D := D) (a := a) hn) := by
  refine Continuous.prodMk ?_ ?_ <;> exact continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem cutc_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : cutc hn (jn hn x v) = (x, v) := by
  refine Prod.ext ?_ ?_ <;> ext i j <;> simp [cutc, jn]

theorem intOff_smul {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (x : Mx D a b) : IntOff S (e • x) := by
  intro v hv i j
  have h0 : cv D v e = 0 := by rw [hS.2 v, if_neg hv]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]
  exact zero_mem _

theorem adj_smul {e : AE D} (hc : cA D e = e) (x : Mx D a b) : adj (e • x) = e • adj x := by
  ext i j
  simp [adj, hc]

theorem ip_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem yv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he hc, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem qv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, ip_smul he hc, yv_smul he hc, pr_smul he hc, smul_sub]

theorem pch_smul {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {x : Mx D t t} (hx : e • x = x) (T : Mx D t t) :
    pch ψ x (e • T) = pch ψ x T := by
  have : mm x (e • T) = mm x T := by
    conv_rhs => rw [← hx]
    simp only [mm, Matrix.smul_mul, Matrix.mul_smul]
  simp only [pch, this]

theorem isOrb_smul {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (h : IsOrb V b₀ e ν) (c : ℝ≥0) : IsOrb V b₀ e (c • ν) where
  fin := ⟨fun K hK => by
    have := h.fin.lt_top_of_isCompact hK
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top (by simp) this⟩
  supp := by rw [Measure.smul_apply, h.supp, smul_zero]
  invU := fun g hg => by rw [Measure.map_smul, h.invU g hg]
  invS := fun y hy => by rw [Measure.map_smul, h.invS y hy]
  cov := fun g hg => by rw [Measure.map_smul, h.cov g hg, smul_comm]

theorem isOrb_zero {V : HSp D} {b₀ : HermE D r} {e : AE D} : IsOrb (t := t) V b₀ e 0 where
  fin := ⟨fun K _ => by simp⟩
  supp := by simp
  invU := fun g _ => by simp
  invS := fun y _ => by simp
  cov := fun g _ => by simp

end GlobalTheory.CompanionTheory.EisE

end
