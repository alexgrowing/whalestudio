import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFTC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar

namespace PositivityTheory.Rg.Rsw.L.LPartFT

variable {D : D7} {n r t a : ℕ}

def c₁ (D : D7) (hn : r + t = n) : Matrix (Fin r) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inl k)) id

def c₃ (D : D7) (hn : r + t = n) : Matrix (Fin t) (Fin n) D.host.E :=
  (1 : Matrix (Fin n) (Fin n) D.host.E).submatrix (fun k => ee hn (Sum.inr k)) id

theorem jn_ee (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (i : Fin a) (s : Fin r ⊕ Fin t) :
    jn hn x v i (ee hn s) = Matrix.fromCols x v i s := by
  simp only [jn, Matrix.submatrix_apply, id, Equiv.symm_apply_apply]

theorem mul_c₁ (hn : r + t = n) (y : Mx D a r) : mm y ((c₁ D hn).map (incA D)) = jn hn y 0 := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₁, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem mul_c₃ (hn : r + t = n) (y : Mx D a t) : mm y ((c₃ D hn).map (incA D)) = jn hn 0 y := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  rw [jn_ee]
  rcases s with k | k <;>
    simp [mm, c₃, Matrix.mul_apply, Matrix.one_apply, (ee hn).injective.eq_iff] <;>
    exact Finset.sum_eq_zero fun x _ => if_neg (by simp [Fin.ext_iff]; omega)

theorem compl_c₁ (hn : r + t = n) : IsCompl (c₁ D hn) 1 := by
  refine ⟨by simp, fun i hi => ?_⟩
  have : ee hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ee_inl_val hn _)
  simp only [c₁, this]
  rfl

theorem compl_c₃ (hn : r + t = n) : IsCompl (c₃ D hn) (Pm D.host.E hn) := by
  refine ⟨Matrix.isUnit_det_of_right_inverse (Pm_mul_alt hn), fun i hi => ?_⟩
  have h1 : ff hn (Sum.inl ⟨i, hi⟩) = i := Fin.ext (ff_inl_val hn _)
  have h2 : πe hn i = ee hn (Sum.inr ⟨i, hi⟩) := by
    have := πe_ff_inl hn ⟨i, hi⟩
    rwa [h1] at this
  funext j
  simp only [Pm, c₃, Matrix.submatrix_apply]
  rw [h2]

theorem linInd_c₁ (hn : r + t = n) : LinearIndependent D.host.E (c₁ D hn) := by
  have h : c₁ D hn = (Pi.basisFun D.host.E (Fin n)) ∘ (fun k => ee hn (Sum.inl k)) := by
    funext k j
    simp [c₁, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h]
  exact (Pi.basisFun D.host.E (Fin n)).linearIndependent.comp _
    (fun k k' h => Sum.inl_injective ((ee hn).injective h))

theorem jn_mul_bl (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) (A : Mx D r r) (B : Mx D r t) (C : Mx D t r)
    (E : Mx D t t) :
    HMul.hMul (jn hn x v) (bl hn A B C E) = jn hn (x * A + v * C) (x * B + v * E) := by
  simp only [jn, bl]
  rw [show (Matrix.fromCols x v).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm =
    (Matrix.fromCols x v).submatrix id (⇑(finSumFinEquiv.trans (finCongr hn)).symm) from rfl,
    Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem jn_add (hn : r + t = n) (x x' : Mx D a r) (v v' : Mx D a t) : jn hn x v + jn hn x' v' = jn hn (x + x') (v + v') := by
  ext i j
  obtain ⟨s, rfl⟩ := (ee hn).surjective j
  simp only [Matrix.add_apply, jn_ee]
  rcases s with k | k <;> simp

end PositivityTheory.Rg.Rsw.L.LPartFT
