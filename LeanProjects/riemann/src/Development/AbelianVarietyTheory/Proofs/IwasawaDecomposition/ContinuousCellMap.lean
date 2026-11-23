import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace GlobalTheory.FlagPts

namespace GlobalTheory.FlagPts.CellCont

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def polyMat (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) (MvPolynomial (CellIdx k V) k) :=
  fun a c => if a = c then 1 else if h : c < a then MvPolynomial.X ⟨i, (a, c), h⟩ else 0

theorem map_polyMat (u : AffPts k (CellIdx k V)) (i : ι) :
    (polyMat (k := k) (V := V) i).map (MvPolynomial.eval u) = uniMat u i := by
  ext a c
  simp only [Matrix.map_apply, polyMat, uniMat]
  split_ifs
  · exact map_one _
  · exact MvPolynomial.eval_X (f := u) _
  · exact map_zero _

theorem eval_adjugate_polyMat (u : AffPts k (CellIdx k V)) (i : ι) (a c : Fin (finrank k (V i))) :
    MvPolynomial.eval u ((polyMat (k := k) (V := V) i).adjugate a c) = (uniMat u i).adjugate a c := by
  have := RingHom.map_adjugate (MvPolynomial.eval u) (polyMat (k := k) (V := V) i)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_polyMat] at this
  exact congrFun (congrFun this a) c

def polyOnCell (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ P : MvPolynomial (CellIdx k V) k, ∀ u, f (cellFrame b u) = MvPolynomial.eval u P}
  mul_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, fun u => by simp [hP, hQ]⟩
  add_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun u => by simp [hP, hQ]⟩
  algebraMap_mem' := fun c => ⟨MvPolynomial.C c, fun u => (MvPolynomial.eval_C (f := u) c).symm⟩

theorem dual_mem_polyOnCell (b : Frames k V) (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => φ (b' i a)) ∈ polyOnCell b :=
  ⟨∑ l, MvPolynomial.C (φ (b i l)) * polyMat (k := k) (V := V) i l a, fun u => by
    simp only [cellFrame_apply, map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPolynomial.eval_C (f := u), ← map_polyMat u i, Matrix.map_apply, mul_comm]⟩

theorem repr_cellFrame (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (v : V i) :
    (cellFrame b u i).repr v = (uniMat u i).adjugate.mulVec ((b i).repr v) := by
  have hu : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
  have hM : (uniMat u i)⁻¹ = (uniMat u i).adjugate := by
    rw [Matrix.inv_def, det_uniMat]; simp
  rw [← hM]
  have he : (Matrix.toLinearEquiv (b i) (uniMat u i) hu).symm v =
      Matrix.toLin (b i) (b i) (uniMat u i)⁻¹ v := by
    rw [LinearEquiv.symm_apply_eq, Matrix.toLinearEquiv_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul,
      Matrix.mul_nonsing_inv _ hu, Matrix.toLin_one]
    rfl
  simp only [cellFrame, Basis.map_repr, LinearEquiv.trans_apply]
  rw [he, ← LinearMap.toMatrix_mulVec_repr (b i) (b i), LinearMap.toMatrix_toLin]

theorem repr_mem_polyOnCell (b : Frames k V) (i : ι) (v : V i) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => (b' i).repr v a) ∈ polyOnCell b :=
  ⟨∑ c, (polyMat (k := k) (V := V) i).adjugate a c * MvPolynomial.C ((b i).repr v c), fun u => by
    show (cellFrame b u i).repr v a = _
    rw [repr_cellFrame]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_C (f := u), eval_adjugate_polyMat]⟩

theorem regFns_le_polyOnCell (b : Frames k V) : regFns k V ≤ polyOnCell b := by
  refine Algebra.adjoin_le ?_
  rintro f (⟨i, φ, a, rfl⟩ | ⟨i, v, a, rfl⟩)
  · exact dual_mem_polyOnCell b i φ a
  · exact repr_mem_polyOnCell b i v a

theorem continuous_cellFrame (b : Frames k V) : Continuous (cellFrame b) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨P, hP⟩ := regFns_le_polyOnCell b hf
  have : cellFrame b ⁻¹' {b' | f b' ≠ 0} = {u | MvPolynomial.eval u P ≠ 0} := by
    refine Set.ext fun u => ?_
    show f (cellFrame b u) ≠ 0 ↔ _
    rw [hP]
    rfl
  rw [this]
  exact isOpen_affPts_ne_zero P

end GlobalTheory.FlagPts.CellCont

namespace GlobalTheory.FlagPts

theorem continuous_cellMap : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  intro k _ ι _ V _ _ _ b
  exact continuous_coinduced_rng.comp (CellCont.continuous_cellFrame b)

end GlobalTheory.FlagPts
