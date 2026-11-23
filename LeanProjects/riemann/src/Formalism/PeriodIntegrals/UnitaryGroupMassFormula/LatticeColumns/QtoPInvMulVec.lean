import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3 MassDataIdxSteps MassDataIdxStIm MassDataIdxSpl
open scoped Matrix TensorProduct

variable {D : D7}

def crd (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
    (Q : GL (Idx D.R.rS D.R.k) (FpX X p)) (v : Fin X.B.I.n → TpX X p) : Idx D.R.rS D.R.k → FpX X p :=
  ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
    (pr1 θ v ∘ (idxEquiv X).symm)

section Crd

variable (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (Idx D.R.rS D.R.k) (FpX X p))

theorem crd_add (v w : Fin X.B.I.n → TpX X p) : crd X p θ Q (v + w) = crd X p θ Q v + crd X p θ Q w := by
  simp only [crd, map_add, Pi.add_comp, Matrix.mulVec_add]

theorem crd_sub (v w : Fin X.B.I.n → TpX X p) : crd X p θ Q (v - w) = crd X p θ Q v - crd X p θ Q w := by
  simp only [crd, map_sub, Pi.sub_comp, Matrix.mulVec_sub]

theorem crd_zero : crd X p θ Q 0 = 0 := by
  simp only [crd, map_zero, Pi.zero_comp, Matrix.mulVec_zero]

theorem crd_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd X p θ Q (t • v) = (θ t).1 • crd X p θ Q v := by
  have h : pr1 θ (t • v) = (θ t).1 • pr1 θ v := by
    funext i
    show (θ (t * v i)).1 = (θ t).1 * (θ (v i)).1
    rw [map_mul]
    rfl
  unfold crd
  rw [h, Pi.smul_comp, Matrix.mulVec_smul]

theorem crd_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) (v : Fin X.B.I.n → TpX X p) :
    crd X p θ Q (M *ᵥ v) =
      (((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
        (Q : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) *ᵥ crd X p θ Q v := by
  have h1 : pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by
    funext i
    show (θ ((M *ᵥ v) i)).1 = ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Prod.fst_sum, Prod.fst_mul, Matrix.map_apply]
    rfl
  have h2 : ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) ∘ (idxEquiv X).symm =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *ᵥ (pr1 θ v ∘ (idxEquiv X).symm) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext s
    simp [Function.comp_def]
  unfold crd
  rw [h1, h2]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem reindex_inv_mulVec (w : Fin X.B.I.n → FpX X p) :
    ((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) *ᵥ w =
      (((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p)) *ᵥ
        (w ∘ (idxEquiv X).symm)) ∘ (idxEquiv X) := by
  unfold reindex₂
  show (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X).symm
    ((Q⁻¹ : GL (Idx D.R.rS D.R.k) (FpX X p)) : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (FpX X p))) *ᵥ w = _
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mulVec_equiv]

theorem crd_int_of_lat (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p)
    (hv : v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) (s : Idx D.R.rS D.R.k) :
    crd X p θ Q v s ∈ p.1.adicCompletionIntegers X.B.I.F := by
  have h := ((hL v).mp hv).1 ((idxEquiv X).symm s)
  rw [reindex_inv_mulVec] at h
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h

theorem lat_of_crd (hL : LatBasis X p θ (reindex₂ X p Q)) (v : Fin X.B.I.n → TpX X p)
    (h2 : pr2 θ v = 0) (h1 : ∀ s, crd X p θ Q v s ∈ p.1.adicCompletionIntegers X.B.I.F) :
    v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  refine (hL v).mpr ⟨fun i => ?_, ?_⟩
  · have h := h1 ((idxEquiv X) i)
    rw [reindex_inv_mulVec, Function.comp_apply]
    exact h
  · intro i
    have hz : (fun j => th2 X p θ (v j)) = 0 := h2
    rw [hz, Matrix.mulVec_zero]
    exact zero_mem _

end Crd

end PIW.MassDataColumns
