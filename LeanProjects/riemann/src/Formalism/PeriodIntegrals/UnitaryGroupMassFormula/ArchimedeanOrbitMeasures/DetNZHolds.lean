import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.S Matrix

def wF {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V :=
  Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

theorem tupH_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    tupH (frameOf X u') = fun i => X.crd (wF X u' i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tupH, F0, wF, Fin.append_left]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp only [Fin.snoc_castSucc]; rfl
  · simp only [tupH, wF, Fin.append_right]; rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (i j : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j = X.ιE.symm ((VS D).hT (wF X u' i) (wF X u' j)) := by
  rw [tupH_eq, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, RingEquiv.symm_apply_apply]
  rfl

theorem hT_fe {D : D7} (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h := (VS D).herm.eq (X.eX b) (X.fY a)
  rw [X.ef] at h
  rw [← h]
  split_ifs <;> simp

theorem hT_ze {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.eX a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u')
  rw [(X.zu_orth u' a).1] at h
  rw [← h]; simp

theorem hT_zf {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.fY a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u')
  rw [(X.zu_orth u' a).2] at h
  rw [← h]; simp

theorem row_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : Fin (D.R.rS + 1 + D.R.rS) → X.B.I.E)
    (i : Fin (D.R.rS + 1 + D.R.rS)) :
    X.ιE ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) *ᵥ v) i) =
      ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) := by
  simp only [Matrix.mulVec, dotProduct, gram_eq, map_sum, map_mul, RingEquiv.apply_symm_apply]

theorem detNZ_holds : DetNZ := by
  intro D X u' ψ hT μinf νinf fibInf _
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have row : ∀ i, ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) = 0 := by
    intro i
    rw [← row_eq, hv]
    simp
  have hTne : ((((D.mem u').A.T : ℕ) : D.host.E)) ≠ 0 := by
    exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have he : ∀ a, v (Fin.castAdd D.R.rS (Fin.castSucc a)) = 0 := by
    intro a
    have h := row (Fin.natAdd (D.R.rS + 1) a)
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_fe, X.ff,
      (X.zu_orth u' _).2] at h
    exact h
  have hf : ∀ a, v (Fin.natAdd (D.R.rS + 1) a) = 0 := by
    intro a
    have h := row (Fin.castAdd D.R.rS (Fin.castSucc a))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ef,
      (X.zu_orth u' _).1] at h
    exact h
  have hz : v (Fin.castAdd D.R.rS (Fin.last D.R.rS)) = 0 := by
    have h := row (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_ze, hT_zf,
      X.zu_norm, hTne] at h
    exact h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hz
    · exact he k
  · exact hf j

end PI.AprimeInfW
