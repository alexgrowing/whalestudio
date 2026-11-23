import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

namespace GlobalTheory.ActQ

theorem snoc_map {α β : Type*} {r : ℕ} (f : α → β) (e : Fin r → α) (z : α) (j : Fin (r + 1)) :
    f (Fin.snoc (α := fun _ => α) e z j) = Fin.snoc (α := fun _ => β) (fun a => f (e a)) (f z) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

end GlobalTheory.ActQ

theorem GlobalTheory.realPoint_ratIsom_isMatOn : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : X.B.I.GA) (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ j, n (frame s.frame j) = ∑ i, A i j • frame s.frame i) → ∀ v : NumberField.InfinitePlace X.B.I.F, GlobalTheory.LoopAct.IsMatOn (uMat (x.1 v)) (fun j => uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j) (A.map (embS D (X.pl v))) := by
  intro D X Y u u' s n x A hR hA v
  obtain ⟨M, -, hM1, -, hM3⟩ := hR
  obtain ⟨M', -, hM1', -, hM3'⟩ := s.rep.2.1
  have hP' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (↑M' : Matrix _ _ _).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1'
  have hL' : ∀ y, X.crd (s.lin y) = (↑M' : Matrix _ _ _) *ᵥ X.crd y := hM3'
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfr : ∀ j, frame s.frame j = s.lin (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j) := by
    intro j
    have e1 : s.frame = Formalism.L2.SG.TermOp.mapLF s.lin (lf D (X.Fu u')) := rfl
    rw [e1]
    unfold Formalism.L2.SG.TermOp.mapLF
    rw [dif_pos hiso]
    rw [GlobalTheory.ActQ.snoc_map (f := (s.lin : (VS D).V → (VS D).V)), ← X.Fu_e u', ← X.flagZVector u']
    rfl
  have hfrm : ∀ j, Formalism.L2.SG.RealObj.frm X u' 1 v j =
      rv X.B.I v (X.crd (Fin.snoc (α := fun _ => (VS D).V) X.eX (X.zu u') j)) := by
    intro j
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    rw [GlobalTheory.ActQ.snoc_map (f := fun y => rv X.B.I v (X.crd y))]
    rfl
  have hf : ∀ j, uMat (s.pt.1 v) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v j = rv X.B.I v (X.crd (frame s.frame j)) := by
    intro j
    rw [hfrm, hfr, hL', ← Formalism.L2.SG.Pf.Level.rv_mulVec X v, ← hP' v]
  have hsum : ∀ (c : Fin (D.R.rS + 1) → D.host.E) (w : Fin (D.R.rS + 1) → (VS D).V),
      rv X.B.I v (X.crd (∑ i, c i • w i)) = ∑ i, embS D (X.pl v) (c i) • rv X.B.I v (X.crd (w i)) := by
    intro c w
    have hc : X.crd (∑ i, c i • w i) = ∑ i, X.ιE.symm (c i) • X.crd (w i) := by
      funext l
      simp [HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, map_sum, Finset.sum_apply, smul_eq_mul]
    rw [hc]
    unfold rv
    have hv : (fun l => X.B.I.φ v ((∑ i, X.ιE.symm (c i) • X.crd (w i)) l)) =
        ∑ i, embS D (X.pl v) (c i) • fun l => X.B.I.φ v (X.crd (w i) l) := by
      funext l
      simp [Finset.sum_apply, map_sum, X.φ_eq]
    rw [hv, Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
  intro b
  dsimp only
  rw [hf b, hM1 v, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, hA b, hsum]
  simp_rw [hf, Matrix.map_apply]

end
