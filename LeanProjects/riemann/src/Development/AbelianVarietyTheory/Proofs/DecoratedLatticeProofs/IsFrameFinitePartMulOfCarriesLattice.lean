import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.Core.Mi.FrameMove

variable {D : D7}

theorem finPart_finIn' (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (GlobalTheory.FinPlLoc.finIn D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    rw [GlobalTheory.FinPlLoc.finIn_tmul]
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem finIn_mem_idAt (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.FinPlLoc.finIn D z ∈ idAt D (fun _ => True) := by
  refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (GlobalTheory.FinPlLoc.infPart_finIn z), ?_⟩
  exact (Submodule.mem_iInf _).2 fun w => absurd trivial w.2

theorem mulVec_mem_ideal {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem finE_mulVec_hat (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

theorem hat_iff_of_moves (V : HSp D) (t : GA D V) (Λ M : Lat V) (hm : Moves V t Λ M (fun _ => True))
    (z : Fin V.rank → Formalism.IndefR.Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      (Formalism.IndefR.Lev.finE V t).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  let sw := Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E
  let y : Fin V.rank → AE D := fun i => GlobalTheory.FinPlLoc.finIn D (sw.symm (z i))
  have hy : ∀ i, y i ∈ idAt D (fun _ => True) := fun i => finIn_mem_idAt _
  have hz : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) = z := by
    funext i
    show Formalism.IndefR.Lev.swapAE D (finPart D (GlobalTheory.FinPlLoc.finIn D (sw.symm (z i)))) = z i
    rw [finPart_finIn']
    exact sw.apply_symm_apply (z i)
  have hy' : ∀ i, (mt V t *ᵥ y) i ∈ idAt D (fun _ => True) := mulVec_mem_ideal _ hy
  rw [← hz, ← finE_mulVec_hat]
  constructor
  · intro h
    have h1 : y ∈ latV V Λ (fun _ => True) := GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ y hy h
    exact GlobalTheory.LatVHat.latV_mem_hatL D V M _ _ ((hm y hy).1 h1)
  · intro h
    have h1 : mt V t *ᵥ y ∈ latV V M (fun _ => True) := GlobalTheory.HatLatV.mem_latV_of_hatL D V M _ _ hy' h
    exact GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y ((hm y hy).2 h1)

theorem isFrame_of_moves : ∀ (D : D7) (V : HSp D) (t : GA D V) (Λ M : Lat V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)), Moves V t Λ M (fun _ => True) → Formalism.L2.DIV.IsFrame β Λ →
    Formalism.L2.DIV.IsFrame (finE V t * β) M := by
  intro D V t Λ M β hm hf x
  have e1 : (finE V t).val *ᵥ (((finE V t)⁻¹).val *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have k := hat_iff_of_moves V t Λ M hm (((finE V t)⁻¹).val *ᵥ x)
  rw [e1] at k
  change x ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ _
  rw [← k, hf, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]

end GlobalTheory.Core.Mi.FrameMove
