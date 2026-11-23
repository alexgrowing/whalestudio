import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HalfInd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def wr (α : Frame p S n') (β : Frame p T n) : Matrix n n' k →+ WO S T where
  toFun x := (β.b * x * α.b').map p.sec
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]

theorem wr_apply (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) (i : Fin T.rank) (j : Fin S.rank) :
    wr α β x i j = p.sec ((β.b * x * α.b') i j) := rfl

theorem rd_eq (α : Frame p S n') (β : Frame p T n) (t : WO S T) :
    rd α β t = β.b' * (Matrix.map t p.pr : Matrix (Fin T.rank) (Fin S.rank) k) * α.b := rfl

theorem isHalf_wr (α : Frame p S n') (β : Frame p T n) (x : Matrix n n' k) : IsHalf p.e (wr α β x) := fun i j => by
  rw [wr_apply, ← p.sec_pr, p.pr_sec]

theorem wr_rd (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) : wr α β (rd α β t) = t := by
  ext i j
  rw [wr_apply, rd_eq, Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb',
    Matrix.mul_one, Matrix.map_apply, p.sec_pr, ht i j]

set_option maxHeartbeats 800000 in

theorem open_compact_sec (p : SplitPt D k) {LS : Lat S} {LT : Lat T} (hS : Submodule.IsLattice D.host.E LS)
    (hT : Submodule.IsLattice D.host.E LT) :
    IsOpen {y : Matrix (Fin T.rank) (Fin S.rank) k | y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} ∧
    IsCompact {y : Matrix (Fin T.rank) (Fin S.rank) k |
      y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
  have : CharZero k := charZero_of_injective_ringHom (f := p.pr.comp (incA D)) (RingHom.injective _)
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.fg hT.fg
  obtain ⟨N, hN, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T) hS hT
  let A : AddSubgroup (Matrix (Fin T.rank) (Fin S.rank) k) :=
    (latO S T (LS : Set _) (LT : Set _) fun _ => True).comap p.sec.mapMatrix
  have hA : ∀ y, y ∈ A ↔ y.map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := fun _ => Iff.rfl
  have hO : ∀ a : k, a ∈ (𝒪[k]).toAddSubgroup ↔ finPart D (p.sec a) ∈ intAE D := p.int_iff
  have key := GlobalTheory.PlaceCoord.isOpen_isCompact_of_comm (𝒪[k]).toAddSubgroup
    (Valuation.isOpen_integer (v := valuation k)) (IsNonarchimedeanLocalField.isCompact_closedBall k 1) A hN hM
    (fun y hy => by
      have ht : IsHalf p.e (y.map p.sec : WO S T) := fun i j => by
        rw [Matrix.map_apply, ← p.sec_pr, p.pr_sec]
      have h1 : (N • y).map p.sec = N • y.map p.sec := Matrix.ext fun i j => map_nsmul p.sec N (y i j)
      rw [hA, h1]
      exact hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split p.split) ht) fun i j =>
        GlobalTheory.PlaceCoord.toEAf_mem ((hO _).1 (hy i j)))
    (fun y hy i j => by
      have h1 : p.sec ((M : k) * y i j) = (M : AE D) * p.sec (y i j) := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      rw [hO, h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ ((hA y).1 hy) i j)
  exact key

theorem exists_idem (p : SplitPt D k) : ∃ ε, IsPlaceIdem D p.v ε ∧ algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
  obtain ⟨ε, hε, h⟩ := p.above
  exact ⟨ε, hε, by rw [← h, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]⟩

theorem compact_open (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) :
    IsCompact {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} ∧
      IsOpen {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} := by
  obtain ⟨ε, hε, heε⟩ := exists_idem p
  have hh : ∀ x, wr α β x ∈ GlobalTheory.PlaceModel.half S T p.e := fun x => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (isHalf_wr α β x)
  obtain ⟨ho, hc⟩ := open_compact_sec p hS.1 hT.1
  have h1 : {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ∧ IsHalf p.e (wr α β x)} =
      {x | wr α β x ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True} := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h.1, fun h => ⟨?_, isHalf_wr α β x⟩⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε p.split.1 heε h).1
    rwa [(GlobalTheory.PlaceModel.mem_half S T).1 (hh x)] at h2
  rw [h1]
  refine ⟨?_, ho.preimage (f := fun x : Matrix n n' k => β.b * x * α.b')
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)⟩
  convert hc.image (f := fun y => β.b' * y * α.b)
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const) using 1
  ext x
  refine ⟨fun h => ⟨β.b * x * α.b', h, ?_⟩, ?_⟩
  · beta_reduce
    rw [Matrix.mul_assoc β.b, ← Matrix.mul_assoc β.b', β.b'b, Matrix.one_mul, Matrix.mul_assoc, α.b'b, Matrix.mul_one]
  · rintro ⟨y, hy, rfl⟩
    change (β.b * (β.b' * y * α.b) * α.b').map p.sec ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True
    rwa [Matrix.mul_assoc β.b', ← Matrix.mul_assoc β.b, β.bb', Matrix.one_mul, Matrix.mul_assoc, α.bb', Matrix.mul_one]

theorem exists_SB_extFun_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∃ Ψ : Matrix n n' k → ℂ, Ψ ∈ GlobalTheory.SplitWeil.SB (Matrix n n' k) ∧ extFun α β Ψ = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p S T n n' _ _ _ _ α β LS LT hS hT
  have := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨hc, ho⟩ := compact_open α β hS hT
  refine ⟨fun x => halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (wr α β x), ?_, ?_⟩
  · unfold halfInd
    convert GlobalTheory.FinPl.Comm.ite_mem_SB hc ho
  · funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht]
      beta_reduce
      rw [wr_rd α β ht]
    · rw [if_neg ht, halfInd, if_neg fun h => ht h.2]

end GlobalTheory.FinPl.HalfInd

end
