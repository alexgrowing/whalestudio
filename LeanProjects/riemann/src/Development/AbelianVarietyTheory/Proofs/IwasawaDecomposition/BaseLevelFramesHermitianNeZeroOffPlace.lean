import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

open scoped ComplexOrder

namespace GlobalTheory.Mem.FramePos

open Formalism.L2.DIV

theorem majAt_XQ_ne_zero {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
    {Pl0 : Type} {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) (Z : Submodule K B.S.Forms) (v : InfinitePlace K)
    (x : Fin (B.dZ ℓ Z) → K) (hx : x ≠ 0) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x x ≠ 0 := by
  have hP : Function.Surjective (B.Pq ℓ Z).mulVec := fun y =>
    ⟨(B.zE ℓ Z).mulVec y, by rw [Matrix.mulVec_mulVec, (BlockDat.lf_z_proj (Z := Z) h).1, Matrix.one_mulVec]⟩
  have hpos : (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)).PosDef :=
    (quotRestrPosDef _ _ _ (BlockDat.lf_HV_pos h v)).1 _ (map_surj _ _ hP)
  have hf := frameOfSpec _ _ hpos
  rw [majAt_eq]
  have e : B.XQ ℓ Z v = frameOf (quotMetC ((B.Pq ℓ Z).map v.embedding) ((B.HV ℓ).map v.embedding)) := rfl
  rw [e, hf.2]
  have hne : (fun i => v.embedding (x i)) ≠ 0 := by
    intro h0
    apply hx
    funext i
    have := congrFun h0 i
    simpa using this
  exact (hpos.dotProduct_mulVec_pos hne).ne'

end GlobalTheory.Mem.FramePos

open GlobalTheory.Mem.FramePos in

theorem GlobalTheory.Mem.R3.framesBase_majAt_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (i : Fin D.R.m) (v : InfinitePlace D.what₂.LL), v ≠ A3.A.v0 → ∀ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ i A3.A.μ0) → D.what₂.LL, x ≠ 0 → Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT i A3.A.μ0) v x x ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ _ hH _ _ i v _ x hx
  have hok := hH.ok.ok2
  have hB : Formalism.L2.DIV.BlockHyp (A3.A.fam.L i A3.A.fam.μ0) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    ⟨hok.conj, hok.irr, hok.lifts i _⟩
  exact majAt_XQ_ne_zero hB _ v x hx
