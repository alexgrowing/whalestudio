import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

abbrev Os (s : ReciprocityTheory.Aut.SplitPlace L) : Type := ↥(s.v.adicCompletionIntegers (maximalRealSubfield L))

structure IsResidue (s : ReciprocityTheory.Aut.SplitPlace L) {k : Type} [CommRing k] (φ : Os s →+* k) : Prop where
  surj : Function.Surjective φ
  ker : ∀ x : Os s, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1

def IsCompOf (s : ReciprocityTheory.Aut.SplitPlace L) (κ : Formalism.AUTREP.GAf L n) (y : GL (Fin n) (Os s)) : Prop :=
  ∀ a c, ((y.val a c : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = (s.loc n κ).val a c

end Local

def colMat {k : Type} [CommRing k] {n : ℕ} (v : Fin n → k) (m : Fin n) : Matrix (Fin n) (Fin n) k :=
  1 + Matrix.vecMulVec v (Pi.single m 1)

variable {D : D7}

def FrameRed {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D))
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)) : Prop :=
  ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, ∀ y, IsCompOf s κ y → ∀ a c : Fin n,
    (redFn β s.w (finE V (P.ψ κ))).val (Fin.cast hn.symm a) (Fin.cast hn.symm c) =
      (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val a c

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

def CenRead (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) : Prop :=
  ∀ (i : Fin D.R.m) (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) → ∀ x,
      D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) =
        D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x))

end GlobalTheory.CenFrame

end
