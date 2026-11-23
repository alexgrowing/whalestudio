import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalRingCardinality.DataExtra

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef

section Ties

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m)

def rOp (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (t : T) (a : MonoidAlgebra D.what₂.LL Gp) :
    Matrix (Fin (rDim D A P ψ t)) (Fin (rDim D A P ψ t)) D.what₂.LL :=
  (A.fam.R t).S.lvlOp (A.fam.R t).r (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ a

theorem rE_eq_rOp (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (t : T) :
    rE D A P ψ t = rOp D A P ψ t (idemOf A.X) := rfl

def CenTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (eG : Gp ≃* G0g D.nd) (tup : T → D.what₂.Tup)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)) : Prop :=
  ∀ (t : T) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL Gp),
    (∀ g : Gp, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    ∀ x, X.cen (tup t) z (jA t x) = jA t ((rOp D A P ψ t a).mulVec x)

end Ties

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def hAt {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) : ℂ :=
  ∑ i, ∑ j, star (v.embedding (x i)) * v.embedding (H i j) * v.embedding (y j)

def PosAt {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) : Prop :=
  (∀ x y, hAt H v y x = star (hAt H v x y)) ∧ ∀ x, x ≠ 0 → 0 < (hAt H v x x).re

end Place

section Amb

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m)

structure AmbIds {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (Fm : AmbForm D X) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : T → D.what₂.Tup) where

  eA : ∀ t, DV.Used D (tup t) → (Fin (rDim D A P ψ t) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fm.MtH (tup t)).V

structure AmbTie {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (X : RowSide D EE) (Fm : AmbForm D X) (P : Subgroup Gp) (ψ : P →* D.what₂.LLˣ) (tup : T → D.what₂.Tup)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t))
    (J : AmbIds D A X Fm P ψ tup) : Prop where

  j_eq : ∀ t (h : DV.Used D (tup t)) x, Fm.jAmb (tup t) (J.eA t h x) = jA t x

  lat : ∀ t (h : DV.Used D (tup t)),
    (Fm.MtH (tup t)).L = (rNab D A P ψ t).map (((J.eA t h).toLinearMap).restrictScalars (𝓞 D.what₂.LL))

  metric : ∀ t (h : DV.Used D (tup t)) (v : InfinitePlace D.what₂.LL), PosAt (rH D A P ψ t) v → ∀ x y,
    Formalism.HermitianLatticesTheory.majAt (Fm.MtH (tup t)).b (Fm.MtH (tup t)).X v (J.eA t h x) (J.eA t h y) = hAt (rH D A P ψ t) v x y

end Amb

section MjH

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ}
  (A : FamIn D.what₂.LL Gp Pl0 T m) {P0 : Subgroup Gp} {ψ0 : P0 →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb}

structure MjHIds (Y : DivX D) (S0 : IndefData (A.side P0 ψ0 Zs)) where

  eW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Y.MjH ((i : ℕ) + 1)).V

structure MjHTie (Y : DivX D) (S0 : IndefData (A.side P0 ψ0 Zs))
    (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (J : MjHIds D A Y S0) : Prop where

  j_eq : ∀ (i : Fin m) x, Y.jM ((i : ℕ) + 1) (J.eW i x) = jW i x

  hlat : ∀ i : Fin m, HLatTie (Y.MjH ((i : ℕ) + 1)) (S0.M i) (S0.XW i) (J.eW i)

end MjH

section Joint

variable (D : D7) {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type}
  (A : FamIn D.what₂.LL Gp Pl0 T D.R.m)

structure BaseDivisionAmbientCompatibility (Y : DivX D) (p0 : BaseLevelRowSide D) (a0 : AmbForm D p0.s)
    (P0 : Subgroup Gp) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup Gp) (ψs : Ps →* D.what₂.LLˣ)
    (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs))
    {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} (C : ColData Dc Sp S1)
    (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 p0 Dc)
    (JA : AmbIds D A p0.s a0 P0 ψ0 I.tup) (JM : MjHIds D A Y S0) : Prop where

  div : DivisionCompatible D A P0 ψ0 Ps ψs Zs S0 S1 p0 C NuC I

  amb0 : AmbTie D A p0.s a0 P0 ψ0 I.tup I.jA0 JA

  mjH : MjHTie D A Y S0 I.jW JM

  cen0 : CenTie D A p0.s P0 ψ0 I.eG I.tup I.jA0

end Joint

section Consistency

variable {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {A : FamIn D.what₂.LL Gp Pl0 T D.R.m}
  {Y : DivX D} {p0 : BaseLevelRowSide D} {a0 : AmbForm D p0.s} {P0 : Subgroup Gp} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup Gp}
  {ψs : Ps →* D.what₂.LLˣ} {Zs : DefSub A.fam.amb} {S0 : IndefData (A.side P0 ψ0 Zs)} {S1 : IndefData (A.side Ps ψs Zs)}
  {Dc : DefCols (A.side Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
  {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 p0 Dc}
  {JA : AmbIds D A p0.s a0 P0 ψ0 I.tup} {JM : MjHIds D A Y S0}

theorem BaseDivisionAmbientCompatibility.center_idempotent_action (H : BaseDivisionAmbientCompatibility D A Y p0 a0 P0 ψ0 Ps ψs Zs S0 S1 C NuC I JA JM) (t : T)
    (h : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (x : Fin (rDim D A P0 ψ0 t) → D.what₂.LL) :
    p0.s.cen (I.tup t) ⟨D.ntypes.e0, h⟩ (I.jA0 t x) = p0.s.eOp (I.tup t) (I.jA0 t x) := by
  rw [(H.div.base.forms t).op_eq x]
  exact H.cen0 t ⟨D.ntypes.e0, h⟩ (idemOf A.X) H.div.grp.e0 x

end Consistency

section Bundle

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}

structure FiniteGroupFamilyCharacterData (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where

  Gp : Type
  [grp : Group Gp]
  [fin : Fintype Gp]

  Pl0 : Type
  T : Type

  A : FamIn D.what₂.LL Gp Pl0 T D.R.m

  P0 : Subgroup Gp
  ψ0 : P0 →* D.what₂.LLˣ
  Ps : Subgroup Gp
  ψs : Ps →* D.what₂.LLˣ

  Zs : DefSub A.fam.amb

  S0 : IndefData (A.side P0 ψ0 Zs)
  S1 : IndefData (A.side Ps ψs Zs)

  Dc : DefCols (A.side Ps ψs Zs)
  Sp : SPer Dc
  C : ColData Dc Sp S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)

  I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 ex.p0 Dc

  JA : AmbIds D A ex.p0.s ex.amb0 P0 ψ0 I.tup

  JM : MjHIds D A Y S0

  tied : BaseDivisionAmbientCompatibility D A Y ex.p0 ex.amb0 P0 ψ0 Ps ψs Zs S0 S1 C NuC I JA JM

attribute [instance] FiniteGroupFamilyCharacterData.grp FiniteGroupFamilyCharacterData.fin

end Bundle

end Formalism.L2.Rows
