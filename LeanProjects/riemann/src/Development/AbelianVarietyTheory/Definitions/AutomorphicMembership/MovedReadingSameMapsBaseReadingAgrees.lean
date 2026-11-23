import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
  Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) (X0 : BaseLevelRowSide D) (tp : D.what₂.Tup → T)
  (eG : G ≃* G0g D.nd)

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure AllT : Type where
  jA : ∀ μ, (Fin (rDim D A P1 ψ1 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ
  jA0 : ∀ μ, (Fin (rDim D A P0 ψ0 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb μ
  eMt : ∀ (i : Fin D.R.m) μ, (Fin (lDim D A P0 ψ0 i (tp μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  formsA : ∀ μ, FormsTie D.what₂.embLL (jA μ) (rH D A P1 ψ1 (tp μ)) (rE D A P1 ψ1 (tp μ)) (D.what₂.eOp μ)
  latA : ∀ μ, OLatTie D.what₂.embLL (D.what₂.Mtilde μ) (jA μ) (rNab D A P1 ψ1 (tp μ))
  formsAtBottomLevel : ∀ μ, FormsTie D.what₂.embLL (jA0 μ) (rH D A P0 ψ0 (tp μ)) (rE D A P0 ψ0 (tp μ)) (X0.s.eOp μ)
  latA0 : ∀ μ, OLatTie D.what₂.embLL (X0.s.Mtilde μ) (jA0 μ) (rNab D A P0 ψ0 (tp μ))
  formsL : ∀ (i : Fin D.R.m) μ, FormsTie D.what₂.embLL ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap)
    (lH D A P0 ψ0 i (tp μ)) (lE D A P0 ψ0 i (tp μ)) (D.what₂.eMt μ ((i : ℕ) + 1))
  latL : ∀ (i : Fin D.R.m) μ, OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1))
    ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap) (lNab D A P0 ψ0 i (tp μ))
  cen : ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g : G, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    (∀ x, (RowSide.sharp D).cen μ z (jA μ x) = jA μ ((Formalism.L2.Rows.rOp D A P1 ψ1 (tp μ) a).mulVec x)) ∧
    (∀ x, X0.s.cen μ z (jA0 μ x) = jA0 μ ((Formalism.L2.Rows.rOp D A P0 ψ0 (tp μ) a).mulVec x)) ∧
    ∀ (i : Fin D.R.m) x, D.ntypes.cenMt μ ((i : ℕ) + 1) z (D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ x)) =
      D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ (((A.fam.L i (tp μ)).S.lvlOp (A.fam.L i (tp μ)).r (A.fam.lvlA P0 ψ0).P
        (A.fam.lvlA P0 ψ0).ψ a).mulVec x))

def SameOn {K : Type} {n n' : ℕ} {V : Type} (j : (Fin n → K) → V) (j' : (Fin n' → K) → V) : Prop :=
  n = n' ∧ ∀ x x', (∀ (a : Fin n) (a' : Fin n'), (a : ℕ) = a' → x a = x' a') → j x = j' x'

end General

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

def tAll (a : I.ι) : R3.TupU I Set.univ := ⟨I.tup a, Or.inr ((R3.tup_mem_tuOf I).2 (Set.mem_univ a))⟩

end Cols

section Forms

open Formalism.L2.Col

def IsFormOf {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
    (P : LevFam X.E X.K R.r Pr.vGs) (x : MtildeV W Ch sel mu P) {V : Type} (y : V) : Prop :=
  ∃ (F : (mtildeKGSD W Ch sel mu).EqFun) (h : F.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
    HEq ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F) y ∧ x = ⟨F.1, h⟩

end Forms

section Crd

attribute [local instance] GlobalTheory.Mem.Col2.starE

def IsCrd {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι) {V M : Type} [AddCommGroup M] [Module ℂ M]
    (e : Df.MtCx I a ≃ₗ[ℂ] M) (y : V) (v : M) : Prop :=
  ∃ x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I),
    IsFormOf (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x y ∧ v = e (Df.toCx I hX a x)

end Crd

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

abbrev famAll {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :=
  (R3.famR (w.st Z) w.I t.hX Set.univ t.r.z.Xg t.r.z.tr).A

set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in

structure RXs {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : Type 1 where
  all : AllT (w.st Z).toD7 (famAll t) (R3.lev0 w.I) (R3.chr0 w.I) (R3.lev1 w.I) (R3.chr1 w.I) p0 (tAll w.I)
    (t.r.z.R.eG.trans t.r.z.cG)
  jA_use : ∀ s, SameOn (all.jA (t.r.Y.tup s)) (t.r.Y.jA s)
  movedReadingSameMaps_baseReading_agrees : ∀ s, SameOn (all.jA0 (t.r.Y.tup s)) (t.r.Y.jA0 s)
  eMt_use : ∀ i s, SameOn (all.eMt i (t.r.Y.tup s)) (t.r.Y.eMt i s)
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  eMt0 : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((Z.W.eMt0 u).symm (e w.C.mu0 F))
  eMtTw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((Z.W.eMtTw u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I t.hX a (e a)
    (R3.rowForm (D := (w.st Z).toD7) (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a) y) (all.jA a y)
  io : ∀ μ j, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → Z.W.io μ j = 0 ∧ p0.s.io μ j = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre Z.W.shaLen
  laws : Formalism.L2.Pj.LawsCore t.r.z.core.toCore
  canon : t.r.z.core.Q.Canon
  rank : ∀ j, 1 ≤ (t.r.z.core.Q.Dw j).p + (t.r.z.core.Q.Dw j).q
  pb : t.r.z.core.pb = f.P.pb
  std : t.r.z.Std

def RX : RPosition := fun _ _ _ _ _ _ _ _ t => RXs t

def DatExC : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f → R3.GrpAt (w.st Z) w.I →
  Formalism.L2.Theta.VolTieG (w.D Z) →
  ∃ z : R3.Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo ∧
    Formalism.L2.Pj.LawsCore z.core.toCore ∧ z.core.Q.Canon ∧
    (∀ j, 1 ≤ (z.core.Q.Dw j).p + (z.core.Q.Dw j).q) ∧ z.core.pb = f.P.pb

end GlobalTheory.Mem.Top.Bl

end
