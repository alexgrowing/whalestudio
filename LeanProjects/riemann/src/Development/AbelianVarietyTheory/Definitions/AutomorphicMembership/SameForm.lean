import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.DataKap

noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev MtCx (a : I.ι) : Type := MtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL

abbrev MtHL (hX : B.fields.Ok) (a : I.ι) : HLat B.LL := MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps

def toCx (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) : MtCx I a := toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL x

def SameForm (l : I.Laws) (u : B.Word) (a : I.ι) (F : MtCx I a) (G : (I.per l u a).Mt) : Prop :=
  ∀ p : (I.stX a).D (), (show (I.perIn u a).Mt B.fields.emb B.embLL from G).1 () p = F.1 (toRow I.sel (I.tup a) p.1.1)

variable (l : I.Laws) (hX : B.fields.Ok)

structure DefTrue (W : RowsRest B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] W.Amb a) : Prop where
  muAt : ∀ w, W.muAt w = I.mu0
  muTw : ∀ w, W.muTw w = if B.places.resChar w = B.host.pde then I.muStar' else I.muStar
  eMt0 : ∀ u F, SameForm I l u I.mu0 F ((W.eMt0 u).symm (e (I.cols l).mu0 F))
  eMtTw : ∀ u (a : (I.cols l).Tup) F, SameForm I l u a F ((W.eMtTw u a).symm (e a F))
  norm : ∀ (a : (I.cols l).Tup) x, Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x = ‖e a (toCx I hX a x)‖
  lat : ∀ a y, y ∈ (W.Mtilde a).carrier ↔ ∃ x ∈ (MtHL I hX a).L, e a (toCx I hX a x) = y
  gen : ∀ a, ∀ y ∈ (W.Mtilde a).gen, y ∈ (W.Mtilde a).carrier
  eOp : ∀ a, W.eOp a = LinearMap.id
  ze : ∀ u a, W.ze u a = 1

structure StandIn {C : Cols B} (W : RowsRest B C) : Prop where
  drows : W.Drows = 0
  d0 : W.D0 = 0
  dall : W.Dall = 0
  delp : W.delp = 0
  ft : IsEmpty W.FT
  mult : ∀ a j, j ≠ B.R.m → Subsingleton (W.Mult a j)
  io : ∀ a j, W.io a j = 0
  mj : ∀ j, Subsingleton (W.Mj j)
  mt : ∀ a j, Subsingleton (W.Mt a j)
  eMt : ∀ a j, W.eMt a j = LinearMap.id
  bu : ∀ u φ F, W.Bu u φ F = 0
  ij : ∀ a j w, W.Ij a j w = 0 ∧ W.jw a j w = 0
  eta : ∀ j w, W.etaJ j w = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre W.shaLen
  kap : ∀ V S N G, DV.KapDef (assemble B C W V S N G)

structure RowsDef : Type 1 where
  W : RowsRest B (I.cols l)
  e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] W.Amb a
  tru : DefTrue I l hX W e
  std : StandIn W

structure AmbTrue (Z : TC.Later B (I.cols l)) (e : ∀ a : (I.cols l).Tup, MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (A : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))) : Prop where
  mt : ∀ a : (I.cols l).Tup, (⟨A.MtH a, fun x => A.jAmb a x⟩ : Σ H : HLat B.LL, (H.V → Z.W.Amb a)) = ⟨MtHL I hX a, fun x => e a (toCx I hX a x)⟩

end GlobalTheory.Mem.Df

end
