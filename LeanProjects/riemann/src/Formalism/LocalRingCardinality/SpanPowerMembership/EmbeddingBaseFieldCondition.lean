import Formalism.LocalRingCardinality.SpanPowerMembership.RangeInclEqSpan
import Formalism.LocalRingCardinality.DataIdx
import Formalism.LocalRingCardinality.DataNChTie
import Formalism.SharpRestriction.InertJacobiLevels.ResCharConj

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section Coord

variable {K F W ι : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι]
  (σ : K →+* F) (b : Module.Basis ι K W)

def coordMap : W →ₛₗ[σ] (ι → F) where
  toFun x a := σ (b.repr x a)
  map_add' x y := funext fun a => by simp
  map_smul' c x := funext fun a => by simp

theorem coordMap_apply (x : W) (a : ι) : coordMap σ b x a = σ (b.repr x a) := rfl

theorem coordMap_basis (i : ι) : coordMap σ b (b i) = Pi.single i 1 := by
  funext a
  rw [coordMap_apply, b.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one σ
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero σ

theorem coordMap_good : LinearIndependent F (fun i => coordMap σ b (b i)) ∧
    Submodule.span F (Set.range fun i => coordMap σ b (b i)) = ⊤ := by
  have e : (fun i => coordMap σ b (b i)) = ⇑(Pi.basisFun F ι) :=
    funext fun i => (coordMap_basis σ b i).trans (Pi.basisFun_apply _ _ i).symm
  rw [e]
  exact ⟨(Pi.basisFun F ι).linearIndependent, (Pi.basisFun F ι).span_eq⟩

theorem coordMap_image_range : coordMap σ b '' Set.range b = Set.range fun a : ι => (Pi.single a 1 : ι → F) := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun i => coordMap_basis σ b i)

end Coord

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (I : NzIn C)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((I.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

def gapN : TwGap D where
  ntw := C.toTwN I
  nexp := C.toExpN I
  nth := C.toThN I
  ntwbr := C.br
  ntwbr_ind := C.br_ind
  nStage_trivialCharacter_coeff_eq := he
  cover := C.cover

abbrev recN : D7 := withTw D (gapN D C I he)

set_option synthInstance.maxHeartbeats 400000 in

structure EmbC where
  twI : D.what₂.places.Pl → C.Tw
  twI_l : ∀ w, C.l (twI w) = D.what₂.places.resChar w
  embW : ∀ w, D.what₂.LL →+* FractionRing (C.Ok (twI w) 1)
  embW_w : ∀ w (x : D.what₂.LL), 0 ≤ D.what₂.places.val w x ↔
    embW w x ∈ (algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))).range
  embedding_baseField_condition : ∀ w (x : D.LL0) (y z : C.O0 (twI w)), z ≠ 0 →
    C.emb0 (twI w) x * algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) z =
      algebraMap (C.O0 (twI w)) (FractionRing (C.O0 (twI w))) y →
    embW w (x : D.what₂.LL) * algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) z)) =
      algebraMap (C.Ok (twI w) 1) (FractionRing (C.Ok (twI w) 1))
        (algebraMap (C.O (twI w)) (C.Ok (twI w) 1) (algebraMap (C.O0 (twI w)) (C.O (twI w)) y))

variable (E : EmbC D C)

structure StdMt where
  bT : ∀ w j, Module.Basis (I.ixM j) D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  bT_gen : ∀ w j, {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen} = Set.range (bT w j)

variable (S : StdMt D C I)

def eMtN (w : D.what₂.places.Pl) (j : ℕ) :
    D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[E.embW w] (I.ixM j → FractionRing (C.Ok (E.twI w) 1)) :=
  coordMap (E.embW w) (S.bT w j)

theorem eMtN_basis (w : D.what₂.places.Pl) (j : ℕ)
    (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :
    LinearIndependent (FractionRing (C.Ok (E.twI w) 1)) (fun i => eMtN D C I E S w j (b i)) ∧
      Submodule.span (FractionRing (C.Ok (E.twI w) 1)) (Set.range fun i => eMtN D C I E S w j (b i)) = ⊤ :=
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis (S.bT w j)
  haveI : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) :=
    Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := Fintype.ofFinite _
  basis_of_basisF (E.embW w) (coordMap (E.embW w) (S.bT w j)) (S.bT w j)
    (coordMap_good (E.embW w) (S.bT w j)) b

theorem eMtN_lat (w : D.what₂.places.Pl) (j : ℕ) :
    Submodule.span (C.Ok (E.twI w) 1)
      (eMtN D C I E S w j '' {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}) =
    LinearMap.range (TwCore.incl (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)) (I.ixM j)) := by
  rw [S.bT_gen w j, TwCore.range_incl_eq_span]
  exact congrArg _ (coordMap_image_range (E.embW w) (S.bT w j))

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

def nchN : NChoice (recN D C I he) :=
  NChoice.ofOk (recN D C I he) E.twI E.twI_l (fun _ => true) (fun _ => ∅) (fun _ => 1) (fun _ => 1) E.embW E.embW_w
    (eMtN D C I E S) (fun w j _ _ _ => eMtN_basis D C I E S w j) (fun w j _ _ _ => eMtN_lat D C I E S w j)

set_option synthInstance.maxHeartbeats 400000 in

theorem nchN_tie : NChTie (recN D C I he) (nchN D C I he E S) where
  twOf_eq := fun a => hL.elim a
  twSide_eq := fun a => hL.elim a
  Q_eq := fun a => hL.elim a
  psi_eq := ⟨fun _ => 1, fun _ => rfl, fun w _ => (map_one (E.embW w)).trans
    (map_one (algebraMap (C.Ok (E.twI w) 1) (FractionRing (C.Ok (E.twI w) 1)))).symm, fun a => hL.elim a⟩
  embedding_baseField_condition := E.embedding_baseField_condition

end Formalism.BasicNotions.Examples₂.NZ
