import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Tr

def piSigmaIso {ι : Type} {P P' : ι → Type} (M : ι → Type) [∀ k, Group (M k)] (e : ∀ k, P k ≃ P' k) :
    (∀ kv : Σ k, P k, M kv.1) ≃* (∀ kv : Σ k, P' k, M kv.1) where
  toFun g kv := g ⟨kv.1, (e kv.1).symm kv.2⟩
  invFun g kv := g ⟨kv.1, e kv.1 kv.2⟩
  left_inv g := by
    funext ⟨k, v⟩
    exact congrArg (β := M k) (fun w : P k => g (Sigma.mk k w)) ((e k).symm_apply_apply v)
  right_inv g := by
    funext ⟨k, v⟩
    exact congrArg (β := M k) (fun w : P' k => g (Sigma.mk k w)) ((e k).apply_symm_apply v)
  map_mul' _ _ := rfl

variable {B : Base} {C : Cols B}

def grpIso {a b : Late B C} (e : ∀ k, a.D.nd.PlG k ≃ b.D.nd.PlG k) : G0g a.D.nd ≃* G0g b.D.nd :=
  (by with_unfolding_all exact ((piSigmaIso (fun k : Fin 2 => GL (Fin a.D.R.r) (ZMod (a.D.host.g k))) e) :))

structure SameGrp (a b : Late B C) where

  e : ∀ k, a.D.nd.PlG k ≃ b.D.nd.PlG k

  pl : ∀ k v, (b.D.naut.plGw k (e k v) : HeightOneSpectrum (𝓞 B.host.E)) = a.D.naut.plGw k v

  e0 : ∀ g, b.D.ntypes.e0.coeff (grpIso e g) = a.D.ntypes.e0.coeff g

abbrev SameGrp.iso {a b : Late B C} (s : SameGrp a b) : G0g a.D.nd ≃* G0g b.D.nd := grpIso s.e

def SameGrp.ofN {W : RowsRest B C} (N : NStage B C W) (V V' : DivStage B C W) (S S' : SStage B C W) (G G' : GJStage B C) :
    SameGrp ⟨W, V, S, N, G⟩ ⟨W, V', S', N, G'⟩ :=
  ⟨fun _ => Equiv.refl _, fun _ _ => rfl, fun _ => rfl⟩

def SameGrp.symm {a b : Late B C} (s : SameGrp a b) : SameGrp b a where
  e k := (s.e k).symm
  pl k v := (s.pl k ((s.e k).symm v)).symm.trans (congrArg (b.D.naut.plGw k) ((s.e k).apply_symm_apply v))
  e0 g := (s.e0 _).symm.trans (congrArg b.D.ntypes.e0.coeff (s.iso.apply_symm_apply g))

namespace Tr

variable {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

variable {b} in

def _root_.GlobalTheory.Mem.R3.SameGrp.back (s : SameGrp a b) : (Σ k : Fin 2, b.D.nd.PlG k) ≃ (Σ k : Fin 2, a.D.nd.PlG k) :=
  Equiv.sigmaCongrRight fun k => (s.e k).symm

variable {b} in

theorem _root_.GlobalTheory.Mem.R3.SameGrp.pl_back (s : SameGrp a b) (kv : Σ k : Fin 2, b.D.nd.PlG k) :
    (a.D.naut.plGw kv.1 ((s.e kv.1).symm kv.2) : HeightOneSpectrum (𝓞 B.host.E)) = b.D.naut.plGw kv.1 kv.2 := s.symm.pl kv.1 kv.2

def GrpCl (D : D7) (Pg : Finset (Pl D.host.E)) (c : G → ℂ) (Dv : Fin 2 → Pl D.host.E → Prop) (eG : G ≃* G0 Pg D.R.r)
    (eR : G ≃* G0g D.nd) : Prop :=
  ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, c g = D.ntypes.e0.coeff (eR g)) ∧
    (∀ kv, Dv kv.1 (plg kv).1) ∧
    ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

omit [Fintype G] in

theorem grpCl_tr (s : SameGrp a b) {Pg c Dv eG} {eR : G ≃* G0g a.D.nd} (h : GrpCl a.D Pg c Dv eG eR) :
    GrpCl b.D ((Pg)) c ((Dv)) ((eG)) (eR.trans s.iso) := by
  obtain ⟨plg, iso, h1, h2, h3, h4⟩ := h
  refine ⟨(by with_unfolding_all exact ((s.back.trans plg) :)), fun kv => (by with_unfolding_all exact ((iso (s.back kv)) :)), fun kv => ?_, fun g => ?_, fun kv => ?_, fun g kv => ?_⟩
  · exact (by with_unfolding_all exact (((h1 (s.back kv)).trans (s.pl_back kv)) :))
  · exact (by with_unfolding_all exact (((h2 g).trans (s.e0 (eR g)).symm) :))
  · exact (by with_unfolding_all exact ((h3 (s.back kv)) :))
  · exact (by with_unfolding_all exact ((h4 g (s.back kv)) :))

omit [Fintype G] in

theorem psiPPTie_transport (s : SameGrp a b) {P0 P1 : Subgroup G} {ψ0 ψ1} {eR : G ≃* G0g a.D.nd} (h : PsiPPTie a.D P0 ψ0 P1 ψ1 eR) :
    PsiPPTie b.D P0 ((ψ0)) P1 ((ψ1)) (eR.trans s.iso) := by
  obtain ⟨Pg, pl, res, ψ, eC, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (Pg :)), (by with_unfolding_all exact ((s.back.trans pl) :)), fun kv => (by with_unfolding_all exact ((res (s.back kv)) :)), (by with_unfolding_all exact (ψ :)), (by with_unfolding_all exact (eC :)), ?_, fun kv => ?_⟩
  · constructor
    case place => intro kv; exact (by with_unfolding_all exact (((h1.place (s.back kv)).trans (s.pl_back kv)) :))
    case comp => intro g kv; exact (by with_unfolding_all exact ((h1.comp g (s.back kv)) :))
    case gen => exact (by with_unfolding_all exact (h1.gen :))
    case p0 => exact (by with_unfolding_all exact (h1.p0 :))
    case chi0 => exact (by with_unfolding_all exact (h1.chi0 :))
    case ps => exact (by with_unfolding_all exact (h1.ps :))
    case chis => exact (by with_unfolding_all exact (h1.chis :))
  · exact (by with_unfolding_all exact ((h2 (s.back kv)) :))

variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Two

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A}

theorem grpRecord_tr (s : SameGrp a b) (h : R.grp_record) : letI := alg b iK; (real b R).grp_record := by
  obtain ⟨eR, plg, iso, h2, h3, h4⟩ := h
  refine ⟨eR.trans s.iso, (by with_unfolding_all exact ((s.back.trans plg) :)), fun kv => (by with_unfolding_all exact ((iso (s.back kv)) :)), fun g => ?_, fun kv => ?_, fun g kv => ?_⟩
  · exact (by with_unfolding_all exact (((h2 g).trans (s.e0 (eR g)).symm) :))
  · exact (by with_unfolding_all exact ((h3 (s.back kv)) :))
  · exact (by with_unfolding_all exact ((h4 g (s.back kv)) :))

theorem isGrp_tr (s : SameGrp a b) (h : R.IsGrp F) : letI := alg b iK; (real b R).IsGrp (face b F) := by
  letI := alg b iK
  constructor
  case red_R => exact (by with_unfolding_all exact (h.red_R :))
  case red_L => exact (by with_unfolding_all exact (h.red_L :))
  case levels => exact (by with_unfolding_all exact (h.levels :))
  case record => exact (by with_unfolding_all exact ((grpRecord_tr b s h.record) :))
  case chiW => exact (by with_unfolding_all exact (h.chiW :))

theorem baseW_tr (s : SameGrp a b) (h : R.BaseW F) : letI := alg b iK; (real b R).BaseW (face b F) := by
  letI := alg b iK
  constructor
  case lev => exact (by with_unfolding_all exact ((levIs_tr b h.lev) :))
  case grp => exact (by with_unfolding_all exact ((isGrp_tr b s h.grp) :))
  case fam => exact (by with_unfolding_all exact ((isFam_tr b h.fam) :))
  case models => exact (by with_unfolding_all exact ((isModels_tr b h.models) :))
  case chain => exact (by with_unfolding_all exact ((isChainW_tr b h.chain) :))
  case thP => exact (by with_unfolding_all exact ((isThPW_tr b h.thP) :))

end Two

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}

section Kept

variable {R : RealDat a.D A.A Ks} {F : Face a.D A.A}

theorem keep_tr (s : SameGrp a b) {cG : G0 R.Pg a.D.R.r ≃* G0g a.D.nd} (h : Keep (A3 := A) R F cG) :
    @Keep b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact ((face b F) :))) ((by with_unfolding_all exact ((cG.trans s.iso) :))) := by
  apply (config := { synthAssignedInstances := false }) Keep.mk
  case grp => exact (by with_unfolding_all exact ((grpCl_tr b s (Pg := R.Pg) (c := fun g => a.D.what₂.embLL ((idemOf A.A.X).coeff g)) (Dv := R.C.P.Div)
    (eG := R.eG) (eR := R.eG.trans cG) ((h.grp))) : _))
  case psi => exact (by with_unfolding_all exact ((psiPPTie_transport b s h.psi) :))
  case std => exact (by with_unfolding_all exact (h.std :))
  case signs => exact (by with_unfolding_all exact (h.signs :))
  case frames => kexactB h.frames
  case beta => exact (by with_unfolding_all exact (h.beta :))
  case prX => exact (by with_unfolding_all exact (h.prX :))
  case guard => exact (by with_unfolding_all exact (h.guard :))
  case valKs => exact (by with_unfolding_all exact (h.valKs :))
  case frameKs => exact (by with_unfolding_all exact (h.frameKs :))
  case levKs => exact (by with_unfolding_all exact (h.levKs :))

theorem keep_back (s : SameGrp b a) {cG : G0 (levCh b R.toLevCh).Pg b.D.R.r ≃* G0g b.D.nd}
    (h : @Keep b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact ((face b F) :))) ((by with_unfolding_all exact (cG :)))) :
    Keep (A3 := A) R F ((by with_unfolding_all exact ((cG.trans s.iso) :))) := by
  let := alg b iK
  apply (config := { synthAssignedInstances := false }) Keep.mk
  case grp => exact (by with_unfolding_all exact ((grpCl_tr a s (Pg := (real b R).Pg) (c := fun g => a.D.what₂.embLL ((idemOf A.A.X).coeff g))
    (Dv := (real b R).C.P.Div) (eG := (real b R).eG) (eR := (real b R).eG.trans ((cG))) ((h.grp))) : _))
  case psi => exact (by with_unfolding_all exact ((psiPPTie_transport a s h.psi) :))
  case std => exact (by with_unfolding_all exact (h.std :))
  case signs => exact (by with_unfolding_all exact (h.signs :))
  case frames => kexactB h.frames
  case beta => exact (by with_unfolding_all exact (h.beta :))
  case prX => exact (by with_unfolding_all exact (h.prX :))
  case guard => exact (by with_unfolding_all exact (h.guard :))
  case valKs => exact (by with_unfolding_all exact (h.valKs :))
  case frameKs => exact (by with_unfolding_all exact (h.frameKs :))
  case levKs => exact (by with_unfolding_all exact (h.levKs :))

end Kept

variable {R : RealDat3 a.D A Ks} {F : Face3 a.D A}

set_option maxHeartbeats 800000 in

theorem weakCharInertPart_realAdelicDataTransport (s : SameGrp a b) (h : R.WeakCharacterisation F) : letI := alg b iK; (real3 b R).WeakCharacterisation (face3 b F) := by
  letI := alg b iK
  constructor
  case base => exact (by with_unfolding_all exact ((baseW_tr b s h.base) :))
  case inert => exact (by with_unfolding_all exact ((isInert_tr b h.inert) :))
  case fullY => tr_clause a b h.fullY
  case fullX => tr_clause a b h.fullX
  case fullP => tr_clause a b h.fullP
  case scal => exact (by with_unfolding_all exact ((isScal_tr b h.scal) :))
  case tup => exact (by with_unfolding_all exact ((isTup_tr b h.tup) :))
  case phase => exact (by with_unfolding_all exact (h.phase :))
  case allPl => exact (by with_unfolding_all exact (h.allPl :))

theorem pins_tr (s : SameGrp a b) {cG : G0 R.Pg a.D.R.r ≃* G0g a.D.nd} (h : Pins R F cG) : letI := alg b iK; Pins (real3 b R) (face3 b F) ((by with_unfolding_all exact ((cG.trans s.iso) :))) := by
  letI := alg b iK
  constructor
  case char => exact (by with_unfolding_all exact ((weakCharInertPart_realAdelicDataTransport b s h.char) :))
  case keep => exact (by with_unfolding_all exact ((keep_tr b s h.keep) :))
  case phs => exact (by with_unfolding_all exact (h.phs :))
  case trSem => tr_via (fun P : type_of% (R.TrISem F) => (∃ tr, P tr ∧ SepWith A tr) → P A.trI ∧ A.fam3.TrISep) (trISem_eq b R F) h.trSem

theorem holds_tr (h : Holds R F) : letI := alg b iK; Holds (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case prim => exact (by with_unfolding_all exact ((primRows3_tr b h.prim) :))
  case aux => exact (by with_unfolding_all exact ((realAdelicInertTransport_furtherRows b h.aux) :))
  case ok => exact (by with_unfolding_all exact (h.ok :))
  case sep => exact (by with_unfolding_all exact (h.sep :))

theorem errEq_tr (h : ErrEq R F) : letI := alg b iK; ErrEq (real3 b R) (face3 b F) := by
  tr_via (fun X : Cx.CxData A.fam3.amb3 => ∀ w j, (X.data F.cr false).err0 w j = errOf (X.data F.cr false) (F.fc X.zs).Z.F0 w)
    (toCx3_eq b R F) h

end Tr

end GlobalTheory.Mem.R3

end
