import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.RealGeo GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Tr

variable {B : Base} {C : Cols B} {a b : Late B C} {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : Top.TwDat B}
  {Wt : Set B.places.Pl}

def SameGrp.ofGrpTrue {f : Top.Fr B.toPre} (h : Top.GrpTrue a.N f) (h' : Top.GrpTrue b.N f) : SameGrp a b where
  e := Top.plEquiv a.N.naut b.N.naut
  pl := Top.TypesTrue.plGw_plEquiv h h'
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

theorem LevOf.transfer (b : Late B C) {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) :
    LevOf b.st I U (levCh b L) :=
  ⟨levIs_tr b h.is, (by with_unfolding_all exact ((congrArg (chFr b) h.C) :)), (by with_unfolding_all exact (h.xiH :)), (by with_unfolding_all exact (h.Pg :)), (by with_unfolding_all exact (h.Q :)), (by with_unfolding_all exact (h.beta :))⟩

theorem GoodSet.transfer (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : ∀ g, b.D.ntypes.e0.coeff ((eR.trans s.iso) g) = a.D.ntypes.e0.coeff (eR g) := fun g => s.e0 (eR g)
  obtain ⟨h1, h2⟩ := (goodSet_iff a.st (px := px) eR Xg).1 h
  refine (goodSet_iff b.st (px := px) _ Xg).2 ⟨fun χ => (h1 χ).trans (and_congr_right fun _ => ?_), fun g => (h2 g).trans (e g).symm⟩
  exact Eq.congr_left (Finset.sum_congr rfl fun g _ => congrArg (· * B.embLL (χ g)) (e g).symm)

theorem GrpAt.pl_transfer (s : SameGrp a b) (h : GrpAt a.st I) :
    ∃ plg : (Σ k : Fin 2, b.D.nd.PlG k) ≃ (B.primes px).vGs,
      ∀ kv, ((plg kv).1 : Pl b.D.host.E) = b.D.naut.plGw kv.1 kv.2 ∧ I.C.P.Div kv.1 (plg kv).1 := by
  obtain ⟨plg, h1⟩ := h.pl
  exact ⟨s.back.trans plg, fun kv => ⟨(h1 (s.back kv)).1.trans (s.pl_back kv), (h1 (s.back kv)).2⟩⟩

def Dat.transfer (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((Tr.alg (a := a) b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := (by with_unfolding_all exact ((real3 (a := a) b z.R) :)))
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf (a := a) b z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr (a := a) b s z.pins) :)))
    (lev := (by with_unfolding_all exact ((z.lev.transfer b) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((GoodSet.transfer s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

namespace Dat

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem transfer_Xg : (z.transfer s).Xg = z.Xg := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).Xg)) :))

theorem transfer_tr : (z.transfer s).tr = z.tr := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).tr)) :))

theorem transfer_field : ((z.transfer s).core.Q.c.F : Type) = z.core.Q.c.F := (by with_unfolding_all exact ((Eq.refl (((z.transfer s).core.Q.c.F : Type))) :))

theorem transfer_mu : (z.transfer s).R.mu = (z.R.mu) := (Eq.refl (transfer s z).R.mu)

theorem transfer_twPl : (z.transfer s).R.twPl = (z.R.twPl) := (Eq.refl (transfer s z).R.twPl)

theorem transfer_kap : (z.transfer s).R.kap = z.R.kap := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).R.kap)) :))

theorem transfer_liftScalars : (z.transfer s).R.lam3 = (z.R.lam3) := (Eq.refl (transfer s z).R.lam3)

theorem transfer_errorTerms : (z.transfer s).R.err0 = (z.R.err0) := (Eq.refl (transfer s z).R.err0)

theorem transfer_phs : (z.transfer s).R.phs = (z.R.phs) := (Eq.refl (transfer s z).R.phs)

theorem transfer_Pg : (z.transfer s).R.Pg = (z.R.Pg) := (Eq.refl (transfer s z).R.Pg)

theorem transfer_eG : (z.transfer s).R.eG = (z.R.eG) := (Eq.refl (transfer s z).R.eG)

theorem transfer_cG : (z.transfer s).cG = (by with_unfolding_all exact ((z.cG.trans s.iso) :)) := (by with_unfolding_all exact ((Eq.refl ((z.transfer s).cG)) :))

theorem transfer_nW : (z.transfer s).R.nW = (z.R.nW) := (Eq.refl (transfer s z).R.nW)

theorem transfer_FW : (z.transfer s).R.FW = (z.R.FW) := (Eq.refl (transfer s z).R.FW)

theorem transfer_HX : (z.transfer s).R.HX = (z.R.HX) := (Eq.refl (transfer s z).R.HX)

theorem transfer_HV : (z.transfer s).R.HV = (z.R.HV) := (Eq.refl (transfer s z).R.HV)

theorem transfer_HE : (z.transfer s).R.HE = (z.R.HE) := (Eq.refl (transfer s z).R.HE)

theorem transfer_HW : (z.transfer s).R.HW = (z.R.HW) := (Eq.refl (transfer s z).R.HW)

theorem transfer_Th : (z.transfer s).R.Th = (z.R.Th) := (Eq.refl (transfer s z).R.Th)

theorem transfer_thG : (z.transfer s).R.thG = (z.R.thG) := (Eq.refl (transfer s z).R.thG)

theorem transfer_zs : zsOf z.R z.F = (by with_unfolding_all exact ((zsOf (z.transfer s).R (z.transfer s).F) :)) :=
  (by with_unfolding_all exact ((congrArg Cx.CxData.zs (toCx3_eq (a := a) b z.R z.F)) :))

theorem transfer_EEat : z.R.toRealDat.EEat = ((transfer s z).R.EEat) := (eeat_eq b z.R.toRealDat)

theorem transfer_Wall : z.R.toRealDat.Wall = ((transfer s z).R.Wall) := (wall_eq b z.R.toRealDat)

theorem transfer_Wat : z.R.toRealDat.Wat = ((transfer s z).R.Wat) := (wat_eq b z.R.toRealDat)

theorem transfer_CC : z.R.toRealDat.CC = ((transfer s z).R.CC) := (cc_eq b z.R.toRealDat)

theorem eigenspace_eq_of_transfer : z.R.EEp3 = ((transfer s z).R.EEp3) := (realAdelicInertTransport_typeRows_eq b z.R)

theorem transfer_formParts : z.R.Wp3 = ((transfer s z).R.Wp3) := (wp3_apply_eq_sq_mul_sub_sq_mul b z.R)

theorem transfer_toCx3 : z.R.toCx3 z.F = ((transfer s z).R.toCx3 (transfer s z).F) := (toCx3_eq b z.R z.F)

theorem transfer_s0Of : HEq (s0Of z.R z.F) (s0Of (z.transfer s).R (z.transfer s).F) :=
  (by with_unfolding_all exact ((congr_arg_heq (fun X : type_of% (z.R.toCx3 z.F) => X.data z.F.cr false) (toCx3_eq (a := a) b z.R z.F)) :))

theorem transfer_s1Of : HEq (s1Of z.R z.F) (s1Of (z.transfer s).R (z.transfer s).F) :=
  (by with_unfolding_all exact ((congr_arg_heq (fun X : type_of% (z.R.toCx3 z.F) => X.data z.F.cr true) (toCx3_eq (a := a) b z.R z.F)) :))

theorem nonzeroIndexPlaces_transferAlongSameFiniteGroup (F0 : HeightOneSpectrum (𝓞 B.LL) → Fin B.R.m → ℝ) : z.W1 F0 = (z.transfer s).W1 F0 :=
  (by with_unfolding_all exact ((congrArg (fun X : type_of% (z.R.toCx3 z.F) => {w : B.places.Pl | ∃ j,
    ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
      IndefData.Iw (Df := (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs) (((X.data z.F.cr false))) j
          (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
        Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
                  (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
          (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
            (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ F0 w' j ≠ 0}) (toCx3_eq (a := a) b z.R z.F)) : _))

variable {z}

theorem holds_transfer (h : Holds z.R z.F) : Holds (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((holds_tr (a := a) b h) :))

theorem exAt_transfer (h : z.R.toRealDat.ExAt) : (z.transfer s).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr (a := a) b h) :))

theorem inGeo_transfer (h : InGeo z.geo) : InGeo (z.transfer s).geo := (by with_unfolding_all exact ((inGeo_tr (a := a) b h) :))

theorem errEq_transfer (h : ErrEq z.R z.F) : ErrEq (z.transfer s).R (z.transfer s).F := (by with_unfolding_all exact ((errEq_tr (a := a) b h) :))

end Dat

theorem nonempty_dat_iff (s : SameGrp a b) : Nonempty (Dat a.st I hX T Wt) ↔ Nonempty (Dat b.st I hX T Wt) :=
  ⟨fun ⟨z⟩ => ⟨z.transfer s⟩, fun ⟨z⟩ => ⟨z.transfer s.symm⟩⟩

def Dat.transferTo {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {W' : RowsRest X.B X.C} {V' : DivStage X.B X.C W'} {S' : SStage X.B X.C W'} {N' : NStage X.B X.C W'}
    {G' : GJStage X.B X.C} (s : SameGrp X.toLate ⟨W', V', S', N', G'⟩) (z : Dat X I hX T Wt) :
    Dat ⟨X.B, X.C, W', V', S', N', G'⟩ I hX T Wt :=
  Dat.transfer (a := X.toLate) s z

section Rows

variable {ix : C.Tup ≃ I.ι} {p0 : BaseLevelRowSide a.D}

def RowsAre.tr (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0) : RowsAre c.to.st I hX T Wt ix (baseLevelRowSideTransport c p0) :=
  @RowsAre.mk c.to.st px I hX T Wt ix (baseLevelRowSideTransport c p0)
    (z := r.z.transfer c.same)
    (intersectionNumber_baseChange := Dat.holds_transfer c.same r.intersectionNumber_baseChange)
    (Y := (by with_unfolding_all exact ((read c r.Y) :)))
    (Z := (by with_unfolding_all exact ((readL c r.Z) :)))
    (tup_ix := (by with_unfolding_all exact (r.tup_ix :)))

namespace RowsAre

variable (c : Refill a) (r : RowsAre a.st I hX T Wt ix p0)

theorem tr_z_eq_transfer : (r.tr c).z = r.z.transfer c.same := rfl

theorem tr_tup : (r.tr c).Y.tup = (r.Y.tup) := (Eq.refl (tr c r).Y.tup)

theorem tr_jA : (r.tr c).Y.jA = (r.Y.jA) := (Eq.refl (tr c r).Y.jA)

theorem transfer_baseForms : (r.tr c).Y.jA0 = (r.Y.jA0) := (Eq.refl (tr c r).Y.jA0)

theorem tr_eMt : (r.tr c).Y.eMt = (r.Y.eMt) := (Eq.refl (tr c r).Y.eMt)

theorem tr_eE : (r.tr c).Y.eE = (r.Y.eE) := (Eq.refl (tr c r).Y.eE)

theorem tr_jW : (r.tr c).Z.jW = (r.Z.jW) := (Eq.refl (tr c r).Z.jW)

theorem tr_eRR : HEq r.Z.eRR (r.tr c).Z.eRR :=
  (by with_unfolding_all exact ((congr_arg_heq (eRRu r.Z) (parts_eq (a := a) c.to r.z.R r.z.F)) :))

theorem transfer_rowLattice : HEq r.Z.eRR0 (r.tr c).Z.eRR0 :=
  (by with_unfolding_all exact ((congr_arg_heq (riemannRochSpaceCoordinateEquiv r.Z) (parts_eq (a := a) c.to r.z.R r.z.F)) :))

end RowsAre

def RowsAre.trSG (r : RowsAre a.st I hX T Wt ix p0) (S : SStage B C a.W) (G : GJStage B C) :
    RowsAre ⟨B, C, a.W, a.V, S, a.N, G⟩ I hX T Wt ix ((baseLevelRowSideTransport (Refill.ofSG a S G) p0)) :=
  (by with_unfolding_all exact ((r.tr (Refill.ofSG a S G)) :))

theorem Refill.ofDiv_D (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) :
    (Refill.ofDiv a L h).to.D = GlobalTheory.EX.OB.setDiv a.D L h := rfl

theorem Refill.refill_divisionSide (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide a.D) :
    baseLevelRowSideTransport (Refill.ofDiv a L h) p0 = (@BaseLevelRowSide.mk (EX.OB.setDiv (@Late.D B C a) L h) (@EX.OB.sideTr (@Late.D B C a) L h (@Rows.Data.EE0 (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0 (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0i (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@Rows.Data.instEE0f (EX.OB.setDiv (@Late.D B C a) L h).R (EX.OB.setDiv (@Late.D B C a) L h).what₂) (@BaseLevelRowSide.s (@Late.D B C a) p0))) :=
  (by with_unfolding_all exact ((Eq.refl (baseLevelRowSideTransport (Refill.ofDiv a L h) p0)) :))

def RowsAre.trDiv (r : RowsAre a.st I hX T Wt ix p0) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) :
    RowsAre (Refill.ofDiv a L h).to.st I hX T Wt ix (baseLevelRowSideTransport (Refill.ofDiv a L h) p0) :=
  r.tr (Refill.ofDiv a L h)

end Rows

example (a : Late B C) (g : G0g a.D.nd) : (SameGrp.ofN a.N a.V a.V a.S a.S a.G a.G).iso g = g := rfl

example (a : Late B C) : (Refill.ofSG a a.S a.G).to = a := rfl

example (s : SameGrp a b) (g : G0g a.D.nd) (k : Fin 2) (v : b.D.nd.PlG k) : s.iso g ⟨k, v⟩ = g ⟨k, (s.e k).symm v⟩ := rfl

example (s : SameGrp a b) (z : Dat a.st I hX T Wt) : ((z.transfer s).transfer s.symm).R.twPl = z.R.twPl :=
  (by with_unfolding_all exact ((Eq.refl z.R.twPl) :))

end GlobalTheory.Mem.R3

end
