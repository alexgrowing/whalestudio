import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.ProjectiveLattices.FullXi
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.PageFix

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta
open Formalism.L2.Host (CharFrame HChar)
open GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Plug

section Record

variable {D : D7}

structure Tied (EX : ErrX D) (J : CoreJ D) (C : CharFrame D) : Prop where
  lawsJ : LawsJ J
  core : CorePin J.toCore C.P.pb
  field : FieldTies D C
  half : HalfAt EX C

def FinOf (δ : HChar D.host.E) (de : (AfE D)ˣ →* ℂˣ) : Prop :=
  ∃ χ : (AE D)ˣ →* Circle, Formalism.IndefR.Links.ChrEq χ δ ∧
    ∀ (x : (AE D)ˣ) (y : (AfE D)ˣ), finPart D (x : AE D) = (y : AfE D) → ((de y : ℂˣ) : ℂ) = ((χ x : Circle) : ℂ)

def IndexAt {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) (p : ℕ) {T : Top D}
    (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) : Prop :=
  ∀ (j : ℕ) (hj : InR D j),
    HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct
        (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j)
        (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧
      Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
        (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j))
        ((recPJ h j hj).rk (kaR Tp hK j) ((recB h.toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)

def RunAt {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) (J : CoreJ D) (p : ℕ)
    (δ : HChar D.host.E) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.K), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal →
    ∃ (de : (AfE D)ˣ →* ℂˣ) (T : Full D) (h : LawsFull T) (hinj : Function.Injective D.what₂.OtoLL),
      FinOf δ de ∧ XiRec D p de ∧ T.J = J ∧ XiTilde T.xi de ∧
      T.half₂ = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ∧
      (∀ j, InR D j → GlobalTheory.FormTies.OneCover T.toTop j ∧ ∀ n, (T.dδ j n).pd = p) ∧ IndexAt Tp hK EX CK p h.p hinj

def BothRuns {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) (J : CoreJ D)
    (C : CharFrame D) : Prop :=
  RunAt Tp hK EX CK J D.host.pde C.del ∧ RunAt Tp hK EX CK J D.host.pde' C.del'

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure CF (D : D7) : Type 1 where
  J : CoreJ D
  C : CharFrame D

end Record

abbrev BdCF : BdT := fun D _ _ => CF D

def CompatibleBundle : BdP BdCF := fun _ O _ b => Tied O.ex.errX b.J b.C

def CoreSlot (𝒮 : Slots) : Prop :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z))
    (t : RowsT K w Z Wt p0), 𝒮.Rx K B f T w Z Wt p0 t → CorePin t.r.z.core.toCore f.P.pb

def cfOf {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) : CF (p.w.D p.Z) := ⟨p.x.what₂.r.z.core, Fr.at (p.w.st p.Z) p.f⟩

def pinCF (𝒮 : Slots) : PinT 𝒮 BdCF := fun _ p _ b => b = cfOf p

def RunsAlong (CK : ℝ) (𝒜 : FamClass) (σ : RawSel BdCF 𝒜) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∀ hc : 𝒜 Fm, ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    BothRuns (Fm.parT x hx i) (Fm.ex x hx i).kap_def (Fm.ex x hx i).errX CK (σ Fm hc x hx i).J (σ Fm hc x hx i).C

def NumAlong {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    GlobalTheory.BigOn.PageNum (Fm.parT x hx i) x ∧ GlobalTheory.FieldSize.HostSz (Fm.D x i).host (Fm.L x i).sc.L ∧
      ∀ C, FieldTies (Fm.D x i) C → FieldSmall (Fm.D x i) (Fm.L x i)

end GlobalTheory.Plug

end
