import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Wp3ApplyEqSqMulSubSqMul

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.FWT GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}

abbrev setCd (c : CDHaar) : Late B C := { b with G := { b.G with cd := c } }

theorem lawsM_tr {T : Core a.D} (h : LawsM T) : LawsM (core b T) := by
  have key : ∀ c : CDHaar, c = a.G.cd → LawsM (core (setCd b c) T) := by
    rintro _ rfl
    constructor
    case pins => exact (by with_unfolding_all exact (h.pins :))
    case half => exact (by with_unfolding_all exact (h.half :))
    case evalWD => exact (by with_unfolding_all exact (h.evalWD :))
    case unf => exact (by with_unfolding_all exact (h.unf :))
    case unTest => exact (by with_unfolding_all exact (h.unTest :))
    case chiTriv => exact (by with_unfolding_all exact (h.chiTriv :))
    case dictU => exact (by with_unfolding_all exact (h.dictU :))
    case spaceW => exact (by with_unfolding_all exact (h.spaceW :))
    case levelK => exact (by with_unfolding_all exact (h.levelK :))
    case xiAbs => exact (by with_unfolding_all exact (h.xiAbs :))
    case muUnit => exact (by with_unfolding_all exact (h.muUnit :))
    case muCont => exact (by with_unfolding_all exact (h.muCont :))
    case finVol => exact (by with_unfolding_all exact (h.finVol :))
    case cuspFD => exact (by with_unfolding_all exact (h.cuspFD :))
    case supDef => exact (by with_unfolding_all exact (h.supDef :))
    case cuspidalL2Subspace => exact (by with_unfolding_all exact (h.cuspidalL2Subspace :))
    case l2Def => exact (by with_unfolding_all exact (h.l2Def :))
    case unitIndep => exact (by with_unfolding_all exact (h.unitIndep :))
    case ptNe => exact (by with_unfolding_all exact (h.ptNe :))
  exact (by with_unfolding_all exact ((key b.G.cd (cd_eq _ _)) :))

theorem lawsJ_tr {T : CoreJ a.D} (h : LawsJ T) : LawsJ (coreJ b T) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cUnit => exact (by with_unfolding_all exact (h.cUnit :))
  case muVal => exact (by with_unfolding_all exact (h.muVal :))
  case muConj => exact (by with_unfolding_all exact (h.muConj :))
  case intAll => exact (by with_unfolding_all exact (h.intAll :))
  case modelW => exact (by with_unfolding_all exact (h.modelW :))
  case familyUniformisationBasePointOrthogonal => exact (by with_unfolding_all exact (h.familyUniformisationBasePointOrthogonal :))
  case kfHalf => exact (by with_unfolding_all exact (h.kfHalf :))
  case adPin => exact (by with_unfolding_all exact (h.adPin :))

variable {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m}

section Theta

variable {T : Core a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F} {i : Fin a.D.R.m} {Tp : Type} {tup : Tp → T0}

def omDat (O : OMDat T R i Tp tup) :
    @OMDat b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T))) iK A R)) ((i)) Tp tup :=
  @OMDat.mk b.D G _ _ Pl0 T0 (famM b A) (core b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (i :))) Tp tup
    (c' := (by with_unfolding_all exact (O.c' :)))
    (hle := (by with_unfolding_all exact (O.hle :)))
    (jL := (by with_unfolding_all exact (O.jL :)))
    (hV := (by with_unfolding_all exact (O.hV :)))
    (c0' := (by with_unfolding_all exact (O.c0' :)))
    (lev := (by with_unfolding_all exact (O.lev :)))
    (dδ := (by with_unfolding_all exact (O.dδ :)))
    (Cl' := (by with_unfolding_all exact (O.Cl' :)))
    (fCl := (by with_unfolding_all exact (O.fCl :)))
    (bad := (by with_unfolding_all exact (O.bad :)))
    (Lh := (by with_unfolding_all exact (O.Lh :)))
    (La := (by with_unfolding_all exact (O.La :)))
    (Nc := (by with_unfolding_all exact (O.Nc :)))
    (gam := (by with_unfolding_all exact (O.gam :)))
    (vol := (by with_unfolding_all exact (O.vol :)))
    (ep := (by with_unfolding_all exact (O.ep :)))
    (B := (by with_unfolding_all exact (O.B :)))
    (epF := (by with_unfolding_all exact (O.epF :)))
    (io := (by with_unfolding_all exact (O.io :)))
    (hw := (by with_unfolding_all exact (O.hw :)))
    (φ := (by with_unfolding_all exact (O.φ :)))
    (w := (by with_unfolding_all exact (O.w :)))
    (U₂ := (by with_unfolding_all exact (O.U₂ :)))
    (dict₂ := (by with_unfolding_all exact (O.dict₂ :)))
    (xi := (by with_unfolding_all exact (O.xi :)))
    (thAd := (by with_unfolding_all exact (O.thAd :)))
    (Plc := (by with_unfolding_all exact (O.Plc :)))

theorem omPins_tr {O : OMDat T R i Tp tup} {κ v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) :
    @OMDat.Pins b.D G _ _ Pl0 T0 (famM b A) (core b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T)))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) T)) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) T))) iK A R)) ((i)) Tp tup (omDat b O) ((@wt B C a b (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@Fin.val (@Late.D B C a).R.m i) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) κ)) ((v₀))
      ((ι)) ((x₀)) := by
  apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
  case lift =>
    apply (config := { synthAssignedInstances := false }) ThPinsR.mk
    case field => exact (by with_unfolding_all exact (h.lift.field :))
    case std => exact (by with_unfolding_all exact (h.lift.std :))
    case v0 => exact (by with_unfolding_all exact (h.lift.v0 :))
    case lev => exact (by with_unfolding_all exact (h.lift.lev :))
    case c0 =>
      obtain ⟨x, y, z, h1, h2⟩ := h.lift.c0
      refine ⟨(by with_unfolding_all exact (x :)), (by with_unfolding_all exact (y :)), (by with_unfolding_all exact (z :)), ?_, (by with_unfolding_all exact (h2 :))⟩
      exact (by with_unfolding_all exact ((famTie_imp b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1) :))
  case tuple =>
    intro t
    apply (config := { synthAssignedInstances := false }) ThPinsT.mk
    case reps => exact (by with_unfolding_all exact ((h.tuple t).reps :))
    case B => exact (by with_unfolding_all exact ((h.tuple t).B :))
    case xi => exact (by with_unfolding_all exact ((h.tuple t).xi :))
    case phi => exact (by with_unfolding_all exact ((h.tuple t).phi :))
    case half => exact (by with_unfolding_all exact ((h.tuple t).half :))
  case act => exact (by with_unfolding_all exact (h.act :))
  case bad => exact (by with_unfolding_all exact (h.bad :))
  case reps => exact (by with_unfolding_all exact (h.reps :))
  case ep => exact (by with_unfolding_all exact (h.ep :))
  case io => exact (by with_unfolding_all exact (h.io :))
  case w => exact (by with_unfolding_all exact (h.w :))
  case cov => exact (by with_unfolding_all exact (h.cov :))
  case cxi => exact (by with_unfolding_all exact (h.cxi :))
  case model₂ => exact (by with_unfolding_all exact (h.model₂ :))

end Theta

variable {T : CoreJ a.D} [iK : Algebra T.Q.c.F a.D.what₂.LL] {R : RealDat a.D A T.Q.c.F}

def fwTie {κ v₀} (x : FWTie T R κ v₀) :
    @FWTie b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) (by with_unfolding_all exact (alg b iK :)) (by with_unfolding_all exact (real b R :)) (fun i => by with_unfolding_all exact (wt b (κ (by with_unfolding_all exact (i :))) :)) (by with_unfolding_all exact (v₀ :)) :=
  @FWTie.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) (fun i => (by with_unfolding_all exact ((wt b (κ ((i)))) : _))) ((by with_unfolding_all exact (v₀ :)))
    (alg_eq := (by with_unfolding_all exact (x.alg_eq :)))
    (e := (by with_unfolding_all exact (x.e :)))
    (ks := (by with_unfolding_all exact (x.ks :)))
    (kap := (by with_unfolding_all exact (x.kap :)))
    (pt := (by with_unfolding_all exact (x.pt :)))
    (nrm_eq := (by with_unfolding_all exact (x.nrm_eq :)))
    (laws := lawsJ_tr b x.laws)
    (chiR := (by with_unfolding_all exact (x.chiR :)))
    (hv₀ := (by with_unfolding_all exact (x.hv₀ :)))
    (x0 := (by with_unfolding_all exact (x.x0 :)))
    (ev0 := (by with_unfolding_all exact (x.ev0 :)))
    (ev := (by with_unfolding_all exact (x.ev :)))

def geoHalf {ph : Fin a.D.R.m → ℂ} (x : GeoHalf T R ph) :
    @GeoHalf b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T)))) iK A R)) ((ph)) :=
  @GeoHalf.mk b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((by with_unfolding_all exact ((alg b iK) :))) ((by with_unfolding_all exact ((real b R) :))) ((by with_unfolding_all exact (ph :)))
    (κ := fun i => (by with_unfolding_all exact ((wt b (x.κ ((i)))) : _)))
    (v₀ := (by with_unfolding_all exact (x.v₀ :)))
    (fw := (by with_unfolding_all exact ((fwTie b x.fw) :)))
    (bar := (by with_unfolding_all exact (x.bar :)))
    (O := fun i => (by with_unfolding_all exact ((omDat b (x.O ((i)))) : _)))
    (pins := fun i => (by with_unfolding_all exact ((And.intro (x.pins ((i))).1 (omPins_tr b (x.pins ((i))).2)) : _)))
    (rhoGeo := (by with_unfolding_all exact (x.rhoGeo :)))
    (equivAll := (by with_unfolding_all exact (x.equivAll :)))
    (cTie := (by with_unfolding_all exact (x.cTie :)))
    (phase := (by with_unfolding_all exact (x.phase :)))

theorem inGeo_tr {ph : Fin a.D.R.m → ℂ} {x : GeoHalf T R ph} (h : InGeo x) :
    @InGeo b.D G _ _ Pl0 T0 (famM b A) (coreJ b T) ((@alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) iK)) ((@real B C a b G ‹Group G› ‹Fintype G› Pl0 T0 (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))))) (@instNumberFieldSubtypeComplexMemIntermediateFieldRatF_formalism (@Formalism.HC.HostRaw.E (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instField (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (@Formalism.HC.HostRaw.instNF (@Late.D B C a).R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.D B C a).R.toFrame (@Host.toHostAx (@Late.D B C a).R (@Late.D B C a).host))) (instCMHost (@Late.D B C a)) (@Par.H (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.l (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T))) (@Par.c (@Late.D B C a) (@Core.Q (@Late.D B C a) (@CoreJ.toCore (@Late.D B C a) T)))) iK A R)) ((ph)) (geoHalf b x) := by
  apply (config := { synthAssignedInstances := false }) InGeo.mk
  case jEvExists => exact (by with_unfolding_all exact (h.jEvExists :))
  case jEvBar => exact (by with_unfolding_all exact (h.jEvBar :))
  case evInj => exact (by with_unfolding_all exact (h.evInj :))
  case jUnif => exact (by with_unfolding_all exact (h.jUnif :))
  case geoAct => kexactB h.geoAct
  case latFull => exact (by with_unfolding_all exact (h.latFull :))
  case dimMatch => exact (by with_unfolding_all exact (h.dimMatch :))

end GlobalTheory.Mem.R3.Tr

end
