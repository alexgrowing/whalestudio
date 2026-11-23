import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.KerTwLv

open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
  (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def frOf {N : ℕ} (B : GL (Fin N) D.host.E) (w' : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) : GL (Fin N) (w'.adicCompletion D.host.F) :=
  bc (((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom).comp
    (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def chartTw (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)) (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E)
    (fr_lat : ∀ w' h (x : Fin (D.sp.X (i + 1)).rank → w'.adicCompletion D.host.F),
      (∃ y ∈ Formalism.L2.Herm.locL w' (T.lev u μ (i + 1) (one_le i) hi β).Lb, ∀ a, ((X0.g u w hg).spl w' h (y a)).1 = x a) ↔
        ∀ a, (((frOf X0 u w hg B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)) :
          Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)).mulVec x a ∈
            w'.adicCompletionIntegers D.host.F)
    (ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w) →*
      (D.gat u w hg).Oˣ)
    (fin : Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w))) :
    ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank where
  J := (D.sp.X (i + 1)).gram
  Lb := (T.lev u μ (i + 1) (one_le i) hi β).Lb
  Uloc := (T.lev u μ (i + 1) (one_le i) hi β).Uloc
  fr := frOf X0 u w hg B
  fr_lat := fr_lat
  ψ := ψ
  eps := 1
  fin := fin

theorem rank_lv (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ) (hi : i < D.R.m) :
    (D.gat u w hg).P.m + (i + 1) * (Fl.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  have hk := Gt.gat_k u w hg
  rw [← rank_step D i hi, ht]
  omega

instance chFin (i : ℕ) : Finite (T.Ch u μ i) := T.ChFin u μ i

abbrev levelsTwG (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
    (St : ∀ i (_ : i < D.R.m), T.Ch u μ (i + 1) → ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank) : Levels Fl :=
  levelsG (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) St

structure ChData where
  B : ∀ i (_ : i + 1 ≤ D.R.m), GL (Fin (D.sp.X (i + 1)).rank) D.host.E
  fr_lat : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)) w' h (x : Fin (D.sp.X (i + 1)).rank → w'.adicCompletion D.host.F),
      (∃ y ∈ Formalism.L2.Herm.locL w' (T.lev u μ (i + 1) (one_le i) hi β).Lb, ∀ a, ((X0.g u w hg).spl w' h (y a)).1 = x a) ↔
        ∀ a, (((frOf X0 u w hg (B i hi) w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)) :
          Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) (w'.adicCompletion D.host.F)).mulVec x a ∈
            w'.adicCompletionIntegers D.host.F
  ψ : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)),
    awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ
  fin : ∀ i (hi : i + 1 ≤ D.R.m) (β : T.Ch u μ (i + 1)),
    Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (T.lev u μ (i + 1) (one_le i) hi β).Uloc (D.what₂.places.resChar w))

variable {T X0 u μ w hg}

abbrev ChData.St (Cd : ChData T X0 u μ w hg) (i : ℕ) (hi : i < D.R.m) (β : T.Ch u μ (i + 1)) :
    ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank :=
  chartTw T X0 u μ w hg i hi β (Cd.B i hi) (Cd.fr_lat i hi β) (Cd.ψ i hi β) (Cd.fin i hi β)

abbrev ChData.Lv (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) : Levels Fl :=
  levelsTwG T X0 u μ w hg Gt Fl ht Cd.St

def ChData.Lc (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ)
    (hi : i + 1 ≤ D.R.m) : LocIn X0 u w hg (Cd.Lv Gt Fl ht) i (T.Ch u μ (i + 1)) :=
  haveI : ∀ β, Fintype (Cd.St i hi β).comp := fun β => haveI := (Cd.St i hi β).fin; Fintype.ofFinite _
  locInOf (fun β => (Cd.St i hi β).comp) (fun β a => ⟨hi, β, a⟩)
    (levelsG_cover (X0.g u w hg) Fl D.R.m _ (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) Cd.St i hi)
    (fun β => (T.lev u μ (i + 1) (one_le i) hi β).Lb) (fun β => (T.lev u μ (i + 1) (one_le i) hi β).Uloc) (Cd.ψ i hi)
    (fun β => levelsG_tie (X0.g u w hg) Fl D.R.m _ (rank_lv u w hg Gt Fl ht) (fun i _ => T.Ch u μ (i + 1)) Cd.St i hi β)
    (Cd.B i hi)

theorem ChData.empty (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (j : ℕ)
    (hj : D.R.m ≤ j) : IsEmpty ((Cd.Lv Gt Fl ht).compS j) :=
  ⟨fun c => absurd c.1 (by omega)⟩

section Ties
variable {Tw : TwForms D} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} (W : TwFormsTiedS D Tw T J F) (hμ : μ ≠ D.what₂.mu0)
  (Cd : ChData T X0 u μ w hg) (Gt : GatTies D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)
  (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)

theorem ChData.frRat (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    FrRatJ ((Cd.Lc Gt Fl ht j hj).t β) (Cd.Lc Gt Fl ht j hj).B :=
  fun _ _ => rfl

set_option maxHeartbeats 4000000 in

theorem ChData.sameU (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    SameUlocJ hj ((formsInTw W u μ hμ j hj (dt j hj)).K β).lev ((Cd.Lc Gt Fl ht j hj).Uloc β) :=
  (W.car u μ hμ (j + 1) (one_le j) hj β).Uloc_eq

set_option maxHeartbeats 4000000 in

theorem ChData.Lb_eq (j : ℕ) (hj : j + 1 ≤ D.R.m) (β : T.Ch u μ (j + 1)) :
    ((formsInTw W u μ hμ j hj (dt j hj)).K β).lev.Lb = reL (rankN D (j + 1) hj) ((Cd.Lc Gt Fl ht j hj).Lb β) :=
  (W.car u μ hμ (j + 1) (one_le j) hj β).Lb_eq

end Ties

end GlobalTheory.Mem.Top.KerTwLv
