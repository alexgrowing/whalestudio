import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsCharted1AtInTw
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.MemAll

noncomputable section

namespace Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

def frB {N : ℕ} (B : GL (Fin N) D.host.E) (w' : HeightOneSpectrum (𝓞 D.host.F))
    (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) : GL (Fin N) (w'.adicCompletion D.host.F) :=
  bc (((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom).comp
    (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B

def IsBaseAt {N : ℕ} (B : GL (Fin N) D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∀ (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (t : Fin N → w'.adicCompletion D.host.F),
    (∃ x ∈ Formalism.L2.Herm.locL w' Lb, ∀ a, ((X0.g u w hg).spl w' h (x a)).1 = t a) ↔
      ∀ a, (((frB X0 u w hg B w' h)⁻¹ : GL (Fin N) (w'.adicCompletion D.host.F)) :
        Matrix (Fin N) (Fin N) (w'.adicCompletion D.host.F)).mulVec t a ∈ w'.adicCompletionIntegers D.host.F

variable {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

section Step

variable {u} {i : ℕ} {hi : i + 1 ≤ D.R.m}

def ulocOf (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)) :=
  ((Fo.K β).lev.Uloc v).comap (reGL (rankN D (i + 1) hi) _).toMonoidHom

def lbOf (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E) :=
  reL (rankN D (i + 1) hi).symm (Fo.K β).lev.Lb

set_option maxHeartbeats 4000000 in

theorem sameU_of (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) : SameUlocJ hi (Fo.K β).lev (ulocOf Fo β) := fun v =>
  (Subgroup.map_comap_eq_self_of_surjective (f := (reGL (rankN D (i + 1) hi) _).toMonoidHom)
    (reGL (rankN D (i + 1) hi) _).surjective ((Fo.K β).lev.Uloc v)).symm

end Step

set_option maxHeartbeats 1000000 in

structure StepD {i : ℕ} {hi : i + 1 ≤ D.R.m} (Fo : FormsIn M (i + 1) hi) where

  B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E
  B_lat : ∀ β, IsBaseAt X0 u w hg B (lbOf Fo β)

  ψ : ∀ β, awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ

  fin : ∀ β, Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) (D.what₂.places.resChar w))

variable {X0 u w hg}

def StepD.chart {i : ℕ} {hi : i + 1 ≤ D.R.m} {Fo : FormsIn M (i + 1) hi} (S : StepD X0 u w hg Fo) (β : Fo.Ch) :
    ChartG (X0.g u w hg) (D.sp.X (i + 1)).rank where
  J := (D.sp.X (i + 1)).gram
  Lb := lbOf Fo β
  Uloc := ulocOf Fo β
  fr := frB X0 u w hg S.B
  fr_lat := S.B_lat β
  ψ := S.ψ β
  eps := 1
  fin := S.fin β

variable (X0 u w hg) (M)

structure SiteD where
  Fo : ∀ i (hi : i + 1 ≤ D.R.m), FormsIn M (i + 1) hi
  chFin : ∀ i hi, Finite (Fo i hi).Ch
  S : ∀ i hi, StepD X0 u w hg (Fo i hi)

variable {X0 u w hg M}

theorem rank_of (X0 : Formalism.L2.Herm.Herm0 D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (i : ℕ) (hi : i < D.R.m) :
    (D.gat u w hg).P.m + (i + 1) * (Fl.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  rw [← rank_step D i hi, ht]
  have h1 := (X0.g u w hg).rk
  generalize (i + 1) * (D.R.t + 1) = q
  omega

namespace SiteD

variable (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)

def lv : Levels Fl :=
  haveI := Z.chFin
  levelsG (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_of X0 Fl ht i hi)
    (fun i hi => (Z.Fo i hi).Ch) (fun i hi β => (Z.S i hi).chart β)

theorem lv_empty (j : ℕ) (hj : D.R.m < j) : IsEmpty ((Z.lv Fl ht).comp j) :=
  haveI := Z.chFin
  levelsG_empty _ _ _ _ _ _ _ j hj

set_option maxHeartbeats 4000000 in

def loc (i : ℕ) (hi : i + 1 ≤ D.R.m) : LocIn X0 u w hg (Z.lv Fl ht) i (Z.Fo i hi).Ch :=
  haveI := Z.chFin
  haveI : ∀ β, Fintype ((Z.S i hi).chart β).comp := fun β => @Fintype.ofFinite _ ((Z.S i hi).fin β)
  locInOf (fun β => ((Z.S i hi).chart β).comp) (fun β a => ⟨hi, β, a⟩)
    (levelsG_cover (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_of X0 Fl ht i hi)
      (fun i hi => (Z.Fo i hi).Ch) (fun i hi β => (Z.S i hi).chart β) i hi)
    (fun β => lbOf (Z.Fo i hi) β) (fun β => ulocOf (Z.Fo i hi) β) (Z.S i hi).ψ
    (fun β => levelsG_tie (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_of X0 Fl ht i hi)
      (fun i hi => (Z.Fo i hi).Ch) (fun i hi β => (Z.S i hi).chart β) i hi β)
    (Z.S i hi).B

theorem loc_B (i : ℕ) (hi : i + 1 ≤ D.R.m) : (Z.loc Fl ht i hi).B = (Z.S i hi).B := rfl

theorem loc_psi (i : ℕ) (hi : i + 1 ≤ D.R.m) : (Z.loc Fl ht i hi).ψ = (Z.S i hi).ψ := rfl

theorem loc_Uloc (i : ℕ) (hi : i + 1 ≤ D.R.m) : (Z.loc Fl ht i hi).Uloc = fun β => ulocOf (Z.Fo i hi) β := rfl

theorem loc_Lb (i : ℕ) (hi : i + 1 ≤ D.R.m) : (Z.loc Fl ht i hi).Lb = fun β => lbOf (Z.Fo i hi) β := rfl

theorem frRat (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) : FrRatJ ((Z.loc Fl ht i hi).t β) (Z.loc Fl ht i hi).B :=
  fun _ _ => rfl

theorem sameU (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) :
    SameUlocJ hi ((Z.Fo i hi).K β).lev ((Z.loc Fl ht i hi).Uloc β) := sameU_of (Z.Fo i hi) β

def st (Gt : GatTies D) (i : ℕ) (hi : i + 1 ≤ D.R.m) : StepIn M (i + 1) hi (gatJ (Z.lv Fl ht) (i + 1)) :=
  stepInOf hi (Z.Fo i hi) (Z.loc Fl ht i hi) (Gt.gat_pos u w hg)

end SiteD

variable {Tw : TwForms D} {μ : D.what₂.Tup}

def SiteD.atIn (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) :
    AtIn X0 Tw u μ w hg (Z.lv Fl ht) where
  Fo := Z.Fo
  Lc := Z.loc Fl ht

def SiteD.inTw (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u μ w hg (Z.lv Fl ht) := (Z.atIn Fl ht).I Gt

def SiteD.inMem (Z : SiteD X0 u w hg (D.fm u)) (Tw : TwForms D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u D.what₂.mu0 w hg (Z.lv Fl ht) :=
  ⟨fun j hj => StepAt.ofMem (Z.st Fl ht Gt j hj)⟩

theorem SiteD.inTw_st (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (j : ℕ)
    (hj : j + 1 ≤ D.R.m) : ((Z.inTw Fl ht Gt).at' j hj).st = Z.st Fl ht Gt j hj := rfl

theorem SiteD.inMem_st (Z : SiteD X0 u w hg (D.fm u)) (Tw : TwForms D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D)
    (j : ℕ) (hj : j + 1 ≤ D.R.m) : ((Z.inMem Tw Fl ht Gt).at' j hj).st = Z.st Fl ht Gt j hj := rfl

end Formalism.MainNotions.G.ChartsLv

end
