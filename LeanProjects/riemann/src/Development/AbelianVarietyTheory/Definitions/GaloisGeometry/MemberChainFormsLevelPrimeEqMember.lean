import Mathlib
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.MemAll
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.TiedCls
import Formalism.LocalToGlobal.HermitianForms.BothLemmas
import Formalism.LocalToGlobal.HermitianForms.BothSym
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocTiesOf
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

noncomputable section

section

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

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

theorem sameU_of (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) : SameUlocJ hi (Fo.K β).lev (ulocOf Fo β) := by
  intro v
  exact (Subgroup.map_comap_eq_self_of_surjective (reGL (rankN D (i + 1) hi) _).surjective _).symm

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
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := (X0.g u w hg).rk
  have hr : (D.sp.X (i + 1)).rank = D.R.N (i + 1) := rankN D (i + 1) (by omega)
  rw [hr]
  show _ = D.R.k + (i + 1) * (D.R.t + 1)
  rw [ht, ← hk]
  ring

namespace SiteD

variable (Z : SiteD X0 u w hg M) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t)

def lv : Levels Fl :=
  haveI := Z.chFin
  levelsG (X0.g u w hg) Fl D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_of X0 Fl ht i hi)
    (fun i hi => (Z.Fo i hi).Ch) (fun i hi β => (Z.S i hi).chart β)

theorem lv_empty (j : ℕ) (hj : D.R.m < j) : IsEmpty ((Z.lv Fl ht).comp j) := by
  have := Z.chFin
  exact levelsG_empty (X0.g u w hg) Fl D.R.m _ _ _ _ j hj

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

theorem frRat (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) : FrRatJ ((Z.loc Fl ht i hi).t β) (Z.loc Fl ht i hi).B := by
  intro w' h
  rfl

theorem sameU (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (Z.Fo i hi).Ch) :
    SameUlocJ hi ((Z.Fo i hi).K β).lev ((Z.loc Fl ht i hi).Uloc β) := by
  rw [Z.loc_Uloc Fl ht i hi]
  exact sameU_of (Z.Fo i hi) β

def st (Gt : GatTies D) (i : ℕ) (hi : i + 1 ≤ D.R.m) : StepIn M (i + 1) hi (gatJ (Z.lv Fl ht) (i + 1)) :=
  stepInOf hi (Z.Fo i hi) (Z.loc Fl ht i hi) (Gt.gat_pos u w hg)

end SiteD

variable {Tw : TwForms D} {μ : D.what₂.Tup}

def SiteD.inMem (Z : SiteD X0 u w hg (D.fm u)) (Tw : TwForms D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) :
    CmpJIn Tw u D.what₂.mu0 w hg (Z.lv Fl ht) :=
  ⟨fun j hj => StepAt.ofMem (Z.st Fl ht Gt j hj)⟩

theorem SiteD.inMem_st (Z : SiteD X0 u w hg (D.fm u)) (Tw : TwForms D) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D)
    (j : ℕ) (hj : j + 1 ≤ D.R.m) : ((Z.inMem Tw Fl ht Gt).at' j hj).st = Z.st Fl ht Gt j hj := rfl

end GlobalTheory.Port
end
section

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_compG_re {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (h : a = b)
    (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (Uloc' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F))) (p : ℕ)
    (hf : Finite (compG σ J' Uloc' p)) :
    Finite (compG σ J (fun v => (Uloc' v).comap (reGL h _).toMonoidHom) p) := by
  cases h
  have hJJ : J' = J := by
    ext x y
    rw [hJ]
    rfl
  subst hJJ
  have hU : (fun v => (Uloc' v).comap (reGL rfl _).toMonoidHom) = Uloc' := by
    funext v
    ext g
    exact Iff.rfl
  rw [hU]
  exact hf

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 4000000 in

theorem fin_of (Fo : FormsIn M (i + 1) hi) (β : Fo.Ch) (p : ℕ) :
    Finite (compG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) p) := by
  have hcls := Finite.of_surjective _ (Fo.K β).y_bij.2
  have hN : Finite (compG (sigD D) (gramN D (i + 1) hi) (Fo.K β).lev.Uloc p) :=
    finite_compG (σE := sigD D) (J := gramN D (i + 1) hi) (Uloc := (Fo.K β).lev.Uloc) (p := p)
      (U := (Fo.K β).lev.U) (hU := fun x hx => ((Fo.K β).lev.U_eq x).1 hx) (hfin := hcls)
  exact finite_compG_re (rankN D (i + 1) hi) (sigD D) (D.sp.X (i + 1)).gram (gramN D (i + 1) hi)
    (fun _ _ => rfl) (Fo.K β).lev.Uloc p hN

end GlobalTheory.Port
end
section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mem

variable {D : D7} {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}

set_option maxHeartbeats 2000000 in

def formsInOne (V : ValTied u eV i hi K) (dt : DetTie K.lev) : FormsIn (D.fm u) i hi where
  T := (D.mem u).A.T
  bad := badG D
  eY := V.eY
  okW := fun _ => True
  Ch := Unit
  chOf := chU u i
  lat := clsCrd D u i hi
  K := oneChart K
  val := valTied_toG V
  tw := fun _ => DetTw.ofChiD dt (cTw D i)

end Mem

section Mem2

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 2000000 in

def formsInMid (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (dt : ∀ β, DetTie (F.ch i h1 h2 β).lev) :
    FormsIn (D.fm u) i (le_of_succ_m h2) where
  T := (D.mem u).A.T
  bad := badG D
  eY := F.eYC i h1 h2
  okW := fun _ => True
  Ch := Ch i
  chOf := chOf i
  lat := fun c => clsCrd D u i (le_of_succ_m h2) c
  K := F.ch i h1 h2
  val := F.valC i h1 h2
  tw := fun β => DetTw.ofChiD (dt β) (cTw D i)

structure MemDt (F : FormsTiedSym D u Ch chOf) where
  top : ∀ i (hi : i ≤ D.R.m) (h : i = D.R.m), DetTie (F.cls i hi (Or.inr h)).lev
  mid : ∀ i (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i), DetTie (F.ch i h1 h2 β).lev

open Classical in

def formsInMem (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) : FormsIn (D.fm u) (i + 1) hi :=
  if h : i + 1 = D.R.m then formsInOne (F.val (i + 1) hi (Or.inr h)) (dt.top (i + 1) hi h)
  else formsInMid F (i + 1) (one_le i) (by omega) (dt.mid (i + 1) (one_le i) (by omega))

theorem formsInMem_top (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) (h : i + 1 = D.R.m) :
    formsInMem F dt i hi = formsInOne (F.val (i + 1) hi (Or.inr h)) (dt.top (i + 1) hi h) := by
  rw [formsInMem, dif_pos h]

theorem formsInMem_mid (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) (h : i + 1 + 1 ≤ D.R.m) :
    formsInMem F dt i hi = formsInMid F (i + 1) (one_le i) h (dt.mid (i + 1) (one_le i) h) := by
  have hne : ¬ i + 1 = D.R.m := by omega
  rw [formsInMem, dif_neg hne]

theorem formsInMem_fin [∀ i, Finite (Ch i)] (F : FormsTiedSym D u Ch chOf) (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) :
    Finite (formsInMem F dt i hi).Ch := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    exact (inferInstance : Finite Unit)
  · have h' : i + 1 + 1 ≤ D.R.m := by omega
    rw [formsInMem_mid F dt i hi h']
    exact (inferInstance : Finite (Ch (i + 1)))

end Mem2

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

theorem fl_t (ex : Extra D L hT Gi Gl K Dx cX) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (Gl.Fl u w hg).t = D.R.t := by
  exact (ex.ker u w hg).fl_t

end Rec

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Step

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

def BaseEx (Fo : FormsIn M (i + 1) hi) : Prop :=
  ∃ B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E B).1 * gramN D (i + 1) hi *
      (reGL (rankN D (i + 1) hi) D.host.E B).1 = 1 ∧ ∀ β, IsBaseAt X0 u w hg B (lbOf Fo β)

variable {u w hg}

set_option maxHeartbeats 1000000 in

def PsiEx (Fo : FormsIn M (i + 1) hi) (e : D.what₂.LL →+* (D.gat u w hg).Kf) : Prop :=
  ∀ β, ∃ ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (ulocOf Fo β) (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ,
    UnitCharacterChartCompatibility hi (Fo.K β).lev e ψ

variable {X0}

def StepD.ofEx {Fo : FormsIn M (i + 1) hi} {e : D.what₂.LL →+* (D.gat u w hg).Kf} (hB : BaseEx X0 u w hg Fo) (hψ : PsiEx Fo e) :
    StepD X0 u w hg Fo where
  B := hB.choose
  B_lat := hB.choose_spec.2
  ψ := fun β => (hψ β).choose
  fin := fun β => fin_of Fo β _

theorem StepD.ofEx_std {Fo : FormsIn M (i + 1) hi} {e : D.what₂.LL →+* (D.gat u w hg).Kf} (hB : BaseEx X0 u w hg Fo) (hψ : PsiEx Fo e) :
    cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E (StepD.ofEx hB hψ).B).1 * gramN D (i + 1) hi *
      (reGL (rankN D (i + 1) hi) D.host.E (StepD.ofEx hB hψ).B).1 = 1 := by
  exact hB.choose_spec.1

theorem StepD.ofEx_psi {Fo : FormsIn M (i + 1) hi} {e : D.what₂.LL →+* (D.gat u w hg).Kf} (hB : BaseEx X0 u w hg Fo) (hψ : PsiEx Fo e)
    (β : Fo.Ch) : UnitCharacterChartCompatibility hi (Fo.K β).lev e ((StepD.ofEx hB hψ).ψ β) := by
  exact (hψ β).choose_spec

end Step

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

end Rec

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat
  Formalism.L2.KerInert.SecondKernelProjection

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RatUsed (D : D7) (Tw : TwForms D) : Prop :=
  ∀ u μ, DV.Used D μ → ∀ j, j < D.R.m → (Tw.fm u μ).KRat j

section One

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def FillOK (μ : D.what₂.Tup) (Lv : Levels Fl) : Prop := ∀ j, D.R.m < j → Lv.comp j → Nonempty ((D.chTw u μ).cls j)

theorem fillOK_of_empty (hE : ∀ j, D.R.m < j → IsEmpty (Lv.comp j)) : FillOK μ Lv := by
  intro j hj a
  exact ((hE j hj).false a).elim

theorem fillOK_of_nonempty (hN : ∀ j, D.R.m < j → Nonempty ((D.chTw u μ).cls j)) : FillOK μ Lv := by
  intro j hj _
  exact hN j hj

def fillOf (hF : FillOK μ Lv) : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j := fun j hj a => (hF j hj a).some

structure LabHyp (I : CmpJIn Tw u μ w h Lv) : Prop where
  onCh : OnChain I
  chX : ∀ j hj, ChX (I.at' j hj).st
  fill : FillOK μ Lv

theorem labHyp_of {I : CmpJIn Tw u μ w h Lv} (X : LabIn I) : LabHyp I := by
  exact ⟨X.onCh, X.chX, fun j hj a => ⟨X.fill j hj a⟩⟩

def labOf {I : CmpJIn Tw u μ w h Lv} (hI : LabHyp I) (fl_t : Fl.t = D.R.t) (fl_m : Fl.mm = D.R.m)
    (c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv) (rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j)
    (dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam) : LabIn I where
  onCh := hI.onCh
  chX := hI.chX
  fl_t := fl_t
  fl_m := fl_m
  c0 := c0
  fill := fillOf hI.fill
  rat := rat
  dgam := dgam

end One

section Built

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

structure ChartLocalForms {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    (Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn M (j + 1) hj) (Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch) : Prop where
  sameU : ∀ j hj β, SameUlocJ hj ((Fo j hj).K β).lev ((Lc j hj).Uloc β)
  frRat : ∀ j hj β, FrRatJ ((Lc j hj).t β) (Lc j hj).B
  hypC : ∀ j hj β, HypTJC ((Lc j hj).t β)

variable (X0 u w h Lv) in

structure AtInM where
  Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn (D.fm u) (j + 1) hj
  Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch

def AtInM.I (Z : AtInM X0 u w h Lv) (Tw : TwForms D) (Gt : GatTies D) : CmpJIn Tw u D.what₂.mu0 w h Lv :=
  ⟨fun j hj => StepAt.ofMem (stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h))⟩

theorem labHyp_atInM (Z : AtInM X0 u w h Lv) (Tw : TwForms D) (Gt : GatTies D) (hZ : ChartLocalForms Z.Fo Z.Lc) (hF : FillOK D.what₂.mu0 Lv) :
    LabHyp (Z.I Tw Gt) where
  onCh := fun _ _ => (D.memberColumns_twistedChain_base u).symm
  chX := fun j hj => chX_stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) (hZ.sameU j hj) (hZ.frRat j hj) (hZ.hypC j hj)
  fill := hF

end Built

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

theorem fl_t_eq (ex : Extra D L hT Gi Gl K Dx cX) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (Gl.Fl u w hg).t = D.R.t := by
  exact (ex.ker u w hg).fl_t

theorem fl_mm_eq (ex : Extra D L hT Gi Gl K Dx cX) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (Gl.Fl u w hg).mm = D.R.m := by
  exact (ex.ker u w hg).fl_m

end Rec

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem memberChainForms_levelPrime_eq_member {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) : (formsInMem F dt i hi).T = (D.mem u).A.T := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    try rfl
  · have h' : i + 1 + 1 ≤ D.R.m := by omega
    rw [formsInMem_mid F dt i hi h']
    try rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq Formalism.MainNotions.G.KAat Formalism.MainNotions.G.ChartsLv Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reL_symm {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin b → E)) :
    reL h (reL h.symm L) = L := by
  cases h
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hx
    exact ⟨x, ⟨x, hx, rfl⟩, rfl⟩

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

structure SiteRest (Z : SiteD X0 u w hg M) (c : LatCmp D) : Prop where

  std : ∀ i hi, cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B).1 = 1

  psi : ∀ i hi β, UnitCharacterChartCompatibility hi ((Z.Fo i hi).K β).lev (c.embW u w hg) ((Z.S i hi).ψ β)

  chRat : ∀ i hi β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = (((Z.Fo i hi).tw β).ch (((Z.Fo i hi).K β).y cl) : ℂ)

structure SiteGood (Z : SiteD X0 u w hg M) : Prop where
  siteGood_prime_torsion : ∀ i hi, ¬ D.what₂.places.resChar w ∣ (Z.Fo i hi).T
  bad_p : ∀ i hi, ∀ w' ∈ (Z.Fo i hi).bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal
  ok : ∀ i hi, (Z.Fo i hi).okW w

section Rec

theorem formsInMem_bad {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) : (formsInMem F dt i hi).bad = badG D := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    try rfl
  · have h' : i + 1 + 1 ≤ D.R.m := by omega
    rw [formsInMem_mid F dt i hi h']
    try rfl

theorem formsInMem_ok {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (dt : MemDt F) (i : ℕ) (hi : i + 1 ≤ D.R.m) (w : D.what₂.places.Pl) : (formsInMem F dt i hi).okW w := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top F dt i hi h]
    exact trivial
  · have h' : i + 1 + 1 ≤ D.R.m := by omega
    rw [formsInMem_mid F dt i hi h']
    exact trivial

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

end Rec

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

def ChartBaseLatticeEqSelfDualAtP (Fo : FormsIn M (i + 1) hi) (p : ℕ) : Prop :=
  ∀ β (w' : HeightOneSpectrum (𝓞 D.host.F)), ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
    Formalism.L2.Herm.locL w' (lbOf Fo β) = Formalism.L2.Herm.locL w' (Formalism.L2.Herm.crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0)

end GlobalTheory.Port
end
section
namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

open Classical in
set_option maxHeartbeats 2000000 in

def stMem (F : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) : GlobalTheory.TwU.StepCharts (D.mem u).C i hi :=
  if h : i = 0 ∨ i = D.R.m then
    ⟨(D.mem u).A.T, badG D, (F.val i hi h).eY, Unit, chU u i, clsCrd D u i hi, oneChart (F.cls i hi h)⟩
  else
    ⟨(D.mem u).A.T, badG D, F.eYC i (by omega) (by omega), Ch i, chOf i, fun c => clsCrd D u i hi c, F.ch i (by omega) (by omega)⟩

end GlobalTheory.Port
end

end
