import Formalism.LocalToGlobal.HermitianColumns.StarConj
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.HermitianColumns.BaseModelLevelEq

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SymmetricHermitianColumns (D : D7) extends HermColsCh D where

  dt : unitaryOneFiniteAdeles D.sp.cm →* D.Dt
  dt_surj : Function.Surjective dt

  dt_ker : ∀ x : unitaryOneFiniteAdeles D.sp.cm, dt x = 1 → (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) ∈ IntegralUnitGroup D.sp.cm

  dt_open : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    IsOpen {x : unitaryOneFiniteAdeles D.sp.cm | dt x = 1}

  dt_UO : D.UO = ((IntegralUnitGroup D.sp.cm).subgroupOf (unitaryOneFiniteAdeles D.sp.cm)).map dt

  dt_rat : ∀ (z : unitary D.host.E) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) = unitaryOneRationalAdele D.host.F z →
    D.e1Dt z = dt x

  det0 : ∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (((lev0 u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Af D.host.F))) →
    D.detCls u 0 c = dt x

  detI : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det
        (((cls u i h1 hm (chOf u i c)).y ⟨c, rfl⟩ : GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] Af D.host.F))) →
    D.detCls u i c = dt x

def SymmetricGroupCompatibility (D : D7) (H : HermColsCh D) : Type :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    GLevTie (H.lev0 u) (D.gat u w hg)

def SymmetricRelativeDeterminant (D : D7) (H : SymmetricHermitianColumns D) : Prop :=
  ∀ (N : ℕ) (L L' : SDLat D.host.E N), ∀ g ∈ UstdAf D.sp.cm N, Carries g L.1 L'.1 →
    ∀ x : unitaryOneFiniteAdeles D.sp.cm, IsDetOf D.sp.cm x g → D.relDet N L L' = QuotientGroup.mk (H.dt x)

structure SymmetricCompatibleData (D : D7) where
  base : SymmetricHermitianColumns D
  atT : ∀ u, AtT D u (base.vT u) (base.Fv u)
  vol : VolumeCompatible D

structure FullTiedS (D : D7) extends SymmetricCompatibleData D where
  levelZeroCompatibility : SymmetricLevelZeroData D base.toHermColsCh atT
  g : SymmetricGroupCompatibility D base.toHermColsCh
  ad : SymmetricAdelicCompatibility D base.toHermColsCh atT
  cof : SymmetricCofactorCompatibility D base.toHermColsCh atT
  piG : PiGConstS D base.toHermColsCh atT levelZeroCompatibility
  stabMap : SymmetricStabilizerMapCompatibility D base.toHermColsCh atT
  fvI : SymmetricResidueFieldLevels D base.toHermColsCh atT
  relDet : SymmetricRelativeDeterminant D base
  std : StdTied D
  vpos : PositiveVolumeCompatible D
  baseL : SymmetricBaseCompatibility D base.toHermColsCh atT

def FullTiedS.cols {D : D7} (X : FullTiedS D) : ColsHermS D where
  base := X.base.toHermColsCh
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

def toErrXS {D : D7} (X : FullTiedS D) : ErrX D where
  piG := (X.levelZeroCompatibility D.u₀).piG
  piG_K := (X.levelZeroCompatibility D.u₀).piG_K
  piG_norm := fun i => by rw [← star_conj]; exact (X.levelZeroCompatibility D.u₀).piG_norm i
  piT := fun u => (X.atT u).piU
  piT_K := fun u => (X.atT u).piU_K
  piT_norm := fun u => (X.atT u).piU_norm
  piT_cong := fun u => (X.atT u).piU_cong
  vPl := fun u v => (X.base.vT u v).1
  vPl_inj := fun u a b h => (X.base.vT u).injective (Subtype.ext h)
  norm_mem_place_ideal := fun u v => (X.base.vT u v).2

theorem piGLevelS {D : D7} (X : FullTiedS D) : PiGLevel D X.base.lev0 (toErrXS X) := by
  intro u i v h
  have h1 := (X.levelZeroCompatibility u).splitG_pi i v h
  rw [X.piG u D.u₀] at h1
  simpa [toErrXS, inclE, star_conj] using h1

theorem piTLevelS {D : D7} (X : FullTiedS D) : PiTLevel D X.base.lev0 (toErrXS X) := by
  intro u v z hz y
  exact (X.levelZeroCompatibility u).fM_pi _ _ z (by first | exact hz | (simp only [toErrXS] at hz; exact hz)) y

def SymmetricGroupCompatibleAtPlaces (D : D7) (H : HermColsCh D) (G : SymmetricGroupCompatibility D H) (Gt : GatTies D) : Prop :=
  ∀ u w hg (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (x : 𝓞 D.host.F),
    x ∈ ((G u w hg).pl v).1.asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w
        (tauLL D (Gt.gat_pos u w hg ⟨v, s⟩) (algebraMap D.host.F D.host.E (x : D.host.F)))

def SymmetricKernelCompatibleAtPlace {D : D7} (H : HermColsCh D) (G : SymmetricGroupCompatibility D H) {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Formalism.MainNotions.G.Fills (D.gat u w hg)}
    {Lv : Formalism.MainNotions.G.Levels Fl} {Ch : Formalism.MainNotions.G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w hg Ch) : Prop :=
  ∀ (v : Fin (D.gat u w hg).P.nV) (x : D.host.E),
    (G u w hg).eQ v _ rfl (Kp.iw 0 v x) =
      ((G u w hg).spl _ ((G u w hg).pl v).2
        (inclE (F := D.host.F) (((G u w hg).pl v).1.adicCompletion D.host.F) x)).1

structure JoinTiedS {D : D7} (X : FullTiedS D) (lev : LevelData D) (eX : ErrX D) (Gt : GatTies D) : Prop where
  lev_eq : lev = X.base.lev0
  errX_eq : eX = toErrXS X
  gpl : SymmetricGroupCompatibleAtPlaces D X.base.toHermColsCh X.g Gt

structure SymmetricExtraCompatibility {D : D7} (X : FullTiedS D) {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    (ex : Extra D L hT Gi Gl K Y cX) : Prop where
  join : JoinTiedS X ex.lev ex.errX hT
  iw : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    SymmetricKernelCompatibleAtPlace X.base.toHermColsCh X.g u w h (ex.ker u w h)
  iw_pos : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    GIwPos u w h (ex.ker u w h)

theorem JoinTiedS.piG_lev {D : D7} {X : FullTiedS D} {lev : LevelData D} {eX : ErrX D} {Gt : GatTies D}
    (J : JoinTiedS X lev eX Gt) : PiGLevel D lev eX := by
  obtain ⟨rfl, rfl, _⟩ := J
  exact piGLevelS X

theorem JoinTiedS.piT_lev {D : D7} {X : FullTiedS D} {lev : LevelData D} {eX : ErrX D} {Gt : GatTies D}
    (J : JoinTiedS X lev eX Gt) : PiTLevel D lev eX := by
  obtain ⟨rfl, rfl, _⟩ := J
  exact piTLevelS X

section Sub

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def ClassTie.sub {hc : CMData F E} {S : HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)}
    {U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))} {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    {lat : cls → Submodule (𝓞 E) S.V} (T : ClassTie hc S Lb U stab lat) (p : cls → Prop) (hp : ∀ c, p c) :
    ClassTie hc S Lb U (fun c : {c // p c} => stab c.1) (fun c => lat c.1) where
  y := fun c => T.y c.1
  y_bij := T.y_bij.comp (f := fun c : {c // p c} => c.1)
    ⟨Subtype.val_injective, fun c => ⟨⟨c, hp c⟩, rfl⟩⟩
  y_lat := fun c => T.y_lat c.1
  stabI := fun c => T.stabI c.1
  stabI_inj := fun c => T.stabI_inj c.1
  stabI_range := fun c => T.stabI_range c.1

def FvTie.sub {hc : CMData F E} {S : HSpace E} {Lb : Submodule (𝓞 E) (Fin S.rank → E)} {cls : Type}
    {y : cls → UAf hc S} {lat : cls → Submodule (𝓞 E) S.V} {w : HeightOneSpectrum (𝓞 F)}
    {k : Type} [AddCommGroup k] {fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k}
    (T : FvTie hc S Lb y lat w k fz) (p : cls → Prop) :
    FvTie hc S Lb (fun c : {c // p c} => y c.1) (fun c => lat c.1) w k (fun c z => fz c.1 z) where
  fb := T.fb
  fvI := fun c z t h => T.fvI c.1 z t h

end Sub

def HermCols.toCh {D : D7} (H : HermCols D) : HermColsCh D where
  lev0 := H.lev0
  Ch := fun _ _ => PUnit
  ChFin := fun _ _ => inferInstance
  Ch_m := fun _ => ⟨inferInstance⟩
  chOf := fun _ _ _ => PUnit.unit
  lev := fun u i h1 hm _ => H.lev u i h1 hm
  cls := fun u i h1 hm β => (H.cls u i h1 hm).sub (fun _ => PUnit.unit = β) (fun _ => Subsingleton.elim _ _)
  vT := H.vT
  Fv := H.Fv

def HermTied.toS {D : D7} (H : HermTied D) : SymmetricHermitianColumns D where
  toHermColsCh := H.toHermCols.toCh
  dt := H.dt
  dt_surj := H.dt_surj
  dt_ker := H.dt_ker
  dt_open := H.dt_open
  dt_UO := H.dt_UO
  dt_rat := H.dt_rat
  det0 := H.det0
  detI := fun u i h1 hm c x h => H.detI u i h1 hm c x h

def FullTied.toS {D : D7} (X : FullTied D) : FullTiedS D where
  base := X.base.toS
  atT := X.atT
  vol := X.vol
  levelZeroCompatibility := X.levelZeroCompatibility
  g := X.g
  ad := ⟨X.ad.up0, fun u i h1 hm v c y h => ⟨rfl, X.ad.upI u i h1 hm v c y h⟩, X.ad.dn0,
    fun u i h1 hm v c g hg => ⟨rfl, X.ad.dnI u i h1 hm v c g hg⟩, X.ad.dil0,
    fun u i h1 hm v a c => ⟨rfl, X.ad.dilI u i h1 hm v a c⟩⟩
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := fun u i h1 hm v β => (X.fvI u i h1 hm v).sub (fun _ => PUnit.unit = β)
  relDet := X.relDet
  std := X.std
  vpos := X.vpos
  baseL := fun u pb h => ⟨(X.baseL u pb h).1, fun i h1 hm _ => (X.baseL u pb h).2 i h1 hm⟩

theorem FullTied.one_chart_model_base_level_eq {D : D7} (X : FullTied D) : X.toS.base.lev0 = X.base.lev0 := rfl

theorem ExtraTied.toS {D : D7} {X : FullTied D} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl K Y cX} (h : ExtraTied X ex) : SymmetricExtraCompatibility X.toS ex :=
  ⟨⟨h.join.lev_eq, h.join.errX_eq, h.join.gpl⟩, h.iw, h.iw_pos⟩

def FullTiedS.to0 {D : D7} (X : FullTiedS D) : Herm0 D := ⟨X.base.lev0, X.g⟩

theorem FullTiedS.base_model_level_eq {D : D7} (X : FullTiedS D) : X.to0.lev0 = X.base.lev0 := rfl

theorem FullTiedS.base_model_g_eq {D : D7} (X : FullTiedS D) : X.to0.g = X.g := rfl

theorem FullTied.one_chart_model_base_eq {D : D7} (X : FullTied D) : X.toS.to0 = X.to0 := rfl

end Formalism.L2.Herm

end
