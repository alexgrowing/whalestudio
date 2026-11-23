import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel

namespace Formalism.L2.SG.FamDefs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def ngenLoc {P : FPair H r} (R : Reps P) (d0 : Datum P) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)) : ENNReal :=
  ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) *
    ∑' t : R.RT d.1, (if ¬ BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (mu P t.1) else 0)

def LocalLowerBoundAtCoset (C0 : ℕ) (P : FPair H r) (R : Reps P) (d0 : Datum P) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)) :
    Prop :=
  0 < ngenLoc R d0 c1 ∧ ngenLoc R d0 c1 ≠ ⊤ ∧
  (P.PrimeTo → nn R d0 = ngenLoc R d0 c1) ∧
  nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * ngenLoc R d0 c1

def IntUni (M : Model F E) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O

def clsLoc (M : Model F E) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IntUni M A ∧ IntUni M A' ∧
    (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) ∧
    Y = (A.transpose.map M.L.cj) * Y0 * A'}

end Loc

def LocalLowerBoundAllCosets (k r C0 : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) →
      ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), (∃ t0 : Loc.Term V M r, LocNG.IsTermOver P d0 t0) →
      ∀ (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t →
      ∀ Y0, H.Zhat t.f t.f' ∈ clsLoc M Y0 → LocalLowerBoundAtCoset C0 P R d0 (clsLoc M Y0)

section Glob

open Formalism.MainNotions.S.LocNG

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def locF (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Fin (D.R.rS + 1) → Vp D p :=
  fun a => frFac (zOf Y).δ p a • baseChange₂ D p (frame F a)

abbrev locF' (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : Fin (D.R.rS + 1) → Vp D p := locF Y p F

def locT (t : TauC Y u u') (p : PlF D) : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS where
  abelian₂ := lattice₂ D (zOf Y).M p t.toTerm.lam
  f a := frFac (zOf Y).δ p a • baseChange₂ D p (frame (lf D (X.Fu u)) a)
  f' b := frFac (zOf Y).δ p b • baseChange₂ D p (frameAct (frame (Quot.out t.toTerm.cls).1)
    (admXi D t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1)⁻¹ b)
  T := ((Tu D u : ℕ) : (D.s.atP p).Fp)
  T' := ((Tu D u' : ℕ) : (D.s.atP p).Fp)

variable {Y u u'}

def moveT {p : PlF D} {Mp : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
    (t : Loc.Term (Vp D p) Mp D.R.rS) : Loc.Term (Vp D p) Mp D.R.rS where
  abelian₂ := img g t.abelian₂
  f b := g (t.f b)
  f' b := g (t.f' b)
  T := t.T
  T' := t.T'

def OverOrb {Cl Nu : Type} (Fm : LocFam (zOf Y) Cl Nu) (t : TauC Y u u') (p : PlF D) (d : Datum (Fm.FP p)) : Prop :=
  ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, IsUnitary (locH (zOf Y) p) g ∧
    ∃ d' : Datum (Fm.FP p), Datum.Rel d d' ∧ IsTermOver (Fm.FP p) d' (moveT g (locT Y u u' t p))

def OrbitFamilyIdentityAt {Cl Nu : Type} (Fm : LocFam (zOf Y) Cl Nu) (V0 : ℝ) : Prop :=
  0 < V0 ∧ ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × Nu, Fm.dat x.1 x.2 = some d) →
    ∑' x : {x : Cl × Nu // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) =
      ENNReal.ofReal (V0 * ∏ p, Fm.toL.wt p (d p))

def FamTie {Cl Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (nml : TauC Y u u' → Nu)
    (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl Nu) : Prop :=
  ∃ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (F'0 F'1 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    toPts w = γ ∧

    (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧

    Fm.V0 = (if h : ∃ v, OrbitFamilyIdentityAt Fm v then h.choose else 0) ∧

    (∃ n ∈ Formalism.L2.SG.NGData.NRat (lf D (X.Fu u)), ∀ a, frame F00 a = n (frame (lf D (X.Fu u)) a)) ∧
    ZhatOM (ZhatL F00 F'0) = ptMat w ∧
    (∀ p, (Fm.FP p).A.f = locF Y p F00 ∧ (Fm.FP p).B.f = locF' Y p F'0 ∧
      (Fm.FP p).A.T = ((Tu D u : ℕ) : (D.s.atP p).Fp) ∧ (Fm.FP p).B.T = ((Tu D u' : ℕ) : (D.s.atP p).Fp)) ∧

    (∀ p : {p // p ∈ Fm.P}, p ∈ Fm.Om ↔ ¬ (Fm.FP p.1).PrimeTo) ∧ (∀ p, p ∉ Fm.P → (Fm.FP p).PrimeTo) ∧

    (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = γ → OverOrb Fm t p (Fm.d0 p)) ∧

    (∃ t₀ ∈ TS, ptPN t₀ = γ ∧ ∀ p, p ∉ Fm.P → IsTermOver (Fm.FP p) (Fm.d0 p) (locT Y u u' t₀ p)) ∧
    (∀ p ∈ Fm.P, ∃ t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS, IsTermOver (Fm.FP p) (Fm.d0 p) t) ∧

    (∃ Λ₀ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P →
      IsTermOver (Fm.FP p) (Fm.d0 p) ⟨lattice₂ D (zOf Y).M p Λ₀, locF Y p F00, locF' Y p F'0,
        ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩) ∧

    (∀ c ν, match Fm.dat c ν with
      | none => ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nml t = ν
      | some d => (∃ t ∈ TS, cls t = c ∧ ptPN t = γ ∧ nml t = ν) ∧
          ∀ t ∈ TS, cls t = c → ptPN t = γ → nml t = ν →
            (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (Formalism.L2.SG.TermOp.wt t) ^ 2) ∧

    (∃ L U : Formalism.L2.SG.PairVal.MatR D, Formalism.MainNotions.S.IsLoUni L ∧ Formalism.MainNotions.S.IsUpUni U ∧
      ZhatOM (ZhatL (lf D (X.Fu u)) F'1) = L * ptMat w * U) ∧
    ∀ p ∈ Fm.P, Fm.ngenL p =
        (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p)
          ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1)))).toReal ∧
      ∃ (d : Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), IsTermOver (Fm.FP p) d t ∧
        (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p)
          ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1))

theorem orbitFamilyIdentity_at_volume {Cl Nu : Type} {TS : Set (TauC Y u u')} {cls : TauC Y u u' → Cl} {nml : TauC Y u u' → Nu}
    {γ : PN.Pts D.host.E D.R.rS} {Fm : LocFam (zOf Y) Cl Nu} (hT : FamTie TS cls nml γ Fm)
    (h : ∃ v, OrbitFamilyIdentityAt Fm v) : OrbitFamilyIdentityAt Fm Fm.V0 := by

  obtain ⟨_, _, _, _, _, _, hV, _⟩ := hT
  rw [hV, dif_pos h]
  exact h.choose_spec

end Glob

section Leaves

open Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem hp_nonneg {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ} (P : FPair H r) :
    0 ≤ P.Hp := by

  unfold FPair.Hp
  apply Real.rpow_nonneg
  refine mul_nonneg (mul_nonneg ?_ ?_) (Finset.prod_nonneg fun l _ => ?_)
  all_goals first
    | positivity
    | exact M.modK_nonneg _
    | (unfold Loc.Model.modK; positivity)

def HTie : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ {Cl Nu : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (nml : TauC Y u u' → Nu)
        (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) Cl Nu),
        FamTie TS cls nml γ Fm →
          Formalism.L2.SG.RowsConc.HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ = Fm.toL.Htot

def OrbitFamilyIdentityNonGeneric : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (γ : PN.Pts D.host.E D.R.rS), PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ →
      ∀ (S : Finset (Set (TauC Y u u') × NuC D)) (Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D)),
        FamTie (Y.tO u u').ngSet (clsOf Y u u') (nmlOf Y u u') γ Fm → ∃ V0, OrbitFamilyIdentityAt Fm V0

def WeightsNG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (γ : PN.Pts D.host.E D.R.rS), PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ →
      ∀ (S : Finset (Set (TauC Y u u') × NuC D)) (Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D)),
        FamTie (Y.tO u u').ngSet (clsOf Y u u') (nmlOf Y u u') γ Fm →
        (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) →
        (∀ p ∈ Fm.P, ∃ (d : Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), IsTermOver (Fm.FP p) d t) →
        OrbitFamilyIdentityAt Fm Fm.V0 → 0 < Fm.toL.ngenTot ∧ Fm.toL.ngenTot ≤
          PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * 2 *
            (NOf2 Y u u' νL νB ng).Hh γ ^ PN.eN D.R.rS * (NOf2 Y u u' νL νB ng).n γ

def ProductStructureNonGeneric : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ CSt : ℝ, 0 ≤ CSt ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν →
      ∃ s : X.B.I.Ginf → NNReal,
        (∀ γ, Formalism.L2.SG.RealObj.RegX X u u' γ → s γ = 1) ∧ (∀ γ, 0 < s γ) ∧
        (∀ γ, (s γ : ℝ) ^ 2 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f)) ∧
        ∀ γ, PN.IsPt (Y.tO u u') (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ →
        ∀ (S : Finset (Set (TauC Y u u') × NuC D)) (Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D)),
          FamTie (Y.tO u u').ngSet (clsOf Y u u') (nmlOf Y u u') γ Fm →
          ∀ x ∈ S, (NOf2 Y u u' (sc s ν) ν (fun _ => 0)).a2 x.1 γ x.2 = a2W Fm.toL Fm.toL.ampNG x.1 x.2

def ExistNG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (γ : PN.Pts D.host.E D.R.rS), PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ →
      ∀ S : Finset (Set (TauC Y u u') × NuC D), ∃ Fm : LocFam (zOf Y) (Set (TauC Y u u')) (NuC D),
        FamTie (Y.tO u u').ngSet (clsOf Y u u') (nmlOf Y u u') γ Fm ∧
        (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧
        (∀ p ∈ Fm.P, ∃ (d : Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), IsTermOver (Fm.FP p) d t) ∧
        (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c)

end Leaves

section Assembly

open Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

theorem four_rank_add_seven_le_k {Cg cb Cw cT CT C0 C' Cl : ℝ} {large₂ : SizeData₂ D} (hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u') :
    4 * D.R.rS + 7 ≤ D.R.k := by
  obtain ⟨⟨hH0, _, _⟩, _, _⟩ := hc
  unfold Formalism.MainNotions.S.StandingHypotheses at hH0
  dsimp only at hH0
  obtain ⟨-, -, h3, h4', -⟩ := hH0
  have hm2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
  have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
  omega

theorem rank_Vp (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.r_eq
  have h2 : 2 * D.R.rS + 2 = D.R.m := by
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rS]; omega
  omega

theorem famOKS_of {Cl Nu : Type} {TS : Set (TauC Y u u')} {cls : TauC Y u u' → Cl} {nml : TauC Y u u' → Nu}
    (N : PN.NGData (TauC Y u u') D.host.E D.R.rS Cl Nu) (γ : PN.Pts D.host.E D.R.rS) (S : Finset (Cl × Nu))
    (AAre : ℝ) (amp : ∀ L : PN.LocalNG Cl Nu, (∀ p, L.D p) → ℂ) (Fm : LocFam (zOf Y) Cl Nu)
    (hFT : FamTie TS cls nml γ Fm)
    (hRel : ∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p)))
    (hTerm : ∀ p ∈ Fm.P, ∃ (d : Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), IsTermOver (Fm.FP p) d t)
    (hDs : ∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) (hrw : ∀ c, 0 ≤ Fm.rw c)
    (hG6 : LocalLowerBoundAllCosets D.R.k D.R.rS 9) (hG5 : OrbitFamilyIdentityAt Fm Fm.V0) (hH : N.Hh γ = Fm.toL.Htot)
    (hWpos : 0 < Fm.toL.ngenTot) (hWle : Fm.toL.ngenTot ≤ AAre * 2 * N.Hh γ ^ PN.eN D.R.rS * N.n γ)
    (htie : ∀ x ∈ S, N.a2 x.1 γ x.2 = a2W Fm.toL (amp Fm.toL) x.1 x.2) :
    FamOKS N γ S 9 AAre amp Fm := by
  obtain ⟨w, F00, F'0, F'1, hw, -, -, hn0, hZ, hbase, hOm, hgood, hstd, -, hd0P, -, hdat, hAt, hngen⟩ := hFT
  obtain ⟨hV0pos, hV0⟩ := hG5
  have hG6p : ∀ p ∈ Fm.P, LocalLowerBoundAtCoset 9 (Fm.FP p) (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p)
      ((locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1))) := by
    intro p hp
    obtain ⟨-, d, t, ht, hm⟩ := hngen p hp
    exact hG6 _ _ ((zOf Y).M p) ((zOf Y).agree p).1 (Vp D p) (locH (zOf Y) p) (rank_Vp p) (Fm.FP p) (hRel p hp)
      (Fm.R p) (Fm.d0 p) (hd0P p hp) d t ht _ hm
  have hwt : ∀ p : {p // p ∈ Fm.P}, ∀ d : {d // d ∈ Fm.Ds p.1}, 0 ≤ Fm.toL.wt p d := by
    intro p d
    show 0 ≤ Datum.wt (Fm.d0 p.1) d.1
    unfold Datum.wt volRel
    positivity
  refine ⟨hRel, hTerm, hOm, hDs, fun p hp => ?_, hV0pos.le, hrw, ⟨fun p hp => ?_, fun p hp => ?_⟩,
    fun d S' hS' => ?_, htie, hH, hWpos, hWle⟩
  · obtain ⟨h0, hfin, -, hle⟩ := hG6p p hp
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
  · obtain ⟨-, -, heq, -⟩ := hG6p p.1 p.2
    have hpr : (Fm.FP p.1).PrimeTo := by
      by_contra h; exact hp ((hOm p).2 h)
    show (LocNG.nn (Fm.R p.1) (Fm.d0 p.1)).toReal = Fm.ngenL p.1
    rw [(hngen p.1 p.2).1, heq hpr]
  · obtain ⟨-, hfin, -, hle⟩ := hG6p p.1 p.2
    show (LocNG.nn (Fm.R p.1) (Fm.d0 p.1)).toReal ≤ 8 * (Fm.FP p.1).Hp ^ (9 * (D.R.rS + 1) ^ 2 + 2 * (2 * D.R.rS + 2)) *
      Fm.ngenL p.1
    rw [(hngen p.1 p.2).1]
    have h8 : 0 ≤ 8 * (Fm.FP p.1).Hp ^ (9 * (D.R.rS + 1) ^ 2 + 2 * (2 * D.R.rS + 2)) :=
      mul_nonneg (by norm_num) (pow_nonneg (hp_nonneg _) _)
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h8] at this
  · show ∑ x ∈ S', Fm.rw x.1 ≤ Fm.V0 * ∏ p, Fm.toL.wt p (d p)
    have hS'' : ∀ x ∈ S', Fm.dat x.1 x.2 = some d := hS'
    by_cases hne : ∃ x : Cl × Nu, Fm.dat x.1 x.2 = some d
    · have hs := hV0 d hne
      have e : ∑ x ∈ S', Fm.rw x.1 = ∑ x ∈ S'.subtype (fun x : Cl × Nu => Fm.dat x.1 x.2 = some d), Fm.rw x.1.1 := by
        rw [Finset.sum_subtype_of_mem (fun x : Cl × Nu => Fm.rw x.1) hS'']
      rw [e]
      have h1 := ENNReal.sum_le_tsum (f := fun x : {x : Cl × Nu // Fm.dat x.1 x.2 = some d} => ENNReal.ofReal (Fm.rw x.1.1))
        (S'.subtype (fun x : Cl × Nu => Fm.dat x.1 x.2 = some d))
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (le_of_le_of_eq h1 hs)
      rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at h2
      have h3 : 0 ≤ Fm.V0 * ∏ p, Fm.toL.wt p (d p) := mul_nonneg hV0pos.le (Finset.prod_nonneg fun p _ => hwt p (d p))
      rw [ENNReal.toReal_ofReal h3] at h2
      simp only [ENNReal.toReal_ofReal (hrw _)] at h2
      exact h2
    · have hS0 : S' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact hne ⟨x, hS'' x hx⟩
      rw [hS0, Finset.sum_empty]
      exact mul_nonneg hV0pos.le (Finset.prod_nonneg fun p _ => hwt p (d p))

theorem stepFamC_of (hG6 : ∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → LocalLowerBoundAllCosets D.R.k D.R.rS 9) (hH : HTie) (hG5 : OrbitFamilyIdentityNonGeneric)
    (hW : WeightsNG) (hG4 : ProductStructureNonGeneric) (hE : ExistNG) : StepFamC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH2⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW2⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE2⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max a4 (max aH (max a5 (max aW aE))), max b4 (max bH (max b5 (max bW bE))),
    fun C' Cl e1 e2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  have e1a : a4 ≤ C' := le_trans (le_max_left _ _) e1
  have e1b : aH ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) e1
  have e1c : a5 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) e1
  have e1d : aW ≤ C' := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) e1
  have e1e : aE ≤ C' := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) e1
  have e2a : b4 ≤ Cl := le_trans (le_max_left _ _) e2
  have e2b : bH ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) e2
  have e2c : b5 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) e2
  have e2d : bW ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) e2
  have e2e : bE ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) e2
  obtain ⟨s, hs1, hs0, hsb, htie⟩ :=
    h4 C' Cl e1a e2a D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  refine ⟨s, hs1, hs0, hsb, fun γ hγ S => ?_⟩
  obtain ⟨Fm, hFT, hRel, hTerm, hDs, hrw⟩ := hE2 C' Cl e1e e2e D large₂ X Y u u' hc (sc s ν) ν (fun _ => 0) γ hγ S
  have hG5Fm : OrbitFamilyIdentityAt Fm Fm.V0 := orbitFamilyIdentity_at_volume hFT (h5 C' Cl e1c e2c D large₂ X Y u u' hc (sc s ν) ν (fun _ => 0) γ hγ S Fm hFT)
  obtain ⟨hWpos, hWle⟩ := hW2 C' Cl e1d e2d D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk
    (sc s ν) ν (fun _ => 0) γ hγ S Fm hFT hRel hTerm hG5Fm
  have hOKS := famOKS_of (NOf2 Y u u' (sc s ν) ν (fun _ => 0)) γ S _ (fun L => L.ampNG) Fm hFT
    hRel hTerm hDs hrw (hG6 D (four_rank_add_seven_le_k hc)) hG5Fm
    (hH2 C' Cl e1b e2b D large₂ X Y u u' hc _ _ _ γ Fm hFT) hWpos hWle (htie γ hγ S Fm hFT)
  exact ⟨Fm, (famOK_iff _ _ _ _ _ _).2 hOKS⟩

end Assembly

end Formalism.L2.SG.FamDefs
