import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

def SatU {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) : Prop :=
  T = TwDat.untw B T.pl → ∀ v v', OverOne (w.D P.Z₀) v v' → v ∈ P.Wt → v' ∈ P.Wt

section Slot

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

def Org (K : Ctx) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) {D : D7} (Wt : Set B.places.Pl) (nch : NChoice D) : Prop :=
  ∃ (P : Pre2 K w) (x : St P) (l : LC hL x), (ListSt cDep x ∧ SatU P) ∧ Wt = P.Wt ∧ Kept l.c.ch nch

def NEo : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c ×
  PLift (Org hL cDep K w Wt nch)

def NEog : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEo hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SFino : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), (ListSt cDep x ∧ SatU P) →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEo hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNo : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEo hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEog hL cDep) S Γ).s K B f T w

end Slot

def ExistsUnlocalizedSaturatedState : Prop := StepW Start fun K _ _ _ w => ∃ (P : Pre2 K w) (x : St P), SatU P ∧ IsEmpty x.o.N.nd.Loc ∧ ∀ j v, x.o.η j v = 0

structure SameGal (D D' : D7) : Prop where
  gal : SameGalois D.nd D'.nd
  pl : HEq D.naut.plGw D'.naut.plGw

structure Carried (D D' : D7) : Prop where
  exp : SameExport D D'
  emb : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (x : D.LL0) (x' : D'.LL0),
    D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      HEq (D.ntw.emb0 i x) (D'.ntw.emb0 i' x') ∧ HEq (D.ntw.emb0b i x) (D'.ntw.emb0b i' x')

theorem SameGal.refl (D : D7) : SameGal D D := ⟨(SameExport.refl D).gal, HEq.rfl⟩

theorem Carried.refl (D : D7) : Carried D D := ⟨SameExport.refl D, fun i i' h x x' e => by
  obtain rfl := eq_of_heq h
  obtain rfl : x = x' := Subtype.ext (D.what₂.embLL.injective e)
  exact ⟨HEq.rfl, HEq.rfl⟩⟩

structure Seed (D : D7) (A : D.ntw.Tw → Finset (PlE D.host)) where
  s : D.what₂.places.Pl → D.ntw.Tw
  reads : ∀ v, ∃ b, ReadsAt (s v) b v
  conj : ∀ v, s (D.what₂.places.conj v) = s v
  same : ∀ v v', TwistedAt D v → TwistedAt D v' → OverOne D v v' → s v' = s v
  xd : ThData D
  all : XdAll xd
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)
  Q : D.ntw.Tw → Finset (PlE D.host)
  k : D.ntw.Tw → ℕ
  ψ : ∀ i, D.ntw.RCG i (Q i) →* (D.ntw.Ok i (k i))ˣ
  good : ∀ v, TwistedAt D v → TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (s v) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (s v)) →
      IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) (twEOf xd) N0 (s v) (twEps D (s v)) (S (s v)) (A (s v)) (Q (s v)) (k (s v)) (ψ (s v) ^ a)
  sep : ∀ v v', TwistedAt D v → TwistedAt D v' → s v ≠ s v' → Disjoint (Q (s v)) (Q (s v'))

def Seed.pack {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) (v : D.what₂.places.Pl) : TwPack D :=
  ⟨σ.s v, σ.Q (σ.s v), σ.k (σ.s v), σ.ψ (σ.s v)⟩

def Seed.ofUntw {D : D7} (A : D.ntw.Tw → Finset (PlE D.host)) (s : D.what₂.places.Pl → D.ntw.Tw) (h1 : ∀ v, ∃ b, ReadsAt (s v) b v)
    (h2 : ∀ v, s (D.what₂.places.conj v) = s v) (xd : ThData D) (h3 : XdAll xd) (h : ∀ v, ¬ TwistedAt D v) : Seed D A :=
  ⟨s, h1, h2, fun v _ hv => absurd hv (h v), xd, h3, fun _ => 0, fun _ _ _ => ∅, fun _ => ∅, fun _ => 0, fun _ => 1,
    fun v hv => absurd hv (h v), fun v _ hv => absurd hv (h v)⟩

def TwFrom (X : Stages) {A : X.toD7.ntw.Tw → Finset (PlE X.toD7.host)} (σ : Seed X.toD7 A) {B' : Base} (h : Enl X.B B')
    (T' : TwDat B') : Prop :=
  (∀ (v' : B'.places.Pl) (z : ℂ), z ^ B'.places.resChar v' ^ T'.k v' = 1 → ∃ x : B'.LL, B'.embLL x = z) ∧
  ∀ v' : B'.places.Pl,
    (TwistedAt X.toD7 (plUnder h v') →
      HEq (T'.Q v') (σ.Q (σ.s (plUnder h v'))) ∧ T'.k v' = σ.k (σ.s (plUnder h v')) ∧
      ∃ (ι : RootIso X.toD7 (σ.s (plUnder h v')) (σ.k (σ.s (plUnder h v')))) (χ : HChar X.toD7.host.E),
        FrobPick (σ.s (plUnder h v')) _ _ (σ.ψ (σ.s (plUnder h v'))) ι χ ∧ HEq (T'.psi v') χ) ∧
    (¬ TwistedAt X.toD7 (plUnder h v') → T'.psi v' = 1)

def BareK : Prop := StepW Start fun K B' f' _ w' => ∀ (P' : Pre2 K w') (X : Stages) (f : Fr X.B.toPre), B'.toPre = X.B.toPre →
  HEq f' f → GrpTrue X.N f → ∃ x' : St P', IsEmpty x'.o.N.nd.Loc ∧ SameGal X.toD7 (Dof x')

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def SAk : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (LA hL x') ∧ SameGal (Dof x) (Dof x')

def SCk : Prop := AllSt fun _ B _ T _ _ x => ∀ (l : StrictHenselianAcyclic hL x) (s : B.places.Pl → (Dof x).ntw.Tw),
  (∀ v, ∃ b, ReadsAt (D := Dof x) (s v) b v) → (∀ v, s (B.places.conj v) = s v) →
  ∃ c : StC l.mt l.b T.k T.psi, c.ch.twI = s

def MvB : Prop := StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ →
  ∀ (P : Pre2 K w) (x : St P), StrictHenselianAcyclic hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', LI hL x' → SameGal (Dof x) (Dof x') →
    ∃ x'' : St P', Nonempty (StrictHenselianAcyclic hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x''

end GlobalTheory.HeightCounting.Up

end
