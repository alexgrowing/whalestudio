import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.PrinLevClass

noncomputable section

namespace Formalism.MainNotions.CanonicalTranslateJets

open Formalism.BasicNotions NumberField
open Classical

def overG (D : D7) (w : D.what₂.places.Pl) (i : Fin 2) : Prop :=
  D.what₂.places.resChar w = D.host.g i

instance instFactRes (D : D7) (w : D.what₂.places.Pl) : Fact (D.what₂.places.resChar w).Prime :=
  ⟨D.what₂.places.resChar_prime w⟩

abbrev Cw (D : D7) (w : D.what₂.places.Pl) : Type := ℂ_[D.what₂.places.resChar w]

def tauLL (D : D7) (τ : D.R.GG) (x : D.host.E) : D.what₂.LL :=
  D.embE (D.host.sigmaOf τ x)

def InR (D : D7) (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

structure Loc (D : D7) (X : DivX D) where

  iota : ∀ w, D.what₂.LL →+* Cw D w

  iota_int : ∀ w (x : D.what₂.LL), ‖iota w x‖ ≤ 1 ↔ 0 ≤ D.what₂.places.val w x

  piG : Fin 2 → 𝓞 D.host.E
  pibG : Fin 2 → 𝓞 D.host.E
  pib_conj : ∀ i, ((pibG i : 𝓞 D.host.E) : D.host.E) = D.host.conj (piG i : D.host.E)
  piG_K : ∀ i, ((piG i : 𝓞 D.host.E) : D.host.E) ∈ D.host.K
  piG_norm : ∀ i, piG i * pibG i = (D.host.g i : 𝓞 D.host.E)

  piG_cop : ∀ i, IsCoprime (piG i) (pibG i)

  FA : ℕ → Type
  [instFA : ∀ j, AddCommGroup (FA j)]
  [instFAm : ∀ j, Module D.what₂.LL (FA j)]

  inM : ∀ j, (X.MjH j).V →ₗ[D.what₂.LL] FA j
  inM_inj : ∀ j, Function.Injective (inM j)

  Coef : ℕ → Type
  [instCoef : ∀ j, AddCommGroup (Coef j)]
  [instCoefm : ∀ j, Module D.what₂.LL (Coef j)]

  harm : ∀ j, Submodule D.what₂.LL (Coef j)

  hom : ∀ j, (D.R.GG → ℕ) → Submodule D.what₂.LL (Coef j)
  hom_disj : ∀ j Dg Dg', Dg ≠ Dg' → Disjoint (hom j Dg) (hom j Dg')

  intP : ∀ j, D.what₂.places.Pl → Set (Coef j)

  wt : ∀ j, Submodule D.what₂.LL (Coef j)
  wt_harm : ∀ j, wt j ≤ harm j

  Cls : D.what₂.Tup → ℕ → Type
  [clsFin : ∀ μ j, Fintype (Cls μ j)]

  gam : ∀ μ j, Cls μ j → ℕ
  gam_pos : ∀ μ j h, 0 < gam μ j h

  fval : ∀ μ j, D.what₂.MtL μ j →ₗ[D.what₂.LL] (Cls μ j → wt j)
  fval_inj : ∀ μ j, Function.Injective (fval μ j)

  Lt : ℕ → Type
  latOf : ∀ μ j, Cls μ j → Lt j

  thS : ∀ μ j, Cls μ j → (wt j →ₗ[D.what₂.LL] FA j)

  theta_rec : ∀ μ j, InR D j → ∀ f : D.what₂.MtL μ j, D.what₂.jMt μ j f ∈ D.what₂.Zj μ j →
    ∃ x : (X.MjH j).V, inM j x = ∑ h, ((gam μ j h : D.what₂.LL))⁻¹ • thS μ j h (fval μ j f h) ∧
      X.jM j x = D.what₂.thetaP μ j (D.what₂.jMt μ j f)

  ModG : ∀ j, Fin 2 → Lt j → Type
  [modGrp : ∀ j i La, AddCommGroup (ModG j i La)]
  [modFin : ∀ j i La, Fintype (ModG j i La)]

  card_ModG : ∀ j i La, Fintype.card (ModG j i La) = D.host.g i ^ (D.R.f * D.R.r * D.R.nV)

  datG : ∀ μ j (h : Cls μ j) i, ModG j i (latOf μ j h) → D.what₂.LL

  Pt : ℕ → D.what₂.places.Pl → Type

  ev : ∀ j w, Pt j w → (FA j →ₛₗ[iota w] Cw D w)

  Tor : ∀ j w, Pt j w → Lt j → Type
  [torFin : ∀ j w y La, Fintype (Tor j w y La)]
  [torGrp : ∀ j w y La, AddCommGroup (Tor j w y La)]
  [torMod : ∀ j w y La, Module (𝓞 D.host.E) (Tor j w y La)]
  tor_pi : ∀ j w y La i, overG D w i → ∀ t : Tor j w y La, piG i • t = 0

  chi : ∀ j w y La i, Tor j w y La → ModG j i La → Cw D w
  chi_add : ∀ j w y La i t x x', chi j w y La i t (x + x') = chi j w y La i t x * chi j w y La i t x'
  chi_pow : ∀ j w y La i t x, chi j w y La i t x ^ (D.what₂.places.resChar w) = 1
  chi_addT : ∀ j w y La i t t' x, chi j w y La i (t + t') x = chi j w y La i t x * chi j w y La i t' x

  chi_perf : ∀ j w y La i, overG D w i → ∀ t, (∀ x, chi j w y La i t x = 1) → t = 0
  card_Tor : ∀ j w y La i, overG D w i → Fintype.card (Tor j w y La) = Fintype.card (ModG j i La)

  Sec : ∀ j w, Pt j w → Lt j → Type
  [secGrp : ∀ j w y La, AddCommGroup (Sec j w y La)]
  [secMod : ∀ j w y La, Module (Cw D w) (Sec j w y La)]

  Th : ∀ j w y La, Sec j w y La

  Ut : ∀ j w y La, Tor j w y La → (Sec j w y La →ₗ[Cw D w] Sec j w y La)
  Ut_zero : ∀ j w y La, Ut j w y La 0 = LinearMap.id

  jetSec : ∀ j w y La, Sec j w y La →ₗ[Cw D w] (Coef j →ₛₗ[iota w] Cw D w)

  intS : ∀ j w y La, Set (Sec j w y La)

  al : ∀ j w y La, Tor j w y La → Cw D w

  XiC : ∀ μ j w (y : Pt j w) (h : Cls μ j) i,
    (ModG j i (latOf μ j h) → Cw D w) →ₗ[Cw D w] Sec j w y (latOf μ j h)

  SecG : ∀ j w, Pt j w → Lt j → Type
  [secGGrp : ∀ j w y La, AddCommGroup (SecG j w y La)]
  [secGMod : ∀ j w y La, Module (Cw D w) (SecG j w y La)]

  pull : ∀ j w y La, Sec j w y La →ₗ[Cw D w] SecG j w y La

  jetG : ∀ j w y La, SecG j w y La →ₗ[Cw D w] (Coef j →ₛₗ[iota w] Cw D w)

  intSG : ∀ j w y La, Set (SecG j w y La)

  TG : ∀ j w y La, Tor j w y La → Type
  TG_ne : ∀ j w y La b, Nonempty (TG j w y La b)

  act : ∀ j w y La b, TG j w y La b → (SecG j w y La →ₗ[Cw D w] SecG j w y La)

attribute [instance] Loc.instFA Loc.instFAm Loc.instCoef Loc.instCoefm
  Loc.clsFin Loc.modGrp Loc.modFin Loc.torFin Loc.torGrp Loc.torMod Loc.secGrp Loc.secMod
  Loc.secGGrp Loc.secGMod

variable {D : D7} {X : DivX D}

def Olam (G : Loc D X) (w : D.what₂.places.Pl) : Subring (Cw D w) :=
  (Subring.closure (G.iota w '' {x | 0 ≤ D.what₂.places.val w x})).topologicalClosure

def OZ (G : Loc D X) (w : D.what₂.places.Pl) : Subring (Cw D w) :=
  Subring.closure ((Olam G w : Set (Cw D w)) ∪ {z | z ^ D.what₂.places.resChar w = 1})

def thetaA (G : Loc D X) (μ : D.what₂.Tup) (j : ℕ) (f : D.what₂.MtL μ j) : G.FA j :=
  ∑ h, ((G.gam μ j h : D.what₂.LL))⁻¹ • G.thS μ j h (G.fval μ j f h)

def ThP (G : Loc D X) (μ : D.what₂.Tup) (j : ℕ) (w : D.what₂.places.Pl) (y : G.Pt j w) (h : G.Cls μ j)
    (i : Fin 2) : G.Sec j w y (G.latOf μ j h) :=
  G.XiC μ j w y h i (fun _ => 1)

def nn (G : Loc D X) (i : Fin 2) (Dg : D.R.GG → ℕ) : D.what₂.LL :=
  ∏ τ, (tauLL D τ (G.pibG i : D.host.E)) ^ (Dg τ)

def fourierG (G : Loc D X) {j : ℕ} {w : D.what₂.places.Pl} {y : G.Pt j w} {La : G.Lt j} {i : Fin 2}
    (Φ : G.ModG j i La → Cw D w) (t : G.Tor j w y La) : Cw D w :=
  ((Fintype.card (G.ModG j i La) : Cw D w))⁻¹ * ∑ x, Φ x * G.chi j w y La i t (-x)

def jetH (G : Loc D X) (j : ℕ) (w : D.what₂.places.Pl) (y : G.Pt j w) (La : G.Lt j)
    (b : G.Tor j w y La) (γ : G.TG j w y La b) (s : G.Sec j w y La) (P : G.Coef j) : Cw D w :=
  G.jetG j w y La (G.act j w y La b γ (G.pull j w y La s)) P

def HarmHom (G : Loc D X) (j : ℕ) (Dg : D.R.GG → ℕ) (P : G.Coef j) : Prop :=
  P ∈ G.harm j ⊓ G.hom j Dg

def adm1 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ μ j, InR D j → ∀ (h : G.Cls μ j) i x,
    G.datG μ j h i x = 0 ∨ ∃ n : ℕ, 0 < n ∧ G.datG μ j h i x ^ n = 1

def adm2 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ μ j, InR D j → ∀ (y : G.Pt j w) (h : G.Cls μ j),
    (∀ Φ, G.XiC μ j w y h i Φ = ∑ t, fourierG G Φ t •
        (G.al j w y (G.latOf μ j h) t • G.Ut j w y (G.latOf μ j h) t (ThP G μ j w y h i))) ∧
    (∀ t, G.al j w y (G.latOf μ j h) t ^ (2 * D.host.g i) = 1) ∧ G.al j w y (G.latOf μ j h) 0 = 1

def adm3 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La,
    G.Th j w y La ∈ G.intS j w y La ∧
    (∀ s ∈ G.intS j w y La, ∀ b (γ : G.TG j w y La b),
      G.act j w y La b γ (G.pull j w y La s) ∈ G.intSG j w y La) ∧
    (∀ h ∈ G.intSG j w y La, ∀ Dg P, P ∈ G.intP j w → HarmHom G j Dg P →
      (∑ τ, Dg τ) + 1 < D.host.g i → ‖G.jetG j w y La h P‖ ≤ 1)

def ArchimedeanSignatureMatching (D : D7) : Prop :=
  ∀ μ j, InR D j → ∀ σ,
    (∀ x ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • x) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

def adm5 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ μ j, InR D j → ∀ (h : G.Cls μ j) i, (D.host.g i).Coprime (G.gam μ j h)

def adm6 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ μ j, InR D j → ∀ (y : G.Pt j w) (h : G.Cls μ j) (P : G.wt j),
    G.ev j w y (G.thS μ j h P) =
      G.jetSec j w y (G.latOf μ j h) (G.XiC μ j w y h i (fun x => G.iota w (G.datG μ j h i x))) (P : G.Coef j)

def adm7 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La (s : G.Sec j w y La) Dg P, HarmHom G j Dg P →
    G.jetG j w y La (G.pull j w y La s) P = G.iota w (nn G i Dg) * G.jetSec j w y La s P

def adm8 (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La b (γ : G.TG j w y La b),
    ∃ (ζ : Cw D w) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ s : G.Sec j w y La,
      G.act j w y La b γ (G.pull j w y La s) = ζ • G.pull j w y La (G.Ut j w y La (G.pibG i • b) s)

def adm9 (D : D7) : Prop := ∀ i, 2 * D.R.f * D.R.nV + 1 < D.host.g i

def admitted (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  adm1 D X G ∧ adm2 D X G ∧ adm3 D X G ∧ ArchimedeanSignatureMatching D ∧ adm5 D X G ∧ adm6 D X G ∧ adm7 D X G ∧ adm8 D X G ∧
    adm9 D

def ConjugationNormInvariance (D : D7) (X : DivX D) (G : Loc D X) (C : ℝ) : Prop :=
  ∃ c0 : ℕ, (c0 : ℝ) ≤ C * D.R.f * D.R.r * D.R.nV ∧
    ∀ w i, overG D w i → ∀ j, InR D j → ∀ μ (y : G.Pt j w),
      ∃ c : ∀ h : G.Cls μ j, G.Tor j w y (G.latOf μ j h) → Cw D w,
        (∀ h t, (D.host.g i : Cw D w) ^ c0 * c h t ∈ OZ G w) ∧
        ∀ f : D.what₂.MtL μ j, G.ev j w y (thetaA G μ j f) = ∑ h, ∑ t, c h t *
          G.jetSec j w y (G.latOf μ j h) (G.Ut j w y (G.latOf μ j h) t (ThP G μ j w y h i))
            (G.fval μ j f h : G.Coef j)

def LiteralThetaLineBound (D : D7) (X : DivX D) (G : Loc D X) (C : ℝ) : Prop :=
  ∃ c0 : ℕ, (c0 : ℝ) ≤ C * D.R.f * D.R.r * D.R.nV ∧
    ∀ w i, overG D w i → ∀ j, InR D j → ∀ μ (y : G.Pt j w),
      ∃ c : ∀ h : G.Cls μ j, G.Tor j w y (G.latOf μ j h) → Cw D w,
        (∀ h t, (D.host.g i : Cw D w) ^ c0 * c h t ∈ OZ G w) ∧
        ∀ f : D.what₂.MtL μ j, G.ev j w y (thetaA G μ j f) = ∑ h, ∑ t, c h t *
          G.jetSec j w y (G.latOf μ j h) (G.Ut j w y (G.latOf μ j h) t (G.Th j w y (G.latOf μ j h)))
            (G.fval μ j f h : G.Coef j)

def CanonicalTranslateJetIdentity (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La b (γ : G.TG j w y La b),
    ∃ (ζ : Cw D w) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ (s : G.Sec j w y La) Dg P, HarmHom G j Dg P →
      jetH G j w y La b γ s P =
        ζ * (G.iota w (nn G i Dg) * G.jetSec j w y La (G.Ut j w y La (G.pibG i • b) s) P)

def IsotypicRank (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La (b : G.Tor j w y La), ∀ s ∈ G.intS j w y La,
    ∀ Dg P, P ∈ G.intP j w → HarmHom G j Dg P → (∑ τ, Dg τ) + 1 < D.host.g i →
      ‖G.iota w (nn G i Dg) * G.jetSec j w y La (G.Ut j w y La (G.pibG i • b) s) P‖ ≤ 1

def JetConsequence (D : D7) (X : DivX D) (G : Loc D X) : Prop := CanonicalTranslateJetIdentity D X G ∧ IsotypicRank D X G

def altInt (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  ∀ w i, overG D w i → ∀ j, InR D j → ∀ (y : G.Pt j w) La (t : G.Tor j w y La), ∀ s ∈ G.intS j w y La,
    ∀ Dg P, P ∈ G.intP j w → HarmHom G j Dg P → (∑ τ, Dg τ) + 1 < D.host.g i →
      ‖G.jetSec j w y La (G.Ut j w y La t s) P‖ ≤ 1

def Stmt (D : D7) (X : DivX D) (G : Loc D X) (CA : ℝ) : Prop :=
  admitted D X G → ConjugationNormInvariance D X G CA ∧ JetConsequence D X G

abbrev LocF {eps : ℝ} (Fm : FamP eps) : Type 1 :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i)

def AdmF {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (GF x hx i)

def familyJetConstantBound (C : ℝ) {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConjugationNormInvariance (Fm.D x i) (Fm.X x i) (GF x hx i) C

def familyJetConsequence {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), JetConsequence (Fm.D x i) (Fm.X x i) (GF x hx i)

def KudlaFamilyStatement (CA : ℝ) {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Stmt (Fm.D x i) (Fm.X x i) (GF x hx i) CA

def ShareAbsoluteConstant (Fm : DFamP) (GF : ∀ ε h0 h1, LocF (Fm ε h0 h1)) : Prop :=
  ∃ CA : ℝ, ∀ ε h0 h1, KudlaFamilyStatement CA (Fm ε h0 h1) (GF ε h0 h1)

abbrev TcF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (i : Fm.Ix x), ℕ → ∀ k : Fin 2, (ZMod ((Fm.D x i).host.g k))ˣ →* ℂˣ

def familyUnitInput {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) (tc : TcF Fm) : Prop :=
  DIV.Align.TameAtG Fm tc → ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm1 (Fm.D x i) (Fm.X x i) (GF x hx i)

def AdmR (D : D7) (X : DivX D) (G : Loc D X) : Prop :=
  adm2 D X G ∧ adm3 D X G ∧ ArchimedeanSignatureMatching D ∧ adm5 D X G ∧ adm6 D X G ∧ adm7 D X G ∧ adm8 D X G ∧ adm9 D

def AdmFT {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) (tc : TcF Fm) : Prop :=
  familyUnitInput Fm GF tc ∧ ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AdmR (Fm.D x i) (Fm.X x i) (GF x hx i)

def CuspidalFamilyPacket (CA : ℝ) {eps : ℝ} (Fm : FamP eps) (GF : LocF Fm) (tc : TcF Fm) : Prop :=
  DIV.Align.TameAtG Fm tc → familyUnitInput Fm GF tc → ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    AdmR (Fm.D x i) (Fm.X x i) (GF x hx i) →
      ConjugationNormInvariance (Fm.D x i) (Fm.X x i) (GF x hx i) CA ∧ JetConsequence (Fm.D x i) (Fm.X x i) (GF x hx i)

def AbsoluteConstantPacket (Fm : DFamP) (GF : ∀ ε h0 h1, LocF (Fm ε h0 h1)) (tc : ∀ ε h0 h1, TcF (Fm ε h0 h1)) : Prop :=
  ∃ CA : ℝ, ∀ ε h0 h1, CuspidalFamilyPacket CA (Fm ε h0 h1) (GF ε h0 h1) (tc ε h0 h1)

end Formalism.MainNotions.CanonicalTranslateJets

end
