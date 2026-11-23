import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Asc

variable {D : D7}

def VacG (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Γ f

def Ann (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Γ : AddSubgroup (WO S T)) : Set (WO S T) :=
  {w | (∀ u ∈ Γ, ψ (symplO S T w (2 • u)) = 1) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ Γ, IsHalf e u → ψ (symplO S T w u) = 1}

structure Tame (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ℓ (f + f') = ℓ f + ℓ f'
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  cont : ∀ f, IsThetaFunO ψ S T f → Continuous fun w => ℓ (heisO ψ S T w f)
  bdd : ∀ f, IsThetaFunO ψ S T f → ∃ C : ℝ, ∀ w, ‖ℓ (heisO ψ S T w f)‖ ≤ C
  sup : ∀ f, IsThetaFunO ψ S T f → ∀ (m : Measure (WO S T)) [SFinite m] (α : WO S T → ℂ), Integrable α m →
    IsThetaFunO ψ S T (fun x => ∫ w, α w * heisO ψ S T w f x ∂m) →
      ℓ (fun x => ∫ w, α w * heisO ψ S T w f x ∂m) = ∫ w, α w * ℓ (heisO ψ S T w f) ∂m

structure BesL (D : D7) (ρ : ℕ) where
  V : HSp D
  V₀ : HSp D
  A : HSp D
  L : HSp D
  d : HypDec V V₀ ρ
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  vA : GlobalTheory.Unf.Vol A
  vN : VolN d

structure JacL (D : D7) (ρ : ℕ) where
  W : HSp D
  W₀ : HSp D
  d : HypDec W W₀ ρ
  v0 : GlobalTheory.Unf.Vol W₀
  vN : VolN d

variable {ψ : AddChar (AF D.host.F) ℂ}

def BesL.per {ρ : ℕ} (B : BesL D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) : ℂ :=
  besPer ψ 1 B.d B.o B.ζ B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 φ f

def JacL.per {ρ : ℕ} (J : JacL D ρ) (ψ : AddChar (AF D.host.F) ℂ) {L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (omz : Om J.W₀ L')
    (φ : GA D J.W₀ → ℂ) (f : GA D J.W → ℂ) (Φ₀ : WO J.W₀ L' → ℂ) : ℂ :=
  fjSrc ψ J.d ζ' omz J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 φ f Φ₀

def JacL.perAll {ρ : ℕ} (J : JacL D ρ) (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (B : BesL D σ) (om₀ : Om B.V₀ J.W₀)
    (φ : GA D B.A → ℂ) (G' : GA D J.W → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) : ℂ :=
  fjAll ψ J.d B.o B.ζ om₀ B.vA.μ B.vA.𝓕 J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 φ G' Ξ

abbrev StBF (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesL D ρ) (J : JacL D ρ) := Step ψ B.V B.V₀ J.W J.W₀ ρ ρ

abbrev StFB (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (J : JacL D (σ + 1)) (B : BesL D σ) := Step ψ J.W J.W₀ B.V B.V₀ (σ + 1) σ

def flatS {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ) : WO V₀ W₀ → ℂ :=
  flatAt ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 s.vU.ν x y Ψ

abbrev flBF {ρ : ℕ} {B : BesL D ρ} {J : JacL D ρ} (s : StBF ψ B J) : (WO B.V J.W → ℂ) → WO B.V₀ J.W₀ → ℂ :=
  flatS B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ))

abbrev flFB {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ} (s : StFB ψ J B) : (WO J.W B.V → ℂ) → WO J.W₀ B.V₀ → ℂ :=
  flatS J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0

def handP {σ : ℕ} {J : JacL D (σ + 1)} {B : BesL D σ} (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (omz : Om J.W₀ B.L)
    (φ : GA D J.W₀ → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) : GA D B.A → ℂ :=
  fun h₁ => ∫ h₀ in J.v0.𝓕, φ h₀ *
    contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) Ξ) (omz (h₀, 1) Φ₀) 0 ∂J.v0.μ

structure Lnk (L : HSp D) (ζ : Fin L.rank → D.host.E) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) where
  τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E
  map : τ *ᵥ ζ' = -ζ
  norm : star ζ ⬝ᵥ L.gram *ᵥ ζ = D.host.xi0 * star D.host.xi0 * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ')

def Lnk.κ {L L' : HSp D} {ζ : Fin L.rank → D.host.E} {ζ' : Fin L'.rank → D.host.E} (l : Lnk L ζ L' ζ') (S : HSp D)
    (w : WO S L') : WO L S :=
  GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat l.τ : Mx D L.rank L'.rank) ⬝ w)

structure Loc {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (𝒮 : Set (WO V W → ℂ)) (Γ₀ : AddSubgroup (WO V₀ W₀)) (K : Subgroup (GA D W)) : Prop where
  theta : ∀ Φ ∈ 𝒮, IsThetaFunO ψ V W Φ
  real : ∀ Φ ∈ 𝒮, ∀ w : WO V W, w.map (finPart D) = 0 → heisO ψ V W w Φ ∈ 𝒮
  core : ∀ Φ ∈ 𝒮, ∀ w ∈ Ann ψ V₀ W₀ Γ₀, heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ ∈ 𝒮
  vac : ∀ Φ ∈ 𝒮, VacG ψ V₀ W₀ Γ₀ (flatS dV dW s x y Φ)
  fin : K ≤ GfC W
  cpt : IsCompact (K : Set (GA D W))
  opn : IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W))
  fix : ∀ Φ ∈ 𝒮, ∀ k ∈ K, s.om (1, k) Φ = Φ
  supp : ∀ Φ ∈ 𝒮, ∀ h, flatS dV dW s x y (s.om (1, h) Φ) ≠ 0 → ∃ r ∈ Rgrp W x, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k
  ne : ∃ Φ ∈ 𝒮, flatS dV dW s x y Φ ≠ 0

def Irr (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)) (ℓ : (WO S T → ℂ) → ℂ),
    Tame ψ S T ℓ → ∀ f₀, VacG ψ S T Γ f₀ → f₀ ≠ 0 → (∀ w ∈ Ann ψ S T Γ, ℓ (heisO ψ S T w f₀) = 0) → ∀ f, VacG ψ S T Γ f → ℓ f = 0

def HtCmp (D : D7) : Prop :=
  (∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h,
    quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a) ∧
  ∀ (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h,
    quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a

def VanBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) 𝒮 Γ₀ K,
    Loc B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) 𝒮 Γ₀ K → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ),
    RapidDec B.A φ → RapidDec J.W G → (∀ k ∈ K, ∀ g, G (g * k) = G g) → (∀ Φ ∈ 𝒮, B.per ψ φ (s.lift G Φ) = 0) →
      ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0

def VanFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) 𝒮 Γ₀ K,
    Loc J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 𝒮 Γ₀ K → ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle)
    (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ),
    RapidDec J.W₀ φ → RapidDec B.V G → IsThetaFunO ψ J.W₀ B.L Φ₀ → (∀ k ∈ K, ∀ g, G (g * k) = G g) →
    (∀ Φ ∈ 𝒮, J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ = 0) → ∀ Φ ∈ 𝒮, B.per ψ (handP s vL omz φ Φ₀ (flFB s Φ)) G = 0

def UpBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J) 𝒮 Γ₀ K,
    Loc B.d J.d s (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) 𝒮 Γ₀ K →
    ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Lnk B.L B.ζ L' ζ') (χA χz χ' : (AE D)ˣ →* Circle)
    (oma : Om B.A J.W₀) (omz : Om J.W₀ L'), s.χV = χA * χz → IsWeilDatumO ψ B.A J.W₀ χA s.χW oma →
    IsWeilDatumO ψ J.W₀ L' χ' χz omz → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G →
    (∀ k ∈ K, ∀ g, G (g * k) = G g) → ∀ (Ξ₁ : WO B.A J.W₀ → ℂ) (Ξ₂ : WO B.L J.W₀ → ℂ), IsThetaFunO ψ B.A J.W₀ Ξ₁ →
    IsThetaFunO ψ B.L J.W₀ Ξ₂ → VacG ψ B.V₀ J.W₀ Γ₀ (B.o.boxS J.W₀ Ξ₁ Ξ₂) →
    J.per ψ ζ' omz (liftT oma B.vA.μ B.vA.𝓕 φ Ξ₁) G (fun w => star (Ξ₂ (l.κ J.W₀ w))) ≠ 0 →
      ∃ Φ ∈ 𝒮, B.per ψ φ (s.lift G Φ) ≠ 0

def UpFB (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) 𝒮 Γ₀ K,
    Loc J.d B.d s (xLast B.d (vecB B.o B.ζ)) 0 𝒮 Γ₀ K → ∀ (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L),
    s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ), RapidDec J.W₀ φ → RapidDec B.V G → (∀ k ∈ K, ∀ g, G (g * k) = G g) →
    ∀ (Ξ₁ : WO J.W₀ B.A → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ₀ → Φ₀ ≠ 0 →
    VacG ψ J.W₀ B.V₀ Γ₀ (B.o.boxT J.W₀ Ξ₁ Φ₀) → B.per ψ (liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁) G ≠ 0 →
      ∃ Φ ∈ 𝒮, J.per ψ B.ζ omz φ (s.lift G Φ) Φ₀ ≠ 0

structure LastLat (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D 0) {X T L'' : HSp D} (o : OrthDec X T L'') (Γ : AddSubgroup (WO J.W T))
    (ΓL : AddSubgroup (WO J.W₀ (negSp L''))) (ΓX : AddSubgroup (WO J.W₀ X)) : Prop where
  ann : ∀ w ∈ Ann ψ J.W₀ X ΓX, J.d.ext0 T (o.resT J.W₀ w).1 ∈ Ann ψ J.W T Γ ∧ (o.resT J.W₀ w).2 ∈ Ann ψ J.W₀ (negSp L'') ΓL
  ex : ∃ f₁ f₂, VacG ψ J.W T Γ f₁ ∧ VacG ψ J.W₀ (negSp L'') ΓL f₂ ∧ f₁ ≠ 0 ∧ f₂ ≠ 0 ∧
    VacG ψ J.W₀ X ΓX (o.boxT J.W₀ (fun w => f₁ (J.d.ext0 T w)) (star f₂))

def UpLast (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (J : JacL D 0) (X T L'' : HSp D) (o : OrthDec X T L'') Γ ΓL ΓX, L''.rank = 1 →
    LastLat ψ J o Γ ΓL ΓX → ∀ (ζ' : Fin (negSp L'').rank → D.host.E) (χS χT χz : (AE D)ˣ →* Circle) (om : Om J.W T) (omX : Om J.W₀ X)
    (omz : Om J.W₀ (negSp L'')), IsWeilDatumO ψ J.W T χS χT om → IsWeilDatumO ψ J.W₀ X χS (χT * χz⁻¹) omX →
    IsWeilDatumO ψ J.W₀ (negSp L'') χS⁻¹ χz omz → ∀ (vT : GlobalTheory.Unf.Vol T) (φ : GA D J.W₀ → ℂ) (u : GA D T → ℂ),
    RapidDec J.W₀ φ → RapidDec T u → ∀ Ξ, VacG ψ J.W₀ X ΓX Ξ →
    (∫ h in vT.𝓕, liftT omX J.v0.μ J.v0.𝓕 φ Ξ (o.emb (h, 1)) * u h ∂vT.μ) ≠ 0 →
      ∃ Φ Φ₀, VacG ψ J.W T Γ Φ ∧ VacG ψ J.W₀ (negSp L'') ΓL Φ₀ ∧ J.per ψ ζ' omz φ (liftS om vT.μ vT.𝓕 u Φ) Φ₀ ≠ 0

def cjOm {S T : HSp D} (om : Om (negSp S) T) : Om S T :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd (Equiv.refl (WO S T))).comp (om.comp ((negGA S).toMonoidHom.prodMap (MonoidHom.id _)))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

abbrev omRow (W : G.Weil) (i : ℕ) : Om (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) := cjOm (W.om (.chi i 0))

abbrev omCore (W : G.Weil) (i : ℕ) : Om (G.V (.core (i + 1))) (G.V (.core i)) := cjOm (W.om (.core i))

variable (G) in

abbrev latRow (i : ℕ) : AddSubgroup (WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))) := depLat G (.chi i 0)

variable (G) in

abbrev latCore (i : ℕ) : AddSubgroup (WO (G.V (.core (i + 1))) (G.V (.core i))) := depLat G (.core i)

set_option genSizeOfSpec false in
set_option genInjectivity false in
variable (G) in

structure Frames where
  Lz : HSp D
  rk : Lz.rank = 1
  oz : OrthDec (G.V (.core 0)) (Yc D 0) Lz
  ζ : ℕ → Fin (negSp Lz).rank → D.host.E
  line : ∀ ρ, IsLineVec (negSp Lz) (ζ ρ)
  lnk : ∀ ρ, Lnk (negSp Lz) (ζ (ρ + 1)) (negSp Lz) (ζ ρ)
  V₀ : ℕ → HSp D
  dB : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → HypDec (G.V (.grid (2 * ρ + 2) 0)) (V₀ ρ) ρ
  oB : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → OrthDec (V₀ ρ) (G.V (.core (2 * ρ + 2))) (negSp Lz)
  nB : ∀ ρ h, VolN (dB ρ h)
  dJ : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → HypDec (G.V (.grid (2 * ρ + 1) 0)) (G.V (.core (2 * ρ + 1))) ρ
  nJ : ∀ ρ h, VolN (dJ ρ h)

namespace Frames

variable (F : Frames G) (v : CoreVol G)

abbrev bes (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : BesL D ρ :=
  ⟨_, _, _, _, F.dB ρ h, F.oB ρ h, F.ζ (ρ + 1), F.line (ρ + 1), v (2 * ρ + 2), F.nB ρ h⟩

abbrev jac (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : JacL D ρ := ⟨_, _, F.dJ ρ h, v (2 * ρ + 1), F.nJ ρ h⟩

structure Ends (W : G.Weil) (M : GlobalTheory.FunObj.Vol G) : Prop where
  bot : ∀ h, F.oz.emb (h, 1) = stabilizerEmbedding G.sp.dec0 h
  top : ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), 2 * ρ + 2 = D.R.m → ∀ (φ : ∀ i, Fn G (.core i)) (f : ∀ i, Fn G (.grid i 0)),
    RapidDec _ (φ D.R.m) → RapidDec _ (f D.R.m) → (F.bes v ρ h).per W.ψ (star (φ (2 * ρ + 2))) (star (f (2 * ρ + 2))) ≠ 0 →
      Bplus W M (φ D.R.m) (f D.R.m) ≠ 0

structure Good (W : G.Weil) (ΓL : ∀ ρ, AddSubgroup (WO (G.V (.core (2 * ρ + 1))) (negSp F.Lz))) : Prop where
  bf : ∀ ρ h (s : StBF W.ψ (F.bes v ρ h) (F.jac v ρ h)), s.om = omRow W (2 * ρ + 1) → ∃ 𝒮 Γ₀,
    Loc (F.dB ρ h) (F.dJ ρ h) s (xZero (F.dJ ρ h)) (yZero _ ρ (vecB (F.oB ρ h) (F.ζ (ρ + 1)))) 𝒮 Γ₀ (lev G (.grid (2 * ρ + 1) 0)) ∧
    (∀ Φ ∈ 𝒮, VacG W.ψ _ _ (latRow G (2 * ρ + 1)) Φ) ∧
    ∀ Ξ₁ Ξ₂, VacG W.ψ _ _ (latCore G (2 * ρ + 1)) Ξ₁ → IsThetaFunO W.ψ _ _ Ξ₂ →
      VacG W.ψ _ _ (ΓL ρ) (fun w => star (Ξ₂ ((F.lnk ρ).κ _ w))) → VacG W.ψ _ _ Γ₀ ((F.oB ρ h).boxS _ Ξ₁ Ξ₂)
  fb : ∀ σ h h' (s : StFB W.ψ (F.jac v (σ + 1) h) (F.bes v σ h')), s.om = omRow W (2 * σ + 2) → ∃ 𝒮 Γ₀,
    Loc (F.dJ (σ + 1) h) (F.dB σ h') s (xLast (F.dB σ h') (vecB (F.oB σ h') (F.ζ (σ + 1)))) 0 𝒮 Γ₀ (lev G (.grid (2 * σ + 2) 0)) ∧
    (∀ Φ ∈ 𝒮, VacG W.ψ _ _ (latRow G (2 * σ + 2)) Φ) ∧
    ∀ Ξ₁ Φ₀, VacG W.ψ _ _ (latCore G (2 * σ + 2)) Ξ₁ → VacG W.ψ _ _ (ΓL (σ + 1)) Φ₀ → VacG W.ψ _ _ Γ₀ ((F.oB σ h').boxT _ Ξ₁ Φ₀)
  lineNe : ∀ ρ, 2 * ρ + 2 ≤ D.R.m → ∃ Φ₀, VacG W.ψ _ _ (ΓL ρ) Φ₀ ∧ Φ₀ ≠ 0
  last : ∀ h, LastLat W.ψ (F.jac v 0 h) F.oz (latRow G 0) (ΓL 0) (latCore G 0)

end Frames

def TowerEx : Prop := All fun {_} _ _ _ {G} W M => ∀ v : CoreVol G, ∃ F : Frames G, F.Ends v W M ∧ ∃ ΓL, F.Good v W ΓL

def FockTot : Prop := All fun {D} _ _ _ {G} W _ => ∀ (i : Fin D.R.m) (ℓ : (WO (G.V (.grid (i.1 + 1) 0)) (G.V (.grid i.1 0)) → ℂ) → ℂ),
  Tame W.ψ _ _ ℓ → (∀ κ P, ℓ (star (W.fock (.chi i.1 0) (W.cosVec i.1 κ) P)) = 0) → ∀ f, VacG W.ψ _ _ (latRow G i.1) f → ℓ f = 0

example : TowerEx ↔ ∀ D : D7, Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (sc : Consts) (G : GridData L sc) (W : G.Weil) (M : GlobalTheory.FunObj.Vol G), M.IsRow →
      ∀ v : CoreVol G, ∃ F : Frames G, F.Ends v W M ∧ ∃ ΓL, F.Good v W ΓL := Iff.rfl

example {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) :
    flBF (B := ⟨_, _, _, _, B.d, B.o, B.ζ, B.line, B.vA, B.vN⟩) (J := ⟨_, _, J.d, J.v0, J.vN⟩) s = flatBF s := rfl

example (S T : HSp D) : Tame ψ S T fun _ => 0 :=
  ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ => continuous_const, fun _ _ => ⟨0, fun _ => by simp⟩,
    fun _ _ _ _ _ _ _ => by simp⟩

end GlobalTheory.Asc

end
