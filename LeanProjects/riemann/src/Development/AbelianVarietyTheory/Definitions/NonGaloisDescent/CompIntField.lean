import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.TowerCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevN (E : ExpSet D) (N : ℕ) : Prop :=
  N ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ N →
    p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) ∧ Squarefree N

def LevN (E : ExpSet D) : Type := {N : ℕ // IsLevN E N}

def LevN.one (E : ExpSet D) : LevN E :=
  ⟨1, one_ne_zero, fun _ hp h => absurd (Nat.dvd_one.1 h) hp.ne_one, squarefree_one⟩

def modN (E : ExpSet D) (N : ℕ) : ℕ := E.gp 0 * E.gp 1 * E.pde 0 * E.pde 1 * N

def KgW (E : ExpSet D) : Subgroup (GA D E.W) := levA E.W (Formalism.L2.DIV.Kg D.sp.cm E.W.gram E.βW E.Pg)

def InKN (E : ExpSet D) (N : ℕ) (κ : GA D E.W) : Prop :=
  κ ∈ levA E.W (Formalism.L2.DIV.Kg D.sp.cm E.W.gram E.βW (E.Pg ∪ E.Pd)) ∧
    ∃ Z : Matrix (Fin E.W.rank) (Fin E.W.rank) (Formalism.IndefR.Datum.EAf D), IsIntM Z ∧
      (E.βW⁻¹ * finE E.W κ * E.βW).val = 1 + N • Z

structure IsLevDat (E : ExpSet D) (N : ℕ) (e : AE D) (Φ : WO E.V E.W → ℂ) : Prop where
  idem : ∃ P1 : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ L ∈ P1, ((N : ℕ) : 𝓞 D.host.E) ∈ L.asIdeal) ∧
    IsIdemSum e (E.Pg ∪ E.Pd ∪ P1)
  supp : ∀ x, Φ x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapO E.V E.W E.βV E.βW x)
  inv : ∀ u, IsHalf (cA D e) u → IsIntM (frMapO E.V E.W E.βV E.βW u) → ∀ x, Φ (x + modN E N • u) = Φ x

structure IsCompFn (E : ExpSet D) (N : ℕ) (c : GA D E.W → ℂ) : Prop where
  det : ∀ g g' : GA D E.W, (mt E.W g).det = (mt E.W g').det → c g = c g'
  left : ∀ γ ∈ GQ E.W, ∀ g, c (γ * g) = c g
  arch : ∀ u ∈ GinfC E.W, ∀ g, c (g * u) = c g
  right : ∀ κ, InKN E N κ → ∀ g, c (g * κ) = c g

def IsLevG (E : ExpSet D) (F : GA D E.W → ℂ) : Prop := ∀ κ ∈ KgW E, ∀ g, F (g * κ) = F g

def serAt (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (s : GA D E.V) (φ : WO E.V E.W → ℂ) (P : C.Cf) :
    GA D E.W → ℂ :=
  fun g => thetaKO E.om s g (E.fock φ (C.rd P))

structure TowerRat (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
    (L1 FO : Subfield ℂ) where

  LQ : LevN E → Subfield ℂ

  Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ)
  numField : ∀ N, NumberField (LQ N)
  le_LQ : ∀ N, L1 ≤ LQ N
  zeta : ∀ (N : LevN E) (z : ℂ), z ^ modN E N.1 = 1 → z ∈ LQ N

  ser : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ L') →
      IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, ∀ P : C.Cf, serAt E C s φ P ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

  comp : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ c : GA D E.W → ℂ, IsCompFn E N.1 c → (∀ g, c g ∈ L') →
      ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), c * F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

  inj : ∀ (N : LevN E) (n : ℕ) (v : Fin n → GA D E.W → ℂ), (∀ a, v a ∈ Rat N) →
    LinearIndependent (LQ N) v → LinearIndependent ℂ v

  desc : ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), IsLevG E F → F ∈ Submodule.span L' Base

  field : ∀ N, LQ N ≤ FO

  one_le : LQ (LevN.one E) ≤ L1

def AdaptL (E : ExpSet D) (s : GA D E.V) : Prop :=
  ∃ k ∈ E.KV, ∃ h : GA D E.V, s = h * k ∧
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((E.l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
      ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (mt E.V h - 1) a b = 0

structure TowerInt {E : ExpSet D} {O : Type} [CommRing O] {C : CoefLat E O} {Base : Set (GA D E.W → ℂ)}
    {L1 FO : Subfield ℂ} (_T : TowerRat E C Base L1 FO) (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) where

  Int : LevN E → Submodule Λ (GA D E.W → ℂ)

  serInt : ∃ c : ℕ, ∀ (N : LevN E) (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ Λ) →
    IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ((E.l : ℂ) ^ c) • serAt E C s φ P ∈ Int N

  compInt : ∀ (N : LevN E) (c : GA D E.W → ℂ), IsCompFn E N.1 c → (∀ g, c g ∈ Λ) →
    ∀ F ∈ Int N, c * F ∈ Int N

  descInt : ∃ c₀ : ℕ, ∀ (N : LevN E) (F : GA D E.W → ℂ), F ∈ Int N → IsLevG E F → ((E.l : ℂ) ^ c₀) • F ∈ BaseInt

section Fields

variable (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
  (LQ : LevN E → Subfield ℂ) (Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ))
  (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) (Int : LevN E → Submodule Λ (GA D E.W → ℂ))

def SerField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ L') →
      IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, ∀ P : C.Cf, serAt E C s φ P ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

def CompField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ c : GA D E.W → ℂ, IsCompFn E N.1 c → (∀ g, c g ∈ L') →
      ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), c * F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ))

def InjField : Prop :=
  ∀ (N : LevN E) (n : ℕ) (v : Fin n → GA D E.W → ℂ), (∀ a, v a ∈ Rat N) →
    LinearIndependent (LQ N) v → LinearIndependent ℂ v

def DescField : Prop :=
  ∀ (N : LevN E) (L' : Subfield ℂ), LQ N ≤ L' →
    ∀ F ∈ Submodule.span L' (Rat N : Set (GA D E.W → ℂ)), IsLevG E F → F ∈ Submodule.span L' Base

def SerIntField : Prop :=
  ∃ c : ℕ, ∀ (N : LevN E) (e : AE D) (Φ φ : WO E.V E.W → ℂ), IsLevDat E N.1 e Φ → (∀ x, Φ x ∈ Λ) →
    IsThetaAt E.ψ (symplO E.V E.W) (heisO E.ψ E.V E.W) (cA D e) (latO E.V E.W E.ΛV E.ΛW fun _ => True) 1 E.f₀ Φ φ →
      ∀ s ∈ GfC E.V, AdaptL E s → ∀ P ∈ C.LL s, ((E.l : ℂ) ^ c) • serAt E C s φ P ∈ Int N

def CompIntField : Prop :=
  ∀ (N : LevN E) (c : GA D E.W → ℂ), IsCompFn E N.1 c → (∀ g, c g ∈ Λ) →
    ∀ F ∈ Int N, c * F ∈ Int N

def DescIntField : Prop :=
  ∃ c₀ : ℕ, ∀ (N : LevN E) (F : GA D E.W → ℂ), F ∈ Int N → IsLevG E F → ((E.l : ℂ) ^ c₀) • F ∈ BaseInt

variable {E C Base LQ Rat Λ BaseInt Int}

def TowerRat.ofFields {L1 FO : Subfield ℂ} (h1 : ∀ N, NumberField (LQ N)) (h2 : ∀ N, L1 ≤ LQ N)
    (h3 : ∀ (N : LevN E) (z : ℂ), z ^ modN E N.1 = 1 → z ∈ LQ N) (hs : SerField E C LQ Rat) (hc : CompField E LQ Rat)
    (hi : InjField E LQ Rat) (hd : DescField E Base LQ Rat) (h4 : ∀ N, LQ N ≤ FO) (h5 : LQ (LevN.one E) ≤ L1) :
    TowerRat E C Base L1 FO :=
  ⟨LQ, Rat, h1, h2, h3, hs, hc, hi, hd, h4, h5⟩

def TowerInt.ofFields {L1 FO : Subfield ℂ} (T : TowerRat E C Base L1 FO) (hs : SerIntField E C Λ Int)
    (hc : CompIntField E Λ Int) (hd : DescIntField E Λ BaseInt Int) : TowerInt T Λ BaseInt :=
  ⟨Int, hs, hc, hd⟩

end Fields

section Covers

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.CoverRead

variable {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hV : T.V j σ = E.W)
  (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (z : ℂ)

def scaled (X : Set (GA D (T.V j σ) → ℂ)) : Set (GA D E.W → ℂ) := {F | ∃ φ ∈ X, F = z • castDict hV φ}

def ratOf (Cv : Cover T j σ) (K : Subfield ℂ) : Submodule K (GA D E.W → ℂ) :=
  Submodule.span K (scaled hV z (Cv.ratForms a n))

def placesIn {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ) (Λ : Subring ℂ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {la | ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ}

def intOf (Cv : Cover T j σ) (Λ : Subring ℂ) : Submodule Λ (GA D E.W → ℂ) :=
  Submodule.span Λ (scaled hV z (Cv.intForms a n (placesIn Cv.σ₂ Λ)))

structure CovTie (Cv : LevN E → Cover T j σ) : Prop where
  unif : ∀ N, (Cv N).IsUnif
  lev : ∀ N, (Cv N).d.l₂.M = modN E N.1
  pos : ∀ N : LevN E, 0 < modN E N.1
  curve : ∀ N, GlobalTheory.FinalJoin.WeberIn T.Q.H (Cv N).d.c₂.F (modN E N.1) ∨ GlobalTheory.CompRat.CurveOver T.Q.H (Cv N).d.c₂.F (modN E N.1)
  lat : E.ΛW = L0c D E.W
  pl : ∀ PP ∈ E.Pg ∪ E.Pd, ((modN E 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal

end Covers

end GlobalTheory.TowerCov
