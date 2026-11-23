import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Lat

open NumberField IsDedekindDomain Module
open scoped Pointwise

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)

abbrev toO (U : Submodule E S.V) : Submodule (𝓞 E) S.V := U.restrictScalars (𝓞 E)

def orth (U : Submodule E S.V) : Submodule E S.V := ⨅ x ∈ U, LinearMap.ker (S.hT x)

def spanE (M : Submodule (𝓞 E) S.V) : Submodule E S.V := Submodule.span E (M : Set S.V)

section Any

variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def dualInH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : Submodule (𝓞 E) V :=
  Formalism.HermitianLatticesTheory.dual h M ⊓ (Submodule.span E (M : Set V)).restrictScalars (𝓞 E)

def genIdxH (A B : Submodule (𝓞 E) V) : ℝ :=
  ∏ᶠ P : HeightOneSpectrum (𝓞 E),
    ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.lidx P.asIdeal A B)

def latDetH (h : V →ₗ⋆[E] V →ₗ[E] E) (M : Submodule (𝓞 E) V) : ℝ :=
  Real.sqrt (genIdxH (dualInH h M) M)

def IsPrimitiveSub (M₀ L : Submodule (𝓞 E) V) : Prop :=
  M₀ ≤ L ∧ M₀ = L ⊓ (Submodule.span E (M₀ : Set V)).restrictScalars (𝓞 E)

end Any

abbrev dualIn (M : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) S.V := dualInH S.hT M

abbrev genIdx (A B : Submodule (𝓞 E) S.V) : ℝ := genIdxH A B

abbrev latDet (M : Submodule (𝓞 E) S.V) : ℝ := latDetH S.hT M

def idx (A B : Submodule (𝓞 E) S.V) : ℕ := Nat.card (A ⧸ B.comap A.subtype)

def nrm (τ : E →+* ℂ) (x : S.V) : ℝ := (τ (S.hT x x)).re

omit [NumberField E] in

def placeProd (X : (E →+* ℂ) → ℝ) : ℝ := Real.sqrt (∏ τ : E →+* ℂ, X τ)

def NE (g : ℕ) : ℝ := (g : ℝ) ^ (Module.finrank ℚ E)

abbrev SplitsCompletely (p : ℕ) : Prop := Formalism.MainNotions.S.SplitsCompl E p

variable (Λ : Submodule (𝓞 E) S.V)

def ModG (g : ℕ) (x : S.V) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
    x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ))

def IsAutLam (β : S.V ≃ₗ[E] S.V) : Prop :=
  β ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ Formalism.HermitianLatticesTheory.gmap β Λ = Λ

structure LFlag (r : ℕ) (T : E) where
  fl : Formalism.MainNotions.S.FlagG S r T
  zt : S.V

variable {S} {r : ℕ}

abbrev frame {T : E} (F : LFlag S r T) : Fin (r + 1) → S.V := F.fl.fvec

abbrev Xsp {T : E} (F : LFlag S r T) : Submodule E S.V := F.fl.X

abbrev Xflag {T : E} (F : LFlag S r T) (j : ℕ) : Submodule E S.V := F.fl.Xa j

abbrev Xplus {T : E} (F : LFlag S r T) : Submodule E S.V := F.fl.Xplus

def XLam {T : E} (F : LFlag S r T) : Submodule (𝓞 E) S.V := Λ ⊓ toO S (Xsp F)

def Lrep {T : E} (F : LFlag S r T) : Submodule (𝓞 E) S.V := Λ ⊓ toO S (orth S (Xsp F))

def Lsub {T : E} (F : LFlag S r T) : Submodule (𝓞 E) S.V :=
  (Lrep Λ F ⊔ toO S (Xsp F)) ⊓ toO S (orth S (Xsp F))

def L0sub {T : E} (F : LFlag S r T) : Submodule (𝓞 E) S.V :=
  Lsub Λ F ⊓ toO S (LinearMap.ker (S.hT F.fl.z))

def IsLift {T : E} (F : LFlag S r T) : Prop := F.fl.z ∈ Λ ∧ F.zt = F.fl.z

def IsFixedConv (g : ℕ) {T : E} (F : LFlag S r T) : Prop :=
  (∀ P : HeightOneSpectrum (𝓞 E), ∃ c : Fin r → E, (∀ a, c a ≠ 0) ∧
    (((g : 𝓞 E) ∈ P.asIdeal) → ∀ a, c a = 1) ∧
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)))) ∧
  (∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c)

abbrev ZhatL {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E := Formalism.MainNotions.S.Zhat F.fl F'.fl

abbrev Dr {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : E := Formalism.MainNotions.S.Dl F.fl F'.fl r

abbrev Dr1 {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : E :=
  Formalism.MainNotions.S.Dl F.fl F'.fl (r + 1)

abbrev Gval {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') : E := Formalism.MainNotions.S.Gflag F.fl F'.fl

section Hyp

variable (T T' : ℕ)

def ch (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ) : ℝ :=
  ‖τ (Dr1 F F' / Dr F F')‖ / Real.sqrt ((T : ℝ) * T')

def sh (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ) : ℝ :=
  Real.sqrt (ch T T' F F' τ ^ 2 - 1)

def onePlusChSh (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ) : ℝ :=
  if Dr F F' = 0 then 1 else (1 + ch T T' F F' τ) / sh T T' F F' τ

def chSh (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ) : ℝ :=
  if Dr F F' = 0 then 1 else ch T T' F F' τ / sh T T' F F' τ

def invSh (F : LFlag S r (T : E)) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ) : ℝ :=
  if Dr F F' = 0 then 0 else 1 / sh T T' F F' τ

end Hyp

def frameAct {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) : Fin n → S.V :=
  fun b => ∑ a, ((ξ a b : 𝓞 E) : E) • f a

def AdmWit {T T' : E} (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧
    ∀ b, ModG S Λ g (frame F' b - frameAct (frame F) ξ b)

def IsAdmissible {T T' : E} (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  ∃ ξ, AdmWit Λ g F F' ξ

def IsTerm {T T' : E} (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  IsLift Λ F' ∧ IsAdmissible Λ g F F' ∧ Gval F F' ≠ 0

section Term

variable {T T' : E}

def UU (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} ⊔ XLam Λ F' ⊔ Submodule.span (𝓞 E) {F'.zt}

def UUE (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V := spanE S (UU Λ F F')

def BLat (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Λ ⊓ toO S (UUE Λ F F')

abbrev BQ (F : LFlag S r T) (F' : LFlag S r T') : Type :=
  BLat Λ F F' ⧸ (UU Λ F F').comap (BLat Λ F F').subtype

def gB (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) (BQ Λ F F') :=
  Ideal.span {(g : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (BQ Λ F F'))

def noZ (F : LFlag S r T) (F' : LFlag S r T') : Set (BQ Λ F F') :=
  {c | ∃ w : BLat Λ F F', (w : S.V) ∈ Xsp F ⊔ Xsp F' ∧ Submodule.Quotient.mk w = c}

def Hp (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V := orth S (UUE Λ F F')

def Thp (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V := Λ ⊓ toO S (Hp Λ F F')

def NgX (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F ⊔ XLam Λ F'

def IotaRel (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (x : S.V) : Prop :=
  ∃ l ∈ Lrep Λ F, x - l ∈ Xsp F ∧ ∃ l' ∈ Lrep Λ F', x - l' ∈ Xsp F' ∧ l - l' ∈ NgX Λ g F F'

def La (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E)
    {x | x ∈ Hp Λ F F' ∧ x ∈ L0sub Λ F ∧ x ∈ L0sub Λ F' ∧ IotaRel Λ g F F' x}

def iIdx (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : ℕ := idx S (La Λ g F F') (Thp Λ F F')

def NG (F : LFlag S r T) (F' : LFlag S r T') : ℝ := latDet S (UU Λ F F')

def G0 (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : ℝ := NG Λ F F' / NE (E := E) g ^ (r + 1)

def Ylift (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V :=
  UUE Λ F F' ⊓ orth S (Xplus F)

def Ylift' (F : LFlag S r T) (F' : LFlag S r T') : Submodule E S.V :=
  UUE Λ F F' ⊓ orth S (Xplus F')

def SgRel (F : LFlag S r T) (F' : LFlag S r T') (y y' : S.V) (al al' : E) : Prop :=
  ∃ x ∈ Xsp F, ∃ x' ∈ Xsp F', y - y' = (al • F.zt + x) + (al' • F'.zt + x')

end Term

section Pair

variable {T T' : E} (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)

def IotaCompat (g : ℕ) : Prop :=
  ∀ x' ∈ Lrep Λ F', ∀ l ∈ Lrep Λ F, (l - x' ∈ NgX Λ g F F' ↔ l - β x' ∈ NgX Λ g F F'')

def IsPair (g : ℕ) : Prop :=
  IsAutLam S Λ β ∧ (∀ j, (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j) ∧
    β F'.fl.z = F''.fl.z ∧ IotaCompat Λ F F' F'' β g

def ThPairs : Submodule E (S.V × S.V) :=
  ((Hp Λ F F').prod (Hp Λ F F'')) ⊓
    (Xsp F).comap (LinearMap.fst E S.V S.V - LinearMap.snd E S.V S.V) ⊓
    (Xsp F'').comap ((β : S.V →ₗ[E] S.V) ∘ₗ LinearMap.fst E S.V S.V - LinearMap.snd E S.V S.V)

def Th : Submodule E S.V := (ThPairs Λ F F' F'' β).map (LinearMap.fst E S.V S.V)

def Th'' : Submodule E S.V := (ThPairs Λ F F' F'' β).map (LinearMap.snd E S.V S.V)

def s0 (k : ℕ) : ℕ := k - finrank E (Th Λ F F' F'' β)

def Mlat (g : ℕ) : Submodule (𝓞 E) S.V := La Λ g F F' ⊓ toO S (Th Λ F F' F'' β)

def Mlat'' (g : ℕ) : Submodule (𝓞 E) S.V := La Λ g F F'' ⊓ toO S (Th'' Λ F F' F'' β)

def WHypG (W : Submodule E S.V) (k : ℕ) : Prop :=
  W ⊔ Xsp F = orth S (Xplus F) ∧ W ⊓ Xsp F = ⊥ ∧ finrank E W = k

def Ssp (W : Submodule E S.V) : Submodule E S.V := W ⊓ orth S (Th Λ F F' F'' β)

def IsProjS (W : Submodule E S.V) (x s : S.V) : Prop :=
  s ∈ Ssp Λ F F' F'' β W ∧ x - s ∈ Th Λ F F' F'' β ⊔ Xsp F

def Psi (W : Submodule E S.V) (M : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {s | ∃ x ∈ M, IsProjS Λ F F' F'' β W x s}

def bForm (x' x'' : S.V) : E := S.hT x' x'' - S.hT (β x') x''

def BNondeg : Prop :=
  (∀ x' ∈ Hp Λ F F', (∀ x'' ∈ Hp Λ F F'', bForm β x' x'' = 0) → x' ∈ Th Λ F F' F'' β) ∧
  (∀ x'' ∈ Hp Λ F F'', (∀ x' ∈ Hp Λ F F', bForm β x' x'' = 0) → x'' ∈ Th'' Λ F F' F'' β)

def radL : Submodule E S.V :=
  Hp Λ F F' ⊓ ⨅ x'' ∈ Hp Λ F F'',
    LinearMap.ker ((S.hT.flip x'') - (S.hT.flip x'').comp (β : S.V →ₗ[E] S.V))

def radR : Submodule E S.V :=
  Hp Λ F F'' ⊓ ⨅ x' ∈ Hp Λ F F', LinearMap.ker (S.hT x' - S.hT (β x'))

def IsScalar : Prop :=
  ∀ y1 ∈ Ylift Λ F F', ∀ y2 ∈ Ylift Λ F F'', ∀ y1' ∈ Ylift' Λ F F', ∀ y2'' ∈ Ylift' Λ F F'',
    y1 - y2 ∈ Xsp F → y2'' - β y1' ∈ Xsp F'' →
      ∀ al al' : E, SgRel F F' y1 y1' al al' ↔ SgRel F F'' y2 y2'' al al'

end Pair

def Mplus {T T' : E} (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E)
    ((XLam Λ F : Set S.V) ∪ {F.zt} ∪
      Set.range fun b => ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b))

def IsGeneric {T T' : E} (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Prop :=
  ∃ ξ, AdmWit Λ g F F' ξ ∧ ∀ P : HeightOneSpectrum (𝓞 E),
    (((g : 𝓞 E) ∈ P.asIdeal) → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ))) ∧
    (((g : 𝓞 E) ∉ P.asIdeal) → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')))

def NLam {T : E} (F : LFlag S r T) : Set (S.V ≃ₗ[E] S.V) :=
  {n | IsAutLam S Λ n ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j) ∧
    (∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F)}

def NEquiv {T T' : E} (F : LFlag S r T) (F' F'₂ : LFlag S r T') : Prop :=
  ∃ n ∈ NLam Λ F, (∀ a, n (F'.fl.e a) = F'₂.fl.e a) ∧ n F'.fl.z = F'₂.fl.z

omit [NumberField E] [StarRing E] in

def ZEquiv {n : ℕ} (Z Z₂ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ A B : Matrix (Fin n) (Fin n) (𝓞 E),
    (∀ a b, a < b → A a b = 0) ∧ (∀ a, A a a = 1) ∧ (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧
    Z₂ = A.map (fun x => (x : E)) * Z * B.map (fun x => (x : E))

end Gen

section D7

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev hS : HSpace D.host.E := D.sp.Y 0

def Wsp : Submodule D.host.E (hS D).V := LinearMap.range (D.sp.iXY 0)

def gS : ℕ := D.host.g 0 * D.host.g 1

def Tu (u : D.what₂.Word) : ℕ := (D.mem u).A.T

def PrimeHyp (u : D.what₂.Word) (T' : ℕ) : Prop :=
  (Tu D u).Prime ∧ 3 ≤ Tu D u ∧ T'.Prime ∧ 3 ≤ T' ∧
  SplitsCompletely (E := D.host.E) (Tu D u) ∧ SplitsCompletely (E := D.host.E) T' ∧
  (∀ i, SplitsCompletely (E := D.host.E) (D.host.g i)) ∧
  Nat.Coprime (gS D) (Tu D u * T') ∧ Tu D u ≡ T' [MOD gS D] ∧
  (∀ ζ : 𝓞 D.host.E, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) →
    (∃ β : 𝓞 D.host.E, ζ - 1 = (Tu D u : 𝓞 D.host.E) * β) → ζ = 1)

def FixedHyp (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T : D.host.E} (F : LFlag (hS D) D.R.rS T) :
    Prop :=
  Submodule.IsLattice D.host.E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ ∧ IsLift Λ F ∧
    IsFixedConv Λ (gS D) F

def WHyp {T : D.host.E} (F : LFlag (hS D) D.R.rS T) (W : Submodule D.host.E (hS D).V) : Prop :=
  WHypG F W D.R.k

def L0X (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T : D.host.E} (F : LFlag (hS D) D.R.rS T) :
    Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
  (L0sub Λ F).comap (((D.sp.iXY 0).restrictScalars (𝓞 D.host.E)))

end D7

end Formalism.MainNotions.S.Lat

end
