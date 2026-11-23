import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

def symTup {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) : Fin N → R :=
  fun j => (Finset.univ.val.map c).esymm ((j : ℕ) + 1) ^ (N.factorial / ((j : ℕ) + 1))

def Prim {V K : Type} [CommRing V] [Field K] (i : V →+* K) {J : Type} (c : J → K) : Prop :=
  (∀ a, i.IsIntegralElem (c a)) ∧ ∃ a, c a ≠ 0 ∧ i.IsIntegralElem (c a)⁻¹

abbrev PCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) : Prop :=
  SecCoord (ProjSpace.O1 o n) (ProjSpace.coord o n) x v

section

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

abbrev SecAt {R : Type} [CommRing R] (x : Sp R ⟶ S) : Type := LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))

def SecAt.pull {R K : Type} [CommRing R] [CommRing K] {x : Sp R ⟶ S} (θ : SecAt G L x) (i : R →+* K) :
    SecAt G L (spMap i ≫ x) :=
  VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) θ

def ThList (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (θ : SecAt G L x) {N : ℕ} (pt : Fin N → (Over.mk x ⟶ G))
    (c : Fin N → K) : Prop :=
  Function.Injective pt ∧ (∀ a, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn (c a))) ∧
    ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 →
      ∃ a, p.left = spMap i ≫ (pt a).left

def HasTh (m : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N : ℕ} (c : Fin N → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)), IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c

def HasTh₂ (m m' : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {N N' : ℕ} (c : Fin N → K) (c' : Fin N' → K) : Prop :=
  ∃ (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (pt' : Fin N' → (Over.mk x ⟶ G)),
    IsGenSec G L _ θ ∧ ThList G L ρ m x θ pt c ∧ ThList G L ρ m' x θ pt' c'

def SymAt (m : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) {N : ℕ} (e : Fin N → R) : Prop :=
  ∀ (K : Type) [Field K] (i : R →+* K) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K),
    ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ∀ j, i (e j) = symTup c j

def ThMap (m : ℕ) {o : Type} [CommRing o] {n : ℕ} {X : Scheme.{0}} (q : X ⟶ S) (f : X ⟶ PSpace o n) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ X) (c : Fin (n + 1) → K), HasTh G L ρ m (x ≫ q) c → PCrd (x ≫ f) (symTup c)

def PolFib (g : ℕ) {R : Type} [CommRing R] (x : Sp R ⟶ S) : Prop :=
  ∃ (P : PolAV (Sp R)) (α : P.A.left ⟶ G.left), P.g = g ∧ IsGrpPullback P.A G x α ∧ LBIso P.L (L.pull α)

variable {G L ρ}

theorem hasTh_iff {m : ℕ} {K : Type} [Field K] {x : Sp K ⟶ S} {N : ℕ} {c : Fin N → K} :
    HasTh G L ρ m x c ↔ HasTh₂ G L ρ m m x c c :=
  ⟨fun ⟨θ, pt, h, h'⟩ => ⟨θ, pt, pt, h, h', h'⟩, fun ⟨θ, pt, _, h, h', _⟩ => ⟨θ, pt, h, h'⟩⟩

end

theorem symTup_one {R : Type} [CommRing R] (c : Fin 1 → R) : symTup c 0 = c 0 := by
  simp [symTup, Multiset.esymm, Multiset.powersetCard_one]

end GlobalTheory.UMin
