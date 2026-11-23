import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

structure IsAmb (p : X ⟶ Sp k) : Prop where

  isDomain : IsDomain k

  finite : Module.Finite ℤ k

  isProjOver : IsProjOver p

theorem isAmb_of_isArithVar {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) : IsAmb p :=
  ⟨h.isDomain, h.finite, h.isProjOver⟩

theorem IsAmb.sub {p : X ⟶ Sp k} (h : IsAmb p) (i : Y ⟶ X) [IsClosedImmersion i] : IsAmb (i ≫ p) :=
  ⟨h.isDomain, h.finite, GlobalTheory.isProjOver_comp_of_finite k X Y i p inferInstance h.isProjOver⟩

theorem IsAmb.isNoetherian {p : X ⟶ Sp k} (h : IsAmb p) : IsNoetherian X := by

  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ k)
  exact GlobalTheory.isNoetherian_of_isProjOver h.isProjOver

def HasDim (x : X) (d : ℕ) : Prop := topologicalKrullDim (closure ({x} : Set X)) = d

def clo (x : X) : Scheme.{0} := (exists_isClosedImmersion_genericPoint x).choose

def cloι (x : X) : clo x ⟶ X := (exists_isClosedImmersion_genericPoint x).choose_spec.choose

instance (x : X) : IsClosedImmersion (cloι x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose

instance (x : X) : IsIntegral (clo x) :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose

instance [IsLocallyNoetherian X] (x : X) : IsLocallyNoetherian (clo x) :=
  LocallyOfFiniteType.isLocallyNoetherian (cloι x)

theorem cloι_genericPoint (x : X) : cloι x (genericPoint (clo x)) = x :=
  (exists_isClosedImmersion_genericPoint x).choose_spec.choose_spec.choose_spec.choose_spec

section Val

variable [IsIntegral Y] {q : Y ⟶ Sp k} {e : ℕ}

def mixArch (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  FibreProj.pol (fun n => (comb L n).archInt M e hr) / e.factorial

variable [IsLocallyNoetherian Y]

def recVal (h : Y → ℝ) (L : Fin e → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : ℝ :=
  ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - mixArch L M hr

end Val

open Classical in

def resArch {q : Y ⟶ Sp k} {e : ℕ} (L : Fin e → HermLB q) (N : HermLB q) (t : N.B.Sec) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    mixArch (fun a => (L a).restr (cloι z)) (N.restr (cloι z)) (isRatSec_ratOfSec _ h) else 0

open Classical in

def resCyc [IsLocallyNoetherian Y] {B : LB Y} (hB : B.IsLB) (t : B.Sec) (g : Y → ℝ) (z : Y) : ℝ :=
  if h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) then
    ∑ᶠ w, ((divOfSec (LB.isLB_pull hB (cloι z)) _ h).mult w : ℝ) * g (cloι z w) else 0

structure IsMix (p : X ⟶ Sp k) (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) : Prop where

  iso : ∀ (d : ℕ) (L M : Fin d → HermLB p) (x : X), d ≤ m → HasDim x d → (∀ a, (L a).Isometric (M a)) → T d L x = T d M x

  symm : ∀ (d : ℕ) (L : Fin d → HermLB p) (e : Equiv.Perm (Fin d)) (x : X), d ≤ m → HasDim x d →
    T d (fun a => L (e a)) x = T d L x

  add : ∀ (d : ℕ) (A B : HermLB p) (L : Fin d → HermLB p) (x : X), d + 1 ≤ m → HasDim x (d + 1) →
    T (d + 1) (Fin.cons (A.tens B) L) x = T (d + 1) (Fin.cons A L) x + T (d + 1) (Fin.cons B L) x

  zero : ∀ (L : Fin 0 → HermLB p) (x : X), HasDim x 0 → T 0 L x = Real.log (Nat.card (X.residueField x))

  recur : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) (e : ℕ), e + 1 ≤ m → topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M : HermLB p) (L : Fin e → HermLB p) (M' : HermLB q) (L' : Fin e → HermLB q), (M.pull i hi).Isometric M' →
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r),
      T (e + 1) (Fin.cons M L) (i (genericPoint Y)) = recVal (fun z => T e L (i z)) L' M' hr

theorem isMix_zero (p : X ⟶ Sp k) : IsMix p 0 fun _ _ x => Real.log (Nat.card (X.residueField x)) where
  iso _ _ _ _ _ _ _ := rfl
  symm _ _ _ _ _ _ := rfl

  add := by intros; omega
  zero _ _ _ := rfl
  recur := by intros; omega

def ArchInteg : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e →
  ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr

def ArchRecip : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k)
  (e : ℕ), IsArithVar q (e + 1) → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec)
  (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t),
  (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) →
    mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) +
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z =
      mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) +
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z

def ArchLelong : Prop := ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k)
  (e : ℕ), IsArithVar q (e + 1) → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec)
  (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), nonzeroLocus t = ⊤ →
    mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) +
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z =
      mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht)

end GlobalTheory.MixHt
