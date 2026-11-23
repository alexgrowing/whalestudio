import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.Mum.TensTor

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def GtRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
    (v'.s χ' : F) * wv (N'.c χ') * wv v'.b =
      ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F) *
        wv (N'.c χ' * v'.b) * wv 1

def QRelV (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) {k : ℕ}
    (q' : N'.QT k) (qs : Fin r → N.QT k) : Prop :=
  (∀ i, e q'.1.1.toAdd i = (qs i).1.1.toAdd) ∧ GtRelV W φ e wv q'.1.2 (fun j => (qs j).1.2)

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def cmp (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) (j : Fin r) : N.A :=
  ν.eA.symm (ν'.eA x ≫ T.pr j)

def chi (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (χ : N'.X) (i : Fin r) : N.X :=
  ν.eX.symm (T.xe (ν'.eX χ) i)

def wv (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (x : N'.A) : F :=
  valF (ν'.eA x).left _
    (T.w.s (fun k => ν.J ((ν'.eA x).left ≫ tensφ T.pr k), ν'.J (ν'.eA x).left)).val

def GtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (v' : N'.Gt) (vs : Fin r → N.Gt) : Prop :=
  GtRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') v' vs

def PtRel (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') {k : ℕ} (p' : QkPt D' F k)
    (ps : Fin r → QkPt D F k) : Prop :=
  ∃ (q' : N'.QT k) (qs : Fin r → N.QT k), ν'.QPt p' q' ∧ (∀ i, ν.QPt (ps i) (qs i)) ∧
    QRelV W (cmp T ν ν') (chi T ν ν') (wv T ν ν') q' qs

end GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

section Facts

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def TensFacts (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) :
    Prop :=
  (∀ x y j, φ (x * y) j = φ x j * φ y j) ∧ Function.Bijective φ ∧
  (∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) ∧ Function.Bijective e ∧
  (∀ χ' j, φ (N'.c χ') j = N.c (e χ' j)) ∧ (∀ x, wv x ≠ 0) ∧
  (∀ x y u, (N'.θ x y u : F) * wv (x * y * u) * wv x * wv y * wv u =
    ((∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j : Fˣ) : F) *
      wv (x * y) * wv (x * u) * wv (y * u) * wv 1) ∧
  ∀ χ', (N'.ψ χ' : F) * wv 1 = wv (N'.c χ') * ((∏ i, ∏ j, N.τ (e χ' i) (e χ' j) ^ W i j : Fˣ) : F)

end Facts

end GlobalTheory.Mum.TensTor
