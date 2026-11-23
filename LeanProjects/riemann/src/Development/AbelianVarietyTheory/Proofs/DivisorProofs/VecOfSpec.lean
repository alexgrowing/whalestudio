import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianVarietyLineBundleSectionsFinite
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyPerfectSectionsComplexOfNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

open GlobalTheory.AbLaw

variable {Rg : Type} [CommRing Rg]

def ringOf {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
  g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom

def cstT {T : Scheme.{0}} (t : T ⟶ Sp Rg) : Rg →+* Γ(T, ⊤) :=
  t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom

theorem ringOf_X {T : Scheme.{0}} {n : ℕ} (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (k : Fin n) :
    ringOf g (MvPolynomial.X k) = coord g k := rfl

def expand (mA mB : ℕ) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg) :=
  MvPolynomial.eval₂ (MvPolynomial.C.comp MvPolynomial.C)
    (fun j => ∑ i, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i) F

variable {A₀ : Scheme.{0}} {N : LB A₀} {mA : ℕ}

def monSec (a : Fin mA → LB.Sec N) (d : ℕ) (ν : Fin mA →₀ ℕ) : LB.Sec (GlobalTheory.AbLaw.pw N (d : ℤ)) where
  f := fun q => if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0
  compat := fun (q q' : N.ι) => by
    change (A₀.presheaf.map (homOfLE (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q)).op).hom
        (if ∑ i, ν i = d then ∏ i, ((a i).f q) ^ ν i else 0) =
      ((N.g q q' ^ (d : ℤ) : Γ(A₀, N.U q ⊓ N.U q')ˣ) : Γ(A₀, N.U q ⊓ N.U q')) *
        (A₀.presheaf.map (homOfLE (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q')).op).hom
          (if ∑ i, ν i = d then ∏ i, ((a i).f q') ^ ν i else 0)
    split_ifs with h
    · simp only [map_prod, map_pow]
      simp only [(a _).compat, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    · simp only [map_zero, mul_zero]

omit [CommRing Rg] in
theorem idPb {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) :
    IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact IsPullback.id_horiz f

variable {X : Scheme.{0}} {M : LB X}

def vecOf {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : Fin Q.a → Rg :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).1

theorem vecOf_ker {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) : (Q.D₀.map (RingHom.id Rg)).mulVec (vecOf Q s) = 0 :=
  ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)).2

theorem vecOf_spec {f : X ⟶ Sp Rg} (Q : Perf f M) (s : LB.Sec M) (i : Q.I) :
    rs X (le_pull M (𝟙 X) (Q.le i)) ((finSecPullId s).f (fun _ => Q.ch i)) =
      ∑ k, cst f ((𝟙 X) ⁻¹ᵁ Q.W i) (vecOf Q s k) * (Scheme.Hom.app (𝟙 X) (Q.W i)).hom (Q.u k i) := by
  have h := (Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose_spec
    ((Q.sec Rg (RingHom.id Rg) X (𝟙 X) f (idPb f)).choose.symm (finSecPullId s)) i
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {mB : ℕ} {f : A₀ ⟶ Sp Rg}

def polys (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (d : ℕ) (F : MvPolynomial (Fin mB) Rg)
    (k : Fin (Q d).a) : MvPolynomial (Fin (mA * mB)) Rg :=
  ∑ ν ∈ (expand mA mB F).support, (expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k)

def formIdeal (Q : ∀ d : ℕ, Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) {B₀ : Scheme.{0}} {H : LB B₀}
    (fB : B₀ ⟶ Sp Rg) (b : Fin mB → LB.Sec H) : Ideal (MvPolynomial (Fin (mA * mB)) Rg) :=
  Ideal.span {P | ∃ (d : ℕ) (F : MvPolynomial (Fin mB) Rg) (k : Fin (Q d).a),
    F.IsHomogeneous d ∧ Kills fB b F ∧ P = polys Q a d F k}

end GlobalTheory.FormsLocus
