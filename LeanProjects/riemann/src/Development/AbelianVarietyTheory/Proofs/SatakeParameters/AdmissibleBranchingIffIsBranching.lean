import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.RootMultiplicityCancellation

noncomputable section

namespace GlobalTheory.InertialTypesCmp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Formalism.MainNotions.SumRepresentations.At GlobalTheory.IndefiniteRowSideFullHecke.InertiaTypeCancellation

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ClauseQ : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (w : PlE H), (w ∈ N.S i ∨ w ∈ N.Q i) →
    (w ∈ N.Q i ∨ (Del N i ∧ (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')))) →
    A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t

def ClauseG : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (w : PlE H), w ∈ N.S i → (∃ k, w ∈ placesOver H.E (H.g k)) →
    TameGen N (N.plOm.1 w) (N.gam0 i w) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t →
    ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧
      ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t

def ClauseC : Prop := ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def Rest : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (chiC N A i (N.gam0 i w)) ≤ R.t →
    A.lpDim (A.locV i P w) = R.nV ∧
    (A.inePol (A.locV i P w) (N.gam0 i w) = 0 →
      ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim b = R.t ∧ HasInertia N A i w b 0 R.t)

def Regular : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    A.lpDim (A.locV i P w) = R.nV ∧ A.inePol (A.locV i P w) (N.gam0 i w) ≠ 0

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_sum_map {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) =
      (l.map fun k => A.lpDim (f k)).sum := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, ih]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_length_mul_of_const {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (m : ℕ) (hf : ∀ k, A.lpDim (f k) = m) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) = l.length * m := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, hf, ih, add_mul, add_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_spehLoc_eq_mul (p : _root_.Formalism.BasicNotions.Part A.CG) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.spehLoc N A p w) = p.a * p.d := by
  unfold _root_.Formalism.MainNotions.N.spehLoc
  rw [lpDim_foldr_lpSum_eq_length_mul_of_const N A _ p.a (fun k => by rw [_root_.Formalism.BasicNotions.NAut.lpDim_tw, _root_.Formalism.BasicNotions.NAut.locG_dim])]
  simp [mul_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
theorem _root_.GlobalTheory.InertialTypesCmp.lpDim_isoLoc (P : List (_root_.Formalism.BasicNotions.Part A.CG)) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.isoLoc N A P w) = _root_.Formalism.MainNotions.N.rankIso N A P := by
  unfold _root_.Formalism.MainNotions.N.isoLoc _root_.Formalism.MainNotions.N.rankIso
  rw [lpDim_foldr_lpSum_eq_sum_map]
  simp [lpDim_spehLoc_eq_mul]

end GlobalTheory.InertialTypesCmp

end
