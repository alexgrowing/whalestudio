import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffEv

noncomputable section

open MvPowerSeries

namespace GlobalTheory.FrameBiextId

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

variable (k d) in

def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add, ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q k d n := ⟨pt k d j, CZ.pt j⟩

theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := by
  intro j i
  exact (b j).2 i

def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := by
  unfold sb
  exact evHom_apply (czQ b) f

def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (X (j, i)) = (b j).1 i
  rw [sb_apply]
  exact ev_X (czQ b) j i

theorem sb_sb {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  show ev (fun j => (b j).1) ((a j).1 i) = sb b ((a j).1 i)
  rw [sb_apply]

theorem sb_gen (f : PS k n d) : sb gen f = f := by
  rw [sb_apply]
  exact ev_pt f

def E2 (f : PS k 2 d) (u v : Q k d n) : PS k n d := sb ![u, v] f

def E3 (f : PS k 3 d) (u v w : Q k d n) : PS k n d := sb ![u, v, w] f

@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q k d l) (f : PS k 2 d) (u v : Q k d n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

@[simp] theorem formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q k d l) (f : PS k 3 d) (u v w : Q k d n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  have h : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  show sb ![gen 0, gen 1] f = f
  have h : (![gen 0, gen 1] : Fin 2 → Q k d 2) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

theorem formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  show sb ![gen 0, gen 1, gen 2] f = f
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q k d 3) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

def ac (A : Q k d 1) (u : Q k d n) : Q k d n := sq ![u] A

@[simp] theorem sq_ac (b : Fin n → Q k d l) (A : Q k d 1) (u : Q k d n) : sq b (ac A u) = ac A (sq b u) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u] (A.1 i)) = sb ![sq b u] (A.1 i)
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j
    fin_cases j
    rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_eq_ev (f : PS k 2 d) (u v : Q k d n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem formalSeriesValueAtThreePoints_eq_ev (f : PS k 3 d) (u v w : Q k d n) : E3 f u v w = ev ![u.1, v.1, w.1] f := by
  show sb ![u, v, w] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ac_val (A : Q k d 1) (u : Q k d n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j
  rfl

def op (F : Q k d 2) (u v : Q k d n) : Q k d n := sq ![u, v] F

theorem op_val (F : Q k d 2) (u v : Q k d n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sq_op (b : Fin n → Q k d l) (F : Q k d 2) (u v : Q k d n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u, v] (F.1 i)) = sb ![sq b u, sq b v] (F.1 i)
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem gen_val (j : Fin n) : (gen j : Q k d n).1 = pt k d j := rfl

theorem ext_of_trunc {R σ : Type} [CommRing R] [Finite σ] {f g : MvPowerSeries σ R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) g)) : f = g := by
  ext e
  have h1 := h (Finsupp.degree e)
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h1
  have h2 := h1 e (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, coeff_truncTotal _ (Nat.lt_succ_self _),
    coeff_truncTotal _ (Nat.lt_succ_self _), sub_eq_zero] at h2
  exact h2

end GlobalTheory.FrameBiextId
