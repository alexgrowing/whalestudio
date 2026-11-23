import Mathlib

noncomputable section

namespace GlobalTheory.SmGL

section Blocks

open Matrix

variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def blk (e : (Σ a, m a) ≃ n) (i : n) : α := (e.symm i).1

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
omit [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n]
  [DecidableEq n] in

@[simp] theorem _root_.GlobalTheory.SmGL.blk_apply (e : (Σ a, m a) ≃ n) (a : α) (i : m a) :
    _root_.GlobalTheory.SmGL.blk e (e ⟨a, i⟩) = a := by
  simp [_root_.GlobalTheory.SmGL.blk]

abbrev Levi (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Type :=
  ∀ a, GL (m a) R

def parab (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) where
  carrier := {g | (g : Matrix n n R).BlockTriangular (blk e)}
  one_mem' := by
    show ((1 : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_one]; exact blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
    rw [Units.val_mul]; exact BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
    have : Invertible (x : Matrix n n R) := x.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hx

variable {R}

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ i j, _root_.GlobalTheory.SmGL.blk e j <
      _root_.GlobalTheory.SmGL.blk e i → (g : Matrix n n R) i j = 0 :=
  ⟨fun h _ _ hij => h hij, fun h _ _ hij => h _ _ hij⟩

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parab_iff {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R e ↔ ∀ a b (i : m a) (j : m b), b < a →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parab]
  constructor
  · intro h a b i j hab
    exact h _ _ (by simpa using hab)
  · intro h i j hij
    simpa using h (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 hij

variable (R)

def diagBlock (e : (Σ a, m a) ≃ n) (a : α) : parab R e →* Matrix (m a) (m a) R where
  toFun p := ((p : GL n R) : Matrix n n R).submatrix (fun i => e ⟨a, i⟩) (fun i => e ⟨a, i⟩)
  map_one' := by
    ext i j
    simp [Matrix.one_apply]
  map_mul' x y := by
    ext i j
    show ((x.1 : Matrix n n R) * (y.1 : Matrix n n R)) _ _ = _
    simp only [mul_apply, submatrix_apply]
    rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
    · intro b _ hb
      refine Finset.sum_eq_zero fun l _ => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · rw [mem_parab_iff.1 x.2 a b i l h, zero_mul]
      · rw [mem_parab_iff.1 y.2 b a l j h, mul_zero]
    · simp

def leviProj (e : (Σ a, m a) ≃ n) : parab R e →* Levi R m :=
  MonoidHom.pi fun a => (diagBlock R e a).toHomUnits

@[simp] theorem leviProj_apply (e : (Σ a, m a) ≃ n) (p : parab R e) (a : α) (i j : m a) :
    (leviProj R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl

open Classical in

def leviEmb {α : Type} {m : α → Type} [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (e : (Σ a, m a) ≃ n) : Levi R m →* GL n R :=
  MonoidHom.toHomUnits
    { toFun := fun g => Matrix.reindex e e (blockDiagonal' fun a => (g a : Matrix (m a) (m a) R))
      map_one' := by
        have : (fun a => (((1 : Levi R m) a : GL (m a) R) : Matrix (m a) (m a) R)) = 1 := rfl
        rw [this, blockDiagonal'_one]
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun g h => by
        have : (fun a => (((g * h : Levi R m) a : GL (m a) R) : Matrix (m a) (m a) R)) =
          fun a => (g a : Matrix (m a) (m a) R) * (h a : Matrix (m a) (m a) R) := rfl
        rw [this, blockDiagonal'_mul]
        simp [Matrix.submatrix_mul_equiv] }

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [LinearOrder α] in

@[simp] theorem _root_.GlobalTheory.SmGL.leviEmb_apply_same (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) (a : α) (i j : m a) :
    (_root_.GlobalTheory.SmGL.leviEmb R e g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) R) i j := by
  simp [_root_.GlobalTheory.SmGL.leviEmb, blockDiagonal'_apply_eq]

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [LinearOrder α] in

theorem _root_.GlobalTheory.SmGL.leviEmb_apply_ne (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) {a b : α} (h : a ≠ b) (i : m a) (j : m b) :
    (_root_.GlobalTheory.SmGL.leviEmb R e g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  classical
  simp [_root_.GlobalTheory.SmGL.leviEmb, blockDiagonal'_apply_ne _ _ _ h]

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.leviEmb_mem_parab (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈ _root_.GlobalTheory.SmGL.parab R e :=
  _root_.GlobalTheory.SmGL.mem_parab_iff.2 fun _ _ i j hab =>
    _root_.GlobalTheory.SmGL.leviEmb_apply_ne R e g hab.ne' i j

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in

@[simp] theorem _root_.GlobalTheory.SmGL.leviProj_leviEmb (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviProj R e ⟨_root_.GlobalTheory.SmGL.leviEmb R e g,
      _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g⟩ = g := by
  funext a
  ext i j
  simp

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
private lemma bijective_blockPosition_of_equiv_sigma (e : (Σ a, m a) ≃ n) (a : α) :
    Function.Bijective fun i : m a =>
      (⟨e ⟨a, i⟩, _root_.GlobalTheory.SmGL.blk_apply e a i⟩ :
        {k : n // _root_.GlobalTheory.SmGL.blk e k = a}) := by
  constructor
  · intro i j hij
    have h := e.injective (Subtype.ext_iff.1 hij)
    simpa using h
  · rintro ⟨k, hk⟩
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective k
    simp only [_root_.GlobalTheory.SmGL.blk_apply] at hk
    subst hk
    exact ⟨i, rfl⟩

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.det_parab (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    GeneralLinearGroup.det (p : GL n R) =
      ∏ a, GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviProj R e p a) := by
  have hp : ((p : GL n R) : Matrix n n R).BlockTriangular (_root_.GlobalTheory.SmGL.blk e) := p.2
  ext
  rw [GeneralLinearGroup.val_det_apply, Units.coe_prod, hp.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [GeneralLinearGroup.val_det_apply,
    ← Matrix.det_submatrix_equiv_self (Equiv.ofBijective _ (bijective_blockPosition_of_equiv_sigma e a))]
  rfl

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
omit [LinearOrder α] in

theorem _root_.GlobalTheory.SmGL.det_leviEmb (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.leviEmb R e g) =
      ∏ a, GeneralLinearGroup.det (g a) := by
  classical
  letI : LinearOrder α := LinearOrder.lift' _ (Fintype.equivFin α).injective
  have h := _root_.GlobalTheory.SmGL.det_parab R e
    ⟨_, _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g⟩
  rwa [_root_.GlobalTheory.SmGL.leviProj_leviEmb] at h

def unipRad (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := (leviProj R e).ker.map (parab R e).subtype

variable {R}

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in

theorem _root_.GlobalTheory.SmGL.mem_unipRad {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipRad R e ↔ g ∈ _root_.GlobalTheory.SmGL.parab R e ∧ ∀ a (i j : m a),
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j := by
  rw [_root_.GlobalTheory.SmGL.unipRad, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun a i j => ?_⟩
    have h := congr_arg (fun x : _root_.GlobalTheory.SmGL.Levi R m =>
      ((x a : GL (m a) R) : Matrix (m a) (m a) R) i j) (MonoidHom.mem_ker.1 hp)
    simpa using h
  · rintro ⟨hg, h⟩
    refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    funext a
    ext i j
    simp [h]

variable (R)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.unipRad_le_parab (e : (Σ a, m a) ≃ n) :
    _root_.GlobalTheory.SmGL.unipRad R e ≤ _root_.GlobalTheory.SmGL.parab R e := fun _ hg =>
  (_root_.GlobalTheory.SmGL.mem_unipRad.1 hg).1

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.coe_mem_unipRad {e : (Σ a, m a) ≃ n}
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    (p : GL n R) ∈ _root_.GlobalTheory.SmGL.unipRad R e ↔ _root_.GlobalTheory.SmGL.leviProj R e p = 1 :=
  (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective _)).trans MonoidHom.mem_ker

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
private lemma conj_mem_unipRad_of_mem_parab {e : (Σ a, m a) ≃ n} {p u : GL n R}
    (hp : p ∈ _root_.GlobalTheory.SmGL.parab R e) (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) :
    p * u * p⁻¹ ∈ _root_.GlobalTheory.SmGL.unipRad R e := by
  have hu' := _root_.GlobalTheory.SmGL.unipRad_le_parab R e hu
  let P : _root_.GlobalTheory.SmGL.parab R e := ⟨p, hp⟩
  let U : _root_.GlobalTheory.SmGL.parab R e := ⟨u, hu'⟩
  have hU : _root_.GlobalTheory.SmGL.leviProj R e U = 1 :=
    (_root_.GlobalTheory.SmGL.coe_mem_unipRad R U).1 hu
  show ((P * U * P⁻¹ : _root_.GlobalTheory.SmGL.parab R e) : GL n R) ∈ _
  rw [_root_.GlobalTheory.SmGL.coe_mem_unipRad, map_mul, map_mul, map_inv, hU,
    mul_one, mul_inv_cancel]

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.parab_le_normalizer (e : (Σ a, m a) ≃ n) :
    _root_.GlobalTheory.SmGL.parab R e ≤
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRad R e : Set (GL n R)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact conj_mem_unipRad_of_mem_parab R hp
  · intro h
    have := conj_mem_unipRad_of_mem_parab R (inv_mem hp) h
    simpa [mul_assoc] using this

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.leviEmb_mem_normalizer (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRad R e : Set (GL n R)) :=
  _root_.GlobalTheory.SmGL.parab_le_normalizer R e
    (_root_.GlobalTheory.SmGL.leviEmb_mem_parab R e g)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.exists_levi_mul_unip (e : (Σ a, m a) ≃ n)
    (p : _root_.GlobalTheory.SmGL.parab R e) :
    ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad R e,
      (p : GL n R) = _root_.GlobalTheory.SmGL.leviEmb R e (_root_.GlobalTheory.SmGL.leviProj R e p) * u := by
  let L : _root_.GlobalTheory.SmGL.parab R e :=
    ⟨_root_.GlobalTheory.SmGL.leviEmb R e (_root_.GlobalTheory.SmGL.leviProj R e p),
      _root_.GlobalTheory.SmGL.leviEmb_mem_parab R e _⟩
  refine ⟨((L⁻¹ * p : _root_.GlobalTheory.SmGL.parab R e) : GL n R),
    (_root_.GlobalTheory.SmGL.coe_mem_unipRad R _).2 ?_, ?_⟩
  · rw [map_mul, map_inv, _root_.GlobalTheory.SmGL.leviProj_leviEmb, inv_mul_cancel]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mul_inv_cancel_left _ _).symm

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.det_eq_one_of_mem_unipRad {e : (Σ a, m a) ≃ n} {u : GL n R}
    (hu : u ∈ _root_.GlobalTheory.SmGL.unipRad R e) : GeneralLinearGroup.det u = 1 := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hu
  show GeneralLinearGroup.det (p : GL n R) = 1
  rw [_root_.GlobalTheory.SmGL.det_parab, MonoidHom.mem_ker.1 hp]
  simp

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
open Classical in

theorem _root_.GlobalTheory.SmGL.continuous_leviEmb [TopologicalSpace R] {α : Type} {m : α → Type}
    [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) :
    Continuous (_root_.GlobalTheory.SmGL.leviEmb R e) := by
  have hval : Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m =>
      ((_root_.GlobalTheory.SmGL.leviEmb R e g : GL n R) : Matrix n n R) := by
    show Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m =>
      Matrix.reindex e e (blockDiagonal' fun a => (g a : Matrix (m a) (m a) R))
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun a => Units.continuous_val.comp (continuous_apply a))).matrix_reindex e e
  have hinv : Continuous fun g : _root_.GlobalTheory.SmGL.Levi R m => g⁻¹ :=
    continuous_pi fun a => Units.continuous_iff.2
      ⟨Units.continuous_coe_inv.comp (continuous_apply a),
        by simp; exact Units.continuous_val.comp (continuous_apply a)⟩
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  convert hval.comp hinv using 1
  funext g
  simp [map_inv]

def opp (e : (Σ a, m a) ≃ n) : (Σ a : αᵒᵈ, m (OrderDual.ofDual a)) ≃ n := e

def parabLower (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := parab R (opp e)

def unipRadLower (e : (Σ a, m a) ≃ n) : Subgroup (GL n R) := unipRad R (opp e)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in

theorem _root_.GlobalTheory.SmGL.mem_parabLower_iff {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parabLower R e ↔ ∀ a b (i : m a) (j : m b), a < b →
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
  unfold _root_.GlobalTheory.SmGL.parabLower
  rw [_root_.GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h (OrderDual.toDual a) (OrderDual.toDual b) i j hab
  · intro h a b i j hab
    exact h (OrderDual.ofDual a) (OrderDual.ofDual b) i j hab

def leviProjLower (e : (Σ a, m a) ≃ n) : parabLower R e →* Levi R m := leviProj R (opp e)

@[simp] theorem leviProjLower_apply (e : (Σ a, m a) ≃ n) (p : parabLower R e) (a : α) (i j : m a) :
    (leviProjLower R e p a : Matrix (m a) (m a) R) i j =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.mem_unipRadLower {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipRadLower R e ↔ g ∈ _root_.GlobalTheory.SmGL.parabLower R e ∧
      ∀ a (i j : m a),
      (g : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) R) i j :=
  _root_.GlobalTheory.SmGL.mem_unipRad (e := _root_.GlobalTheory.SmGL.opp e)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.leviEmb_mem_parabLower (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈ _root_.GlobalTheory.SmGL.parabLower R e :=
  (_root_.GlobalTheory.SmGL.mem_parabLower_iff R).2 fun _ _ i j hab =>
    _root_.GlobalTheory.SmGL.leviEmb_apply_ne R e g hab.ne i j

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.leviEmb_mem_normalizer_lower (e : (Σ a, m a) ≃ n)
    (g : _root_.GlobalTheory.SmGL.Levi R m) :
    _root_.GlobalTheory.SmGL.leviEmb R e g ∈
      Subgroup.normalizer (_root_.GlobalTheory.SmGL.unipRadLower R e : Set (GL n R)) :=
  _root_.GlobalTheory.SmGL.parab_le_normalizer R (_root_.GlobalTheory.SmGL.opp e)
    (_root_.GlobalTheory.SmGL.leviEmb_mem_parabLower R e g)

def stdBlocks {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N) : (Σ a, Fin (d a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr h)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in

theorem _root_.GlobalTheory.SmGL.stdBlocks_val {s N : ℕ} (d : Fin s → ℕ) (h : ∑ a, d a = N)
    (a : Fin s) (i : Fin (d a)) :
    (_root_.GlobalTheory.SmGL.stdBlocks d h ⟨a, i⟩ : ℕ) =
      ∑ b : Fin a, d (Fin.castLE a.2.le b) + i := by
  simp [_root_.GlobalTheory.SmGL.stdBlocks, finSigmaFinEquiv_apply]

@[reducible] def Two (a b : Type) : Bool → Type
  | false => a
  | true => b

variable {a b : Type}

instance [Fintype a] [Fintype b] : ∀ x, Fintype (Two a b x)
  | false => inferInstanceAs (Fintype a)
  | true => inferInstanceAs (Fintype b)

instance [DecidableEq a] [DecidableEq b] : ∀ x, DecidableEq (Two a b x)
  | false => inferInstanceAs (DecidableEq a)
  | true => inferInstanceAs (DecidableEq b)

def two (e : a ⊕ b ≃ n) : (Σ x, Two a b x) ≃ n :=
  Equiv.trans
    { toFun := fun x => match x with
        | ⟨false, i⟩ => Sum.inl i
        | ⟨true, j⟩ => Sum.inr j
      invFun := fun y => match y with
        | Sum.inl i => ⟨false, i⟩
        | Sum.inr j => ⟨true, j⟩
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (_ | _) <;> rfl } e

omit [Fintype n] [DecidableEq n] in

@[simp] theorem two_false (e : a ⊕ b ≃ n) (i : a) : two e ⟨false, i⟩ = e (Sum.inl i) := rfl

omit [Fintype n] [DecidableEq n] in

@[simp] theorem two_true (e : a ⊕ b ≃ n) (j : b) : two e ⟨true, j⟩ = e (Sum.inr j) := rfl

def stdSum {r t N : ℕ} (h : r + t = N) : Fin r ⊕ Fin t ≃ Fin N := finSumFinEquiv.trans (finCongr h)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in

@[simp] theorem _root_.GlobalTheory.SmGL.stdSum_inl {r t N : ℕ} (h : r + t = N) (i : Fin r) :
    (_root_.GlobalTheory.SmGL.stdSum h (Sum.inl i) : ℕ) = i := by
  simp [_root_.GlobalTheory.SmGL.stdSum]

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in

@[simp] theorem _root_.GlobalTheory.SmGL.stdSum_inr {r t N : ℕ} (h : r + t = N) (j : Fin t) :
    (_root_.GlobalTheory.SmGL.stdSum h (Sum.inr j) : ℕ) = r + j := by
  simp [_root_.GlobalTheory.SmGL.stdSum]

variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def leviTwo (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] :
    GL a R × GL b R ≃* Levi R (Two a b) where
  toFun g := fun x => match x with
    | false => g.1
    | true => g.2
  invFun g := (g false, g true)
  left_inv _ := rfl
  right_inv g := by funext x; cases x <;> rfl
  map_mul' g h := by funext x; cases x <;> rfl

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.continuous_leviTwo [TopologicalSpace R] :
    Continuous (_root_.GlobalTheory.SmGL.leviTwo R a b) :=
  continuous_pi fun x => by
    cases x
    · exact continuous_fst
    · exact continuous_snd

def emb₂ (e : a ⊕ b ≃ n) : GL a R × GL b R →* GL n R :=
  (leviEmb R (two e)).comp (leviTwo R a b).toMonoidHom

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.val_emb₂ (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    (_root_.GlobalTheory.SmGL.emb₂ R e g : Matrix n n R) =
      Matrix.reindex e e (fromBlocks g.1.val 0 0 g.2.val) := by
  ext i j
  obtain ⟨s, rfl⟩ := e.surjective i
  obtain ⟨t, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) false s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) (by decide : false ≠ true) s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) (by decide : true ≠ false) s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) true s t

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.det_emb₂ (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.emb₂ R e g) =
      GeneralLinearGroup.det g.1 * GeneralLinearGroup.det g.2 := by
  rw [_root_.GlobalTheory.SmGL.emb₂, MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.det_leviEmb,
    Fintype.prod_bool, mul_comm]
  rfl

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.mem_parab_two {e : a ⊕ b ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two e) ↔
      ∀ (j : b) (i : a), (g : Matrix n n R) (e (.inr j)) (e (.inl i)) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · intro h j i
    exact h true false j i (by decide)
  · intro h x y i j hxy
    rcases x with _ | _ <;> rcases y with _ | _
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)
    · exact h i j
    · exact absurd hxy (by decide)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.mem_parabLower_two {e : a ⊕ b ≃ n} {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) ↔
      ∀ (i : a) (j : b), (g : Matrix n n R) (e (.inl i)) (e (.inr j)) = 0 := by
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_iff]
  constructor
  · intro h i j
    exact h false true i j (by decide)
  · intro h x y i j hxy
    rcases x with _ | _ <;> rcases y with _ | _
    · exact absurd hxy (by decide)
    · exact h i j
    · exact absurd hxy (by decide)
    · exact absurd hxy (by decide)

def points (n : Type) : (Σ _ : n, Unit) ≃ n := Equiv.sigmaUnique n fun _ => Unit

omit [Fintype n] [DecidableEq n] in

@[simp] theorem points_apply (i : n) (u : Unit) : points n ⟨i, u⟩ = i := rfl

def leviTorus (n : Type) : (n → Rˣ) ≃* Levi R (fun _ : n => Unit) where
  toFun t i := GeneralLinearGroup.scalar Unit (t i)
  invFun g i := GeneralLinearGroup.det (g i)
  left_inv t := by
    funext i
    ext
    simp [GeneralLinearGroup.scalar]
  right_inv g := by
    funext i
    ext x y
    simp [GeneralLinearGroup.scalar]
  map_mul' s t := by
    funext i
    simp

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.continuous_leviTorus [TopologicalSpace R] (n : Type) :
    Continuous (_root_.GlobalTheory.SmGL.leviTorus R n) :=
  continuous_pi fun i => Units.continuous_iff.2
    ⟨continuous_pi fun x => continuous_pi fun y => by
        simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar]
        exact Units.continuous_val.comp (continuous_apply i),
      continuous_pi fun x => continuous_pi fun y => by
        simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar]
        exact Units.continuous_coe_inv.comp (continuous_apply i)⟩

def diagT (n : Type) [Fintype n] [DecidableEq n] : (n → Rˣ) →* GL n R :=
  (leviEmb R (points n)).comp (leviTorus R n).toMonoidHom

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.val_diagT (t : n → Rˣ) :
    (_root_.GlobalTheory.SmGL.diagT R n t : Matrix n n R) = diagonal fun i => (t i : R) := by
  ext i j
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq]
    exact (_root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.points n)
      (_root_.GlobalTheory.SmGL.leviTorus R n t) i () ()).trans
        (by simp [_root_.GlobalTheory.SmGL.leviTorus, GeneralLinearGroup.scalar])
  · rw [diagonal_apply_ne _ h]
    exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.points n)
      (_root_.GlobalTheory.SmGL.leviTorus R n t) h () ()

def borel (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := parab R (points n)

def unipB (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := unipRad R (points n)

def unipBLower (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n] : Subgroup (GL n R) := unipRadLower R (points n)

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.mem_borel {n : Type} [Fintype n] [DecidableEq n]
    [LinearOrder n] {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.borel R n ↔ ∀ i j, j < i → (g : Matrix n n R) i j = 0 :=
  _root_.GlobalTheory.SmGL.mem_parab

open Matrix in
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
variable {R} in
variable (R) in
variable {R} in
variable (R) in
variable {a b : Type} in
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in

theorem _root_.GlobalTheory.SmGL.mem_unipB {n : Type} [Fintype n] [DecidableEq n]
    [LinearOrder n] {g : GL n R} :
    g ∈ _root_.GlobalTheory.SmGL.unipB R n ↔
      (∀ i j, j < i → (g : Matrix n n R) i j = 0) ∧ ∀ i, (g : Matrix n n R) i i = 1 := by
  show g ∈ _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.points n) ↔ _
  rw [_root_.GlobalTheory.SmGL.mem_unipRad]
  refine and_congr _root_.GlobalTheory.SmGL.mem_parab ⟨fun h i => ?_, fun h a i j => ?_⟩
  · exact (h i () ()).trans (one_apply_eq ())
  · cases i
    cases j
    exact (h a).trans (one_apply_eq ()).symm

end Blocks

end GlobalTheory.SmGL
