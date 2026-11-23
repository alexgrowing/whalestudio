import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRegular
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

namespace GlobalTheory.DepthZeroJac

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData GlobalTheory.IwahoriInj ValuativeRel Matrix

section Group

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem mem_fixed_sup {A B : Subgroup G} {v : V} (hA : v ∈ fixed π A) (hB : v ∈ fixed π B) :
    v ∈ fixed π (A ⊔ B) := by
  let H : Subgroup G :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *; rw [hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have h : A ⊔ B ≤ H := sup_le (fun g hg => mem_fixed.1 hA g hg) (fun g hg => mem_fixed.1 hB g hg)
  exact mem_fixed.2 fun g hg => h hg

theorem fixed_anti {A B : Subgroup G} (h : A ≤ B) {v : V} (hv : v ∈ fixed π B) : v ∈ fixed π A :=
  mem_fixed.2 fun g hg => mem_fixed.1 hv g (h hg)

theorem apply_mem_twKer_of_normalizer {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {v : V} (hv : v ∈ twKer π H 1) : π g v ∈ twKer π H 1 :=
  twKer_le_comap π H g hg hv

end Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Cong

variable {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w * g * w⁻¹ ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w * g * w⁻¹).val - 1 = w.val * (g.val - 1) * (w⁻¹).val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).1.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).2

theorem mem_normalizer_KOne {w : GL n k} (hw : w ∈ KO k n) :
    w ∈ Subgroup.normalizer (KOne k n : Set (GL n k)) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => conj_mem_KOne hw hg, fun hg => ?_⟩
  have := conj_mem_KOne (inv_mem hw) hg
  simpa [mul_assoc] using this

end Cong

section Red

variable (k) in

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

variable (k) in

abbrev red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem incl_mem_KO (a : GL (Fin n) 𝒪[k]) : incl k n a ∈ KO k (Fin n) := ⟨a, rfl⟩

theorem incl_mem_KOne {a : GL (Fin n) 𝒪[k]} (h : red k n a = 1) : incl k n a ∈ KOne k (Fin n) := ⟨a, h, rfl⟩

theorem red_surjective (n : ℕ) : Function.Surjective (red k n) := by
  intro B
  choose A hA using fun i j => IsLocalRing.residue_surjective (B.val i j)
  have hm : (IsLocalRing.residue 𝒪[k]).mapMatrix (Matrix.of A) = B.val := Matrix.ext hA
  have hdet : IsUnit (Matrix.of A).det := by
    rw [← isUnit_map_iff (IsLocalRing.residue 𝒪[k]), RingHom.map_det, hm]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨u, Units.ext ?_⟩
  show (IsLocalRing.residue 𝒪[k]).mapMatrix u.val = B.val
  rw [hu, hm]

variable {π : Representation ℂ (GL (Fin n) k) V}

theorem incl_apply_eq {w : V} (hw : w ∈ fixed π (KOne k (Fin n))) {a b : GL (Fin n) 𝒪[k]}
    (h : red k n a = red k n b) : π (incl k n a) w = π (incl k n b) w := by
  have h1 : incl k n (b⁻¹ * a) ∈ KOne k (Fin n) := incl_mem_KOne (by rw [map_mul, h, map_inv, inv_mul_cancel])
  have : incl k n a = incl k n b * incl k n (b⁻¹ * a) := by rw [← map_mul, mul_inv_cancel_left]
  rw [this, map_mul, Module.End.mul_apply, mem_fixed.1 hw _ h1]

theorem apply_mem_fixed {w : V} (hw : w ∈ fixed π (KOne k (Fin n))) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    π g w ∈ fixed π (KOne k (Fin n)) := by
  refine mem_fixed.2 fun h hh => ?_
  have := mem_fixed.1 hw _ (conj_mem_KOne (inv_mem hg) hh)
  rw [← Module.End.mul_apply, ← map_mul]
  conv_rhs => rw [← this]
  rw [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

def repF (π : Representation ℂ (GL (Fin n) k) V) :
    Representation ℂ (GL (Fin n) 𝓀[k]) (fixed π (KOne k (Fin n))) where
  toFun u := (π (incl k n (Function.surjInv (red_surjective n) u))).restrict
    fun _ hw => apply_mem_fixed hw (incl_mem_KO _)
  map_one' := LinearMap.ext fun w => Subtype.ext (by
    show π (incl k n _) w = w
    rw [incl_apply_eq w.2 (b := 1) (by rw [Function.surjInv_eq (red_surjective (k := k) n), map_one])]
    simp)
  map_mul' u v := LinearMap.ext fun w => Subtype.ext (by
    show π (incl k n _) w = π (incl k n _) (π (incl k n _) w)
    rw [incl_apply_eq w.2 (b := Function.surjInv (red_surjective n) u * Function.surjInv (red_surjective n) v)
      (by rw [map_mul, Function.surjInv_eq (red_surjective (k := k) n), Function.surjInv_eq (red_surjective (k := k) n),
        Function.surjInv_eq (red_surjective (k := k) n)]), map_mul, map_mul]
    rfl)

theorem repF_red (π : Representation ℂ (GL (Fin n) k) V) (a : GL (Fin n) 𝒪[k]) (w : fixed π (KOne k (Fin n))) :
    (repF π (red k n a) w : V) = π (incl k n a) w :=
  incl_apply_eq w.2 (Function.surjInv_eq _ _)

end Red

section Blocks

variable {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) (T : Finset (Fin s))

def pr (A : Type) [Ring A] : Matrix (Fin n) (Fin n) A := diagonal fun i => if blk e i ∈ T then 1 else 0

def qr (A : Type) [Ring A] : Matrix (Fin n) (Fin n) A := diagonal fun i => if blk e i ∈ T then 0 else 1

variable {A : Type} [Ring A]

theorem pr_mul_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (pr e T A * M) i j = if blk e i ∈ T then M i j else 0 := by
  simp only [pr, diagonal_mul]; split_ifs <;> simp

theorem mul_pr_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (M * pr e T A) i j = if blk e j ∈ T then M i j else 0 := by
  simp only [pr, mul_diagonal]; split_ifs <;> simp

theorem qr_mul_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (qr e T A * M) i j = if blk e i ∈ T then 0 else M i j := by
  simp only [qr, diagonal_mul]; split_ifs <;> simp

theorem mul_qr_apply (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (M * qr e T A) i j = if blk e j ∈ T then 0 else M i j := by
  simp only [qr, mul_diagonal]; split_ifs <;> simp

theorem pr_mul_pr : pr e T A * pr e T A = pr e T A := by
  ext i j; rw [pr_mul_apply]; simp only [pr, diagonal_apply]; split_ifs <;> simp_all

theorem qr_mul_qr : qr e T A * qr e T A = qr e T A := by
  ext i j; rw [qr_mul_apply]; simp only [qr, diagonal_apply]; split_ifs <;> simp_all

theorem pr_mul_qr : pr e T A * qr e T A = 0 := by
  ext i j; rw [pr_mul_apply]; simp only [qr, diagonal_apply]; split_ifs <;> simp_all

theorem qr_mul_pr : qr e T A * pr e T A = 0 := by
  ext i j; rw [qr_mul_apply]; simp only [pr, diagonal_apply]; split_ifs <;> simp_all

theorem pr_add_qr : pr e T A + qr e T A = 1 := by
  ext i j; simp only [pr, qr, Matrix.add_apply, diagonal_apply, one_apply]; split_ifs <;> simp_all

theorem ne_of_side {i j : Fin n} (h : ¬ (blk e i ∈ T ↔ blk e j ∈ T)) : i ≠ j := by
  rintro rfl; exact h Iff.rfl

theorem mem_U_iff (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    u ∈ GlobalTheory.OppRad.U (pr e T A) (qr e T A) ↔ ∀ i j, ¬ (blk e i ∈ T ∧ blk e j ∉ T) → (u.val - 1) i j = 0 := by
  rw [GlobalTheory.OppRad.mem_U]
  constructor
  · rintro ⟨h1, h2⟩ i j h
    have a1 := congrFun (congrFun h1 i) j
    have a2 := congrFun (congrFun h2 i) j
    rw [pr_mul_apply] at a1
    rw [mul_qr_apply] at a2
    split_ifs at a1 a2 <;> simp_all
  · intro h
    constructor <;> ext i j
    · rw [pr_mul_apply]; split_ifs with h1
      · rfl
      · exact (h i j (by tauto)).symm
    · rw [mul_qr_apply]; split_ifs with h1
      · exact (h i j (by tauto)).symm
      · rfl

theorem mem_U_iff' (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    u ∈ GlobalTheory.OppRad.U (qr e T A) (pr e T A) ↔ ∀ i j, ¬ (blk e i ∉ T ∧ blk e j ∈ T) → (u.val - 1) i j = 0 := by
  rw [GlobalTheory.OppRad.mem_U]
  constructor
  · rintro ⟨h1, h2⟩ i j h
    have a1 := congrFun (congrFun h1 i) j
    have a2 := congrFun (congrFun h2 i) j
    rw [qr_mul_apply] at a1
    rw [mul_pr_apply] at a2
    split_ifs at a1 a2 <;> simp_all
  · intro h
    constructor <;> ext i j
    · rw [qr_mul_apply]; split_ifs with h1
      · exact (h i j (by tauto)).symm
      · rfl
    · rw [mul_pr_apply]; split_ifs with h1
      · rfl
      · exact (h i j (by tauto)).symm

theorem comm_pr_of_side {u : Matrix (Fin n) (Fin n) A}
    (h : ∀ i j, ¬ (blk e i ∈ T ↔ blk e j ∈ T) → (u - 1) i j = 0) :
    u * pr e T A = pr e T A * u ∧ u * qr e T A = qr e T A * u := by
  have h' : ∀ i j, ¬ (blk e i ∈ T ↔ blk e j ∈ T) → u i j = 0 := fun i j hij => by
    have := h i j hij
    rwa [Matrix.sub_apply, one_apply_ne (ne_of_side e T hij), sub_zero] at this
  constructor <;> ext i j
  · rw [mul_pr_apply, pr_mul_apply]
    by_cases a : blk e i ∈ T <;> by_cases b : blk e j ∈ T <;> simp only [a, b, if_true, if_false] <;>
      first | rfl | exact (h' i j (by tauto)).symm | exact h' i j (by tauto)
  · rw [mul_qr_apply, qr_mul_apply]
    by_cases a : blk e i ∈ T <;> by_cases b : blk e j ∈ T <;> simp only [a, b, if_true, if_false] <;>
      first | rfl | exact (h' i j (by tauto)).symm | exact h' i j (by tauto)

end Blocks

section Dia

variable {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {c : k} (hc : c ≠ 0)

def dia (C : Fin s → ℕ) : GL (Fin n) k :=
  ⟨diagonal fun i => c ^ C (blk e i), diagonal fun i => (c ^ C (blk e i))⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext i; exact mul_inv_cancel₀ (pow_ne_zero _ hc),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext i; exact inv_mul_cancel₀ (pow_ne_zero _ hc)⟩

theorem dia_val (C : Fin s → ℕ) : (dia e hc C).val = diagonal fun i => c ^ C (blk e i) := rfl

theorem dia_inv_val (C : Fin s → ℕ) : ((dia e hc C)⁻¹).val = diagonal fun i => (c ^ C (blk e i))⁻¹ := rfl

theorem dia_add (C C' : Fin s → ℕ) : dia e hc (fun a => C a + C' a) = dia e hc C * dia e hc C' :=
  Units.ext (by rw [Units.val_mul, dia_val, dia_val, dia_val, diagonal_mul_diagonal]; simp only [pow_add])

theorem dia_zero : dia e hc (fun _ => 0) = 1 :=
  Units.ext (by rw [dia_val]; simp)

theorem conj_sub_apply (C : Fin s → ℕ) (g : GL (Fin n) k) (i j : Fin n) :
    ((dia e hc C * g * (dia e hc C)⁻¹).val - 1) i j =
      c ^ C (blk e i) * (g.val - 1) i j * (c ^ C (blk e j))⁻¹ := by
  have : (dia e hc C * g * (dia e hc C)⁻¹).val - 1 =
      (dia e hc C).val * (g.val - 1) * ((dia e hc C)⁻¹).val := by
    simp [mul_sub, sub_mul]
  rw [this, dia_val, dia_inv_val, mul_diagonal, diagonal_mul]

theorem conj'_sub_apply (C : Fin s → ℕ) (g : GL (Fin n) k) (i j : Fin n) :
    (((dia e hc C)⁻¹ * g * dia e hc C).val - 1) i j =
      (c ^ C (blk e i))⁻¹ * (g.val - 1) i j * c ^ C (blk e j) := by
  have : ((dia e hc C)⁻¹ * g * dia e hc C).val - 1 =
      ((dia e hc C)⁻¹).val * (g.val - 1) * (dia e hc C).val := by
    simp [mul_sub, sub_mul]
  rw [this, dia_val, dia_inv_val, mul_diagonal, diagonal_mul]

theorem deep_pow {a : ℤ} {x : k} (h : Deep a x) (m : ℕ) : Deep (m * a) (x ^ m) := by
  induction m with
  | zero => simp [Deep]
  | succ m ih =>
    rw [pow_succ]
    exact (ih.mul h).mono (by push_cast; linarith)

variable {e hc}

theorem deep_conj (hc1 : Deep 1 c) (hc2 : Deep (-1) c⁻¹) {A B : ℕ} {t : ℤ} {x : k} (hx : Deep t x) :
    Deep ((A : ℤ) - B + t) (c ^ A * x * (c ^ B)⁻¹) := by
  have h1 := deep_pow hc1 A
  have h2 := deep_pow hc2 B
  rw [← inv_pow]
  exact ((h1.mul hx).mul h2).mono (by linarith)

theorem deep_conj' (hc1 : Deep 1 c) (hc2 : Deep (-1) c⁻¹) {A B : ℕ} {t : ℤ} {x : k} (hx : Deep t x) :
    Deep ((B : ℤ) - A + t) ((c ^ A)⁻¹ * x * c ^ B) := by
  have h1 := deep_pow hc1 B
  have h2 := deep_pow hc2 A
  rw [← inv_pow]
  exact ((h2.mul hx).mul h1).mono (by linarith)

end Dia

section Lift

variable {n : ℕ}

theorem exists_lift {Z : Fin n → Fin n → Prop} (hZ : ∀ i l j, Z i l → Z l j → False)
    (u : GL (Fin n) 𝓀[k]) (hu : ∀ i j, ¬ Z i j → (u.val - 1) i j = 0) :
    ∃ a : GL (Fin n) 𝒪[k], red k n a = u ∧ (∀ i j, ¬ Z i j → ((incl k n a).val - 1) i j = 0) ∧
      ∀ i j, ¬ Z i j → ((incl k n a⁻¹).val - 1) i j = 0 := by
  classical
  let L : 𝓀[k] → 𝒪[k] := fun y => if y = 0 then 0 else Function.surjInv IsLocalRing.residue_surjective y
  have hL : ∀ y, IsLocalRing.residue 𝒪[k] (L y) = y := fun y => by
    by_cases h : y = 0
    · simp [L, h]
    · simp only [L, if_neg h]; exact Function.surjInv_eq _ _
  let Y : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => L ((u.val - 1) i j)
  have hYz : ∀ i j, ¬ Z i j → Y i j = 0 := fun i j h => by
    show L ((u.val - 1) i j) = 0
    rw [hu i j h]; simp [L]
  have hYY : Y * Y = 0 := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun (l : Fin n) _ => ?_
    by_cases h1 : Z i l
    · by_cases h2 : Z l j
      · exact (hZ i l j h1 h2).elim
      · rw [hYz l j h2, mul_zero]
    · rw [hYz i l h1, zero_mul]
  refine ⟨⟨1 + Y, 1 - Y, by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩, Units.ext ?_, ?_, ?_⟩
  · have : (IsLocalRing.residue 𝒪[k]).mapMatrix Y = u.val - 1 := by ext i j; exact hL _
    show (IsLocalRing.residue 𝒪[k]).mapMatrix (1 + Y) = u.val
    rw [map_add, map_one, this, add_sub_cancel]
  · intro i j h
    show ((algebraMap 𝒪[k] k).mapMatrix (1 + Y) - 1) i j = 0
    rw [map_add, map_one, add_sub_cancel_left]
    simp [hYz i j h]
  · intro i j h
    show ((algebraMap 𝒪[k] k).mapMatrix (1 - Y) - 1) i j = 0
    rw [map_sub, map_one, sub_sub_cancel_left]
    simp [hYz i j h]

theorem red_sub_apply {a : GL (Fin n) 𝒪[k]} {i j : Fin n} (h : ((incl k n a).val - 1) i j = 0) :
    ((red k n a).val - 1) i j = 0 := by
  have h1 : ((a.val i j : 𝒪[k]) : k) = (((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j : 𝒪[k]) : k) := by
    rw [Matrix.sub_apply, sub_eq_zero] at h
    refine h.trans ?_
    simp only [one_apply]; split_ifs <;> simp
  have h2 : a.val i j = (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j := Subtype.ext h1
  show (IsLocalRing.residue 𝒪[k] (a.val i j)) - (1 : Matrix (Fin n) (Fin n) 𝓀[k]) i j = 0
  rw [h2, sub_eq_zero]
  simp only [one_apply]; split_ifs <;> simp

theorem intM_incl (a : GL (Fin n) 𝒪[k]) : IntM (incl k n a).val := fun i j => (a.val i j).2

end Lift

section Conj

variable {n s : ℕ} {d : Fin s → ℕ}

variable (e : (Σ a, Fin (d a)) ≃ Fin n) in

abbrev Gp : Subgroup (GL (Fin n) k) := KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))

def ind (T : Finset (Fin s)) (a : Fin s) : ℕ := if a ∈ T then 1 else 0

theorem mem_int_of_deep {x : k} (h : Deep 0 x) : x ∈ 𝒪[k] := deep_zero_iff.1 h

theorem deep_of_mem_int {x : k} (h : x ∈ 𝒪[k]) : Deep 0 x := deep_zero_iff.2 h

variable {e : (Σ a, Fin (d a)) ≃ Fin n} {T : Finset (Fin s)} {c : k} {hc : c ≠ 0}

theorem one_apply_blk (a : Fin s) (i j : Fin (d a)) :
    (1 : Matrix (Fin n) (Fin n) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j := by
  simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem mem_unipRad_of {g : GL (Fin n) k} (h : ∀ i j, ¬ blk e i < blk e j → (g.val - 1) i j = 0) :
    g ∈ unipRad k e := by
  refine mem_unipRad.2 ⟨fun i j hij => ?_, fun a i j => ?_⟩
  · have := h i j (not_lt.2 hij.le)
    rwa [Matrix.sub_apply, one_apply_ne (fun e' => by rw [e'] at hij; exact lt_irrefl _ hij), sub_zero] at this
  · have := h (e ⟨a, i⟩) (e ⟨a, j⟩) (by simp)
    rw [Matrix.sub_apply, sub_eq_zero] at this
    rw [this, one_apply_blk]

theorem blk_lt_of_side (hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T) {i j : Fin n} (hi : blk e i ∈ T)
    (hj : blk e j ∉ T) : blk e i < blk e j := by
  by_contra h
  exact hj (hT _ _ (not_lt.1 h) hi)

theorem deep_sub_one_of_intM {g : Matrix (Fin n) (Fin n) k} (hg : IntM g) (i j : Fin n) : Deep 0 ((g - 1) i j) :=
  deep_of_mem_int (by rw [sub_eq_add_neg]; exact (hg.add (intM_one (k := k) (n := Fin n)).neg) i j)

variable (hc1 : Deep 1 c) (hc2 : Deep (-1) c⁻¹)
include hc1 hc2

theorem conj_KOne_mem (hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T) {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) :
    (dia e hc (ind T))⁻¹ * g * dia e hc (ind T) ∈ Gp e := by
  set h := (dia e hc (ind T))⁻¹ * g * dia e hc (ind T) with hh
  have hd : ∀ i j, Deep ((ind T (blk e j) : ℤ) - ind T (blk e i) + 1) ((h.val - 1) i j) := fun i j => by
    rw [hh, conj'_sub_apply]
    exact deep_conj' hc1 hc2 (deep_one_iff.2 (mem_KOne.1 hg i j))
  let Y : Matrix (Fin n) (Fin n) k := pr e T k * h.val * qr e T k
  have hY : ∀ i j, Y i j = if blk e i ∈ T ∧ blk e j ∉ T then h.val i j else 0 := fun i j => by
    simp only [Y, mul_qr_apply, pr_mul_apply]; split_ifs <;> simp_all
  have hcu : ∀ i j, blk e i ∈ T → blk e j ∉ T → h.val i j = (h.val - 1) i j := fun i j hi hj => by
    rw [Matrix.sub_apply, one_apply_ne (fun e' => by rw [e'] at hi; exact hj hi), sub_zero]
  have hYi : IntM Y := fun i j => by
    rw [hY]; split_ifs with hij
    · rw [hcu i j hij.1 hij.2]
      refine mem_int_of_deep ((hd i j).mono ?_)
      simp [ind, hij.1, hij.2]
    · exact zero_mem _
  have hYY : Y * Y = 0 := by
    simp only [Y, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (qr e T k) (pr e T k), qr_mul_pr]; simp
  let E : Matrix (Fin n) (Fin n) k := h.val - 1 - Y
  have hE : MaxM E := fun i j => by
    simp only [E, Matrix.sub_apply]
    rw [hY]; split_ifs with hij
    · rw [← Matrix.sub_apply, hcu i j hij.1 hij.2, sub_self, map_zero]; exact zero_lt_one
    · rw [sub_zero]
      refine deep_one_iff.1 ((hd i j).mono ?_)
      by_cases a : blk e i ∈ T <;> by_cases b : blk e j ∈ T <;> simp_all [ind]
  let nu : GL (Fin n) k := ⟨1 + Y, 1 - Y, by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩
  have hnu : nu ∈ unipRad k e ⊓ KO k (Fin n) := by
    refine ⟨mem_unipRad_of fun i j hij => ?_, mem_KO.2 ⟨intM_one.add hYi, ?_⟩⟩
    · show (1 + Y - 1) i j = 0
      rw [add_sub_cancel_left, hY, if_neg fun h' => hij (blk_lt_of_side hT h'.1 h'.2)]
    · show IntM (1 - Y)
      rw [sub_eq_add_neg]; exact intM_one.add hYi.neg
  have hk : nu⁻¹ * h ∈ KOne k (Fin n) := by
    refine mem_KOne.2 ?_
    have e1 : h.val = 1 + Y + E := by simp only [E]; abel
    have e2 : (nu⁻¹ * h).val - 1 = E - Y * E := by
      show (1 - Y) * h.val - 1 = E - Y * E
      rw [e1, show (1 - Y) * (1 + Y + E) - 1 = E - Y * E - Y * Y by noncomm_ring, hYY, sub_zero]
    rw [e2, sub_eq_add_neg]
    exact hE.add (hYi.mul_maxM hE).neg
  have : h = nu * (nu⁻¹ * h) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hnu) (Subgroup.mem_sup_left hk)

theorem conj_lower_mem {g : GL (Fin n) k} (hgi : IntM g.val)
    (hg : ∀ i j, ¬ (blk e i ∉ T ∧ blk e j ∈ T) → (g.val - 1) i j = 0) :
    (dia e hc (ind T))⁻¹ * g * dia e hc (ind T) ∈ KOne k (Fin n) := by
  refine mem_KOne.2 fun i j => ?_
  rw [conj'_sub_apply]
  by_cases hij : blk e i ∉ T ∧ blk e j ∈ T
  · refine deep_one_iff.1 ((deep_conj' hc1 hc2 (deep_sub_one_of_intM hgi i j)).mono ?_)
    simp [ind, hij.1, hij.2]
  · rw [hg i j hij]; simp

theorem conj_upper_intM {C : Fin s → ℕ} (hC : ∀ a ∈ T, ∀ b ∉ T, C b ≤ C a) {g : GL (Fin n) k} (hgi : IntM g.val)
    (hg : ∀ i j, ¬ (blk e i ∈ T ∧ blk e j ∉ T) → (g.val - 1) i j = 0) :
    IntM (dia e hc C * g * (dia e hc C)⁻¹).val := by
  have h1 : IntM ((dia e hc C * g * (dia e hc C)⁻¹).val - 1) := fun i j => by
    rw [conj_sub_apply]
    by_cases hij : blk e i ∈ T ∧ blk e j ∉ T
    · refine mem_int_of_deep ((deep_conj hc1 hc2 (deep_sub_one_of_intM hgi i j)).mono ?_)
      have := hC _ hij.1 _ hij.2
      omega
    · rw [hg i j hij]; simp
  have := h1.add (intM_one (k := k) (n := Fin n))
  rwa [sub_add_cancel] at this

end Conj

section Factor

theorem ring_inv {R : Type} [Ring R] {P Q g h : R} (pp : P * P = P) (qq : Q * Q = Q) (pq : P * Q = 0)
    (qp : Q * P = 0) (one : P + Q = 1) (gh : g * h = 1) (a : Q * g * P = 0) (b : Q * h * P = 0) :
    (P * g * P + Q * g * Q) * (P * h * P + Q * h * Q) = 1 := by
  have e1 : P * g * P * h * P = P := by
    have : P * g * P * h * P = P * g * (P + Q) * h * P - P * g * (Q * h * P) := by noncomm_ring
    rw [this, one, mul_one, b, mul_zero, sub_zero, mul_assoc P g h, gh, mul_one, pp]
  have e2 : Q * g * Q * h * Q = Q := by
    have : Q * g * Q * h * Q = Q * g * (P + Q) * h * Q - Q * g * P * h * Q := by noncomm_ring
    rw [this, one, mul_one, a, zero_mul, zero_mul, sub_zero, mul_assoc Q g h, gh, mul_one, qq]
  have : (P * g * P + Q * g * Q) * (P * h * P + Q * h * Q) =
      P * g * (P * P) * h * P + P * g * (P * Q) * h * Q + Q * g * (Q * P) * h * P + Q * g * (Q * Q) * h * Q := by
    noncomm_ring
  rw [this, pp, pq, qp, qq, e1, e2]
  simp [one]

theorem ring_factor {R : Type} [Ring R] {P Q g h : R} (qq : Q * Q = Q) (one : P + Q = 1) (hg : h * g = 1)
    (a : Q * g * P = 0) (b : Q * h * P = 0) :
    (P * h * P + Q * h * Q) * g = 1 - P * (h * Q * g) * Q := by
  have s1 : P * h * P * g = P - P * h * Q * g := by
    have : P * h * P * g = P * h * (P + Q) * g - P * h * Q * g := by noncomm_ring
    rw [this, one, mul_one, mul_assoc P h g, hg, mul_one]
  have s2 : Q * h * Q * g = Q := by
    have : Q * h * Q * g = Q * h * (P + Q) * g - Q * h * P * g := by noncomm_ring
    rw [this, one, mul_one, b, zero_mul, sub_zero, mul_assoc Q h g, hg, mul_one]
  have t : P * h * Q * g * P = 0 := by
    have : P * h * Q * g * P = P * h * (Q * Q) * g * P := by rw [qq]
    rw [this, show P * h * (Q * Q) * g * P = P * h * Q * (Q * g * P) by noncomm_ring, a, mul_zero]
  have s3 : P * h * Q * g = P * (h * Q * g) * Q := by
    calc P * h * Q * g = P * h * Q * g * (P + Q) := by rw [one, mul_one]
      _ = P * h * Q * g * P + P * (h * Q * g) * Q := by noncomm_ring
      _ = P * (h * Q * g) * Q := by rw [t, zero_add]
  have : (P * h * P + Q * h * Q) * g = P * h * P * g + Q * h * Q * g := by noncomm_ring
  rw [this, s1, s2, s3, ← one]
  abel

variable {n s : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin n} {T : Finset (Fin s)}

theorem sub_one_of_mem_unipRad {g : GL (Fin n) k} (hg : g ∈ unipRad k e) {i j : Fin n}
    (h : ¬ blk e i < blk e j) : (g.val - 1) i j = 0 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  rcases (not_lt.1 h).lt_or_eq with h3 | h3
  · rw [Matrix.sub_apply, mem_parab.1 h1 i j h3, one_apply_ne (fun e' => by rw [e'] at h3; exact lt_irrefl _ h3), sub_zero]
  · obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : b = a := by simpa using h3
    subst hab
    rw [Matrix.sub_apply, h2, one_apply_blk, sub_self]

theorem intM_pr : IntM (pr e T k) := fun i j => by
  simp only [pr, diagonal_apply]; split_ifs <;> simp

theorem intM_qr : IntM (qr e T k) := fun i j => by
  simp only [qr, diagonal_apply]; split_ifs <;> simp

theorem qr_mul_mul_pr_eq_zero (hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k e) : qr e T k * g.val * pr e T k = 0 := by
  ext i j
  rw [mul_pr_apply, qr_mul_apply]
  split_ifs with h1 h2
  · rfl
  · have := sub_one_of_mem_unipRad hg (i := i) (j := j) (fun h => h2 (hT _ _ h.le h1))
    rwa [Matrix.sub_apply, one_apply_ne (fun e' => by subst e'; exact h2 h1), sub_zero] at this
  · rfl

theorem exists_factor (hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T) {g : GL (Fin n) k}
    (hg : g ∈ unipRad k e ⊓ KO k (Fin n)) :
    ∃ gm gc : GL (Fin n) k, g = gm * gc ∧ gm ∈ unipRad k e ⊓ KO k (Fin n) ∧ gc ∈ KO k (Fin n) ∧
      (∀ i j, ¬ (blk e i ∈ T ↔ blk e j ∈ T) → (gm.val - 1) i j = 0) ∧
      (∀ i j, ¬ (blk e i ∈ T ∧ blk e j ∉ T) → (gc.val - 1) i j = 0) := by
  set P := pr e T k
  set Q := qr e T k
  have pp := pr_mul_pr e T (A := k)
  have qq := qr_mul_qr e T (A := k)
  have pq := pr_mul_qr e T (A := k)
  have qp := qr_mul_pr e T (A := k)
  have one := pr_add_qr e T (A := k)
  have a := qr_mul_mul_pr_eq_zero hT hg.1
  have b := qr_mul_mul_pr_eq_zero hT (inv_mem hg.1)
  have gh : g.val * (g⁻¹).val = 1 := Units.mul_inv g
  have hg' : (g⁻¹).val * g.val = 1 := Units.inv_mul g
  let gm : GL (Fin n) k := ⟨P * g.val * P + Q * g.val * Q, P * (g⁻¹).val * P + Q * (g⁻¹).val * Q,
    ring_inv pp qq pq qp one gh a b, ring_inv pp qq pq qp one hg' b a⟩
  have hgm1 : ∀ i j, ¬ (blk e i ∈ T ↔ blk e j ∈ T) → (gm.val - 1) i j = 0 := fun i j h => by
    show (P * g.val * P + Q * g.val * Q - 1) i j = 0
    rw [Matrix.sub_apply, Matrix.add_apply, mul_pr_apply, pr_mul_apply, mul_qr_apply, qr_mul_apply,
      one_apply_ne (ne_of_side e T h)]
    by_cases h1 : blk e i ∈ T <;> by_cases h2 : blk e j ∈ T <;> simp_all
  have hgmN : gm ∈ unipRad k e := mem_unipRad_of fun i j hij => by
    by_cases h : (blk e i ∈ T ↔ blk e j ∈ T)
    · have := sub_one_of_mem_unipRad hg.1 hij
      show (P * g.val * P + Q * g.val * Q - 1) i j = 0
      rw [Matrix.sub_apply] at this ⊢
      rw [Matrix.add_apply, mul_pr_apply, pr_mul_apply, mul_qr_apply, qr_mul_apply]
      by_cases h1 : blk e i ∈ T <;> by_cases h2 : blk e j ∈ T <;> simp_all
    · exact hgm1 i j h
  have hgmKO : gm ∈ KO k (Fin n) := by
    have hi := intM_of_mem_KO hg.2
    have hi' := intM_of_mem_KO (inv_mem hg.2)
    exact mem_KO.2 ⟨((intM_pr.mul hi).mul intM_pr).add ((intM_qr.mul hi).mul intM_qr),
      ((intM_pr.mul hi').mul intM_pr).add ((intM_qr.mul hi').mul intM_qr)⟩
  refine ⟨gm, gm⁻¹ * g, by group, ⟨hgmN, hgmKO⟩, mul_mem (inv_mem hgmKO) hg.2, hgm1, fun i j h => ?_⟩
  have e3 : (gm⁻¹ * g).val - 1 = -(P * ((g⁻¹).val * Q * g.val) * Q) := by
    show (P * (g⁻¹).val * P + Q * (g⁻¹).val * Q) * g.val - 1 = _
    rw [ring_factor qq one hg' a b]
    abel
  rw [e3, Matrix.neg_apply, mul_qr_apply, pr_mul_apply]
  by_cases h1 : blk e i ∈ T <;> by_cases h2 : blk e j ∈ T <;> simp_all

theorem dia_ind_val {c : k} (hc : c ≠ 0) : (dia e hc (ind T)).val = c • pr e T k + qr e T k := by
  ext i j
  simp only [dia_val, pr, qr, ind, diagonal_apply, Matrix.add_apply, Matrix.smul_apply]
  split_ifs <;> simp_all

theorem comm_dia {c : k} (hc : c ≠ 0) {g : GL (Fin n) k}
    (hg : ∀ i j, ¬ (blk e i ∈ T ↔ blk e j ∈ T) → (g.val - 1) i j = 0) :
    g * dia e hc (ind T) = dia e hc (ind T) * g := by
  obtain ⟨h1, h2⟩ := comm_pr_of_side e T hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, dia_ind_val, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    h1, h2]

end Factor

section Step

variable {n s : ℕ} {d : Fin s → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable (e : (Σ a, Fin (d a)) ≃ Fin n) (π : Representation ℂ (GL (Fin n) k) V) {c : k} (hc : c ≠ 0) in

def Claim (C : Fin s → ℕ) : Prop :=
  ∀ w ∈ fixed π (Gp e), π (dia e hc C) w ∈ twKer π (KOne k (Fin n)) 1 → w = 0

variable {e : (Σ a, Fin (d a)) ≃ Fin n} {π : Representation ℂ (GL (Fin n) k) V} {c : k} {hc : c ≠ 0}
  (hc1 : Deep 1 c) (hc2 : Deep (-1) c⁻¹)
include hc1 hc2

theorem apply_conj (g h : GL (Fin n) k) (w : V) : π g (π h w) = π h (π (h⁻¹ * g * h) w) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem step {T : Finset (Fin s)} (hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T) {C : Fin s → ℕ}
    (hC : ∀ a ∈ T, ∀ b ∉ T, C b ≤ C a) (ih : Claim e π hc C) : Claim e π hc (fun a => C a + ind T a) := by
  classical
  intro w hw hwk
  set D := dia e hc (ind T) with hD
  have hdia : dia e hc (fun a => C a + ind T a) = dia e hc C * D := dia_add e hc C (ind T)
  have hx1 : π D w ∈ fixed π (KOne k (Fin n)) := mem_fixed.2 fun g hg => by
    rw [apply_conj hc1 hc2, mem_fixed.1 hw _ (conj_KOne_mem hc1 hc2 hT hg)]
  let X : fixed π (KOne k (Fin n)) := ⟨π D w, hx1⟩
  have hX : ∀ u ∈ GlobalTheory.OppRad.U (qr e T 𝓀[k]) (pr e T 𝓀[k]), repF π u X = X := by
    intro u hu
    obtain ⟨a, rfl, ha, -⟩ := exists_lift (Z := fun i j => blk e i ∉ T ∧ blk e j ∈ T)
      (fun i l j h1 h2 => h2.1 h1.2) u ((mem_U_iff' e T u).1 hu)
    refine Subtype.ext ?_
    rw [repF_red]
    show π (incl k n a) (π D w) = π D w
    rw [apply_conj hc1 hc2, mem_fixed.1 hw _ (Subgroup.mem_sup_left (conj_lower_mem hc1 hc2 (intM_incl a) ha))]
  set W := GlobalTheory.OppRad.S (repF π) (GlobalTheory.OppRad.U (pr e T 𝓀[k]) (qr e T 𝓀[k])) X with hW
  have hW2 : π (dia e hc C) (W : V) ∈ twKer π (KOne k (Fin n)) 1 := by
    haveI := Fintype.ofFinite (GlobalTheory.OppRad.U (pr e T 𝓀[k]) (qr e T 𝓀[k]))
    rw [hW, GlobalTheory.OppRad.S_apply, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun u _ => ?_
    obtain ⟨a, hau, ha, hai⟩ := exists_lift (Z := fun i j => blk e i ∈ T ∧ blk e j ∉ T)
      (fun i l j h1 h2 => h1.2 h2.1) u.1 ((mem_U_iff e T u.1).1 u.2)
    rw [← hau, repF_red]
    have hKO : dia e hc C * incl k n a * (dia e hc C)⁻¹ ∈ KO k (Fin n) := by
      refine mem_KO.2 ⟨conj_upper_intM hc1 hc2 hC (intM_incl a) ha, ?_⟩
      have : (dia e hc C * incl k n a * (dia e hc C)⁻¹)⁻¹ = dia e hc C * incl k n a⁻¹ * (dia e hc C)⁻¹ := by
        rw [map_inv]; group
      rw [this]
      exact conj_upper_intM hc1 hc2 hC (intM_incl _) hai
    have hx : π (dia e hc C) (π D w) ∈ twKer π (KOne k (Fin n)) 1 := by
      rw [← Module.End.mul_apply, ← map_mul, ← hdia]; exact hwk
    have : π (dia e hc C) (π (incl k n a) (π D w)) =
        π (dia e hc C * incl k n a * (dia e hc C)⁻¹) (π (dia e hc C) (π D w)) := by
      have e4 : dia e hc C * incl k n a * (dia e hc C)⁻¹ * dia e hc C = dia e hc C * incl k n a := by group
      conv_rhs => rw [← Module.End.mul_apply, ← map_mul, e4, map_mul, Module.End.mul_apply]
    rw [show ((X : fixed π (KOne k (Fin n))) : V) = π D w from rfl, this]
    exact apply_mem_twKer_of_normalizer (mem_normalizer_KOne hKO) hx
  have hW1 : (W : V) ∈ fixed π (Gp e) := by
    refine mem_fixed_sup W.2 (mem_fixed.2 fun g hg => ?_)
    obtain ⟨gm, gc, rfl, hgm, hgc, hgm1, hgc1⟩ := exists_factor hT hg
    obtain ⟨b, rfl⟩ := hgm.2
    obtain ⟨a, rfl⟩ := hgc
    have hua : red k n a ∈ GlobalTheory.OppRad.U (pr e T 𝓀[k]) (qr e T 𝓀[k]) :=
      (mem_U_iff e T _).2 fun i j h => red_sub_apply (hgc1 i j h)
    obtain ⟨hp, hq⟩ := comm_pr_of_side e T (A := 𝓀[k]) (u := (red k n b).val)
      fun i j h => red_sub_apply (hgm1 i j h)
    have hbX : repF π (red k n b) X = X := by
      refine Subtype.ext ?_
      rw [repF_red]
      show π (incl k n b) (π D w) = π D w
      rw [← Module.End.mul_apply, ← map_mul, comm_dia hc hgm1, map_mul, Module.End.mul_apply,
        mem_fixed.1 hw _ (Subgroup.mem_sup_right hgm)]
    have h1 : π (incl k n a) (W : V) = W := by
      rw [← repF_red π a W, hW, GlobalTheory.OppRad.S_left hua]
    have h2 : repF π (red k n b) W = W := by
      rw [hW, GlobalTheory.OppRad.S_conj (fun u hu => GlobalTheory.OppRad.conj_mem hp hq hu)
        (fun u hu => GlobalTheory.OppRad.conj_mem (GlobalTheory.OppRad.inv_rel hp) (GlobalTheory.OppRad.inv_rel hq) hu), hbX]
    rw [map_mul, Module.End.mul_apply, h1, ← repF_red, h2]
  have hW0 : W = 0 := by
    apply Subtype.ext
    simpa using ih _ hW1 hW2
  have hX0 : X = 0 := GlobalTheory.OppRad.oppInj GlobalTheory.OppRad.matrix_regular (qr_mul_qr e T) (pr_mul_pr e T)
    (qr_mul_pr e T) (pr_mul_qr e T) X hX hW0
  have h3 : π D w = 0 := congrArg Subtype.val hX0
  have := congrArg (π D⁻¹) h3
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this

end Step

def expo (s M : ℕ) (a : Fin s) : ℕ := (M + 1) * (s - 1 - a)

theorem antitone_expo {s : ℕ} (M : ℕ) : Antitone (expo s M) := fun a b hab => by
  have : (a : ℕ) ≤ b := hab
  exact Nat.mul_le_mul_left _ (by omega)

section Walk

variable {n s : ℕ} {d : Fin s → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {e : (Σ a, Fin (d a)) ≃ Fin n} {π : Representation ℂ (GL (Fin n) k) V} {c : k} {hc : c ≠ 0}
  (hc1 : Deep 1 c) (hc2 : Deep (-1) c⁻¹)
include hc1 hc2

theorem claim_of_antitone (hπ : IsSmooth π) :
    ∀ m : ℕ, ∀ C : Fin s → ℕ, ∑ a, C a = m → Antitone C → Claim e π hc C := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro C hm hC
  classical
  by_cases h0 : ∀ a, C a = 0
  · have : C = fun _ => 0 := funext h0
    subst this
    intro w hw hwk
    rw [dia_zero, map_one, Module.End.one_apply] at hwk
    exact eq_zero_of_fixed hπ isCompact_KOne (fixed_anti le_sup_left hw) hwk
  · push_neg at h0
    obtain ⟨a0, ha0⟩ := h0
    let T : Finset (Fin s) := Finset.univ.filter fun a => 0 < C a
    have hmemT : ∀ a, a ∈ T ↔ 0 < C a := fun a => by simp [T]
    let C' : Fin s → ℕ := fun a => C a - ind T a
    have hCC : (fun a => C' a + ind T a) = C := funext fun a => by
      simp only [C', ind]
      by_cases h : a ∈ T
      · have := (hmemT a).1 h; simp only [h, if_true]; omega
      · simp [h]
    have hT : ∀ a b : Fin s, a ≤ b → b ∈ T → a ∈ T := fun a b hab hb =>
      (hmemT a).2 (lt_of_lt_of_le ((hmemT b).1 hb) (hC hab))
    have hC' : ∀ a ∈ T, ∀ b ∉ T, C' b ≤ C' a := fun a _ b hb => by
      have : C b = 0 := by by_contra h; exact hb ((hmemT b).2 (Nat.pos_of_ne_zero h))
      simp [C', ind, hb, this]
    have hanti : Antitone C' := fun a b hab => by
      have h1 := hC hab
      have hz : ∀ x, x ∉ T → C x = 0 := fun x hx => by
        by_contra h; exact hx ((hmemT x).2 (Nat.pos_of_ne_zero h))
      simp only [C', ind]
      by_cases hb : b ∈ T
      · have ha := hT a b hab hb
        simp only [ha, hb, if_true]; omega
      · have := hz b hb
        simp only [hb, if_false]; split_ifs <;> omega
    have hlt : ∑ a, C' a < m := by
      rw [← hm]
      refine Finset.sum_lt_sum (fun a _ => Nat.sub_le _ _) ⟨a0, Finset.mem_univ _, ?_⟩
      have : a0 ∈ T := (hmemT a0).2 (Nat.pos_of_ne_zero ha0)
      simp only [C', ind, this, if_true]
      omega
    rw [← hCC]
    exact step hc1 hc2 hT hC' (ih _ hlt C' rfl hanti)

theorem eventually_conj_mem {u : GL (Fin n) k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, dia e hc (expo s M) * u * (dia e hc (expo s M))⁻¹ ∈ KOne k (Fin n) := by
  have key : ∀ᶠ M : ℕ in Filter.atTop, ∀ i j, Deep (-(M : ℤ)) (u.val i j) := by
    simp only [Filter.eventually_all]
    exact fun i j => eventually_deep _
  filter_upwards [key] with M hM
  refine mem_KOne.2 fun i j => ?_
  rw [conj_sub_apply]
  by_cases h : blk e i < blk e j
  · have hij : i ≠ j := fun e' => by rw [e'] at h; exact lt_irrefl _ h
    rw [Matrix.sub_apply, one_apply_ne hij, sub_zero]
    refine deep_one_iff.1 ((deep_conj hc1 hc2 (hM i j)).mono ?_)
    have h1 : ((blk e i : Fin s) : ℕ) < ((blk e j : Fin s) : ℕ) := h
    have h2 : ((blk e j : Fin s) : ℕ) < s := (blk e j).2
    have hN : expo s M (blk e j) + (M + 1) ≤ expo s M (blk e i) := by
      simp only [expo]
      calc (M + 1) * (s - 1 - ((blk e j : Fin s) : ℕ)) + (M + 1) = (M + 1) * (s - 1 - ((blk e j : Fin s) : ℕ) + 1) := by ring
        _ ≤ (M + 1) * (s - 1 - ((blk e i : Fin s) : ℕ)) := Nat.mul_le_mul_left _ (by omega)
    have : (expo s M (blk e j) : ℤ) + M + 1 ≤ expo s M (blk e i) := by exact_mod_cast hN
    omega
  · rw [sub_one_of_mem_unipRad hu h]; simp

theorem eventually_mem_twKer {v : V} (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, π (dia e hc (expo s M)) v ∈ twKer π (KOne k (Fin n)) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_conj_mem hc1 hc2 u.2] with M hM
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    have : π (dia e hc (expo s M)) (π u w) =
        π (dia e hc (expo s M) * u * (dia e hc (expo s M))⁻¹) (π (dia e hc (expo s M)) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [this]
    exact sub_mem_twKer hM _
  | zero => simp
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h1 h2
    rw [map_add]; exact add_mem h1 h2
  | smul a x _ hx =>
    filter_upwards [hx] with M h1
    rw [map_smul]; exact Submodule.smul_mem _ a h1

end Walk

theorem depthZeroJacquetInjective : GlobalTheory.Published.DepthZeroJacquetInjective := by
  intro k _ _ _ _ n s d e π v hv h0
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  have h1 : v ∈ twKer π.π (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  exact claim_of_antitone hc1 hc2 π.smooth _ _ rfl (antitone_expo M) v hv hM

end GlobalTheory.DepthZeroJac
