import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Matrix
open scoped Classical

namespace GlobalTheory.GLm.MirStep

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def Em (h : Mt g m) (v : Fin m → ZMod g) : Mt g (m + 1) := Matrix.of fun i j =>
  Fin.lastCases (motive := fun _ => ZMod g) (Fin.lastCases (motive := fun _ => ZMod g) 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => ZMod g) (v i') (h i') j) i

@[simp] theorem Em_cc (h : Mt g m) (v) (i j : Fin m) : Em h v i.castSucc j.castSucc = h i j := by simp [Em]
@[simp] theorem Em_cl (h : Mt g m) (v) (i : Fin m) : Em h v i.castSucc (Fin.last m) = v i := by simp [Em]
@[simp] theorem Em_lc (h : Mt g m) (v) (j : Fin m) : Em h v (Fin.last m) j.castSucc = 0 := by simp [Em]
@[simp] theorem Em_ll (h : Mt g m) (v) : Em h v (Fin.last m) (Fin.last m) = 1 := by simp [Em]

theorem Em_mul (h k : Mt g m) (v w) : Em h v * Em k w = Em (h * k) (h *ᵥ w + v) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

theorem Em_one : Em (1 : Mt g m) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem tl_apply (M : Mt g (m + 1)) (i j : Fin m) : tl m M i j = M i.castSucc j.castSucc := by
  have hi := i.2
  have hj := j.2
  simp only [tl, entN]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

@[simp] theorem tl_Em (h : Mt g m) (v) : tl m (Em h v) = h := by
  ext i j
  simp [tl_apply]

theorem inMir_iff_row {n : ℕ} (l : Fin n) (hl : (l : ℕ) + 1 = n) (M : Mt g n) :
    InMir M ↔ Pi.single l 1 ᵥ* M = Pi.single l 1 := by
  rw [Matrix.single_one_vecMul]
  constructor
  · intro h
    ext j
    rw [Matrix.row_apply, h l j hl, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]
  · intro h i j hi
    have : i = l := Fin.ext (by omega)
    subst this
    have := congrFun h j
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]

theorem inMir_Em (h : Mt g m) (v) : InMir (Em h v) := by
  intro i j hi
  have : i = Fin.last m := Fin.ext (by simp; omega)
  subst this
  induction j using Fin.lastCases <;> simp [Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

theorem eq_Em {M : Mt g (m + 1)} (hM : InMir M) : M = Em (tl m M) fun i => M i.castSucc (Fin.last m) := by
  ext i j
  induction i using Fin.lastCases
  · rw [hM _ j (by simp), inMir_Em _ _ _ j (by simp)]
  · induction j using Fin.lastCases <;> simp [tl_apply]

def E (h : Gn g m) (v : Fin m → ZMod g) : Gn g (m + 1) where
  val := Em (h : Mt g m) v
  inv := Em ((h⁻¹ : Gn g m) : Mt g m) (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v))
  val_inv := by
    rw [Em_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Units.mul_inv]
    simp [Em_one]
  inv_val := by
    rw [Em_mul, Units.inv_mul]
    simp [Em_one]

@[simp] theorem E_coe (h : Gn g m) (v) : ((E h v : Gn g (m + 1)) : Mt g (m + 1)) = Em (h : Mt g m) v := rfl

theorem E_mul (h k : Gn g m) (v w) : E h v * E k w = E (h * k) ((h : Mt g m) *ᵥ w + v) := by
  ext1
  simp [Em_mul]

theorem E_inv (h : Gn g m) (v) : (E h v)⁻¹ = E h⁻¹ (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v)) := by
  ext1
  rfl

theorem E_conj (h k : Gn g m) (v w) : (E k w)⁻¹ * E h v * E k w =
    E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) := by
  rw [E_inv, E_mul, E_mul]
  congr 1
  rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Units.val_mul]
  abel

theorem exists_E {x : Gn g (m + 1)} (hx : InMir (x : Mt g (m + 1))) : ∃ h v, x = E h v := by
  have hx' : InMir ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [inMir_iff_row (Fin.last m) (by simp)] at hx ⊢
    conv_lhs => rw [← hx]
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have h1 : tl m (x : Mt g (m + 1)) * tl m ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) = 1 := by
    have := x.mul_inv
    rw [eq_Em hx, eq_Em hx', Em_mul, ← Em_one] at this
    simpa using congrArg (tl m) this
  have hu : IsUnit (tl m (x : Mt g (m + 1))) := IsUnit.of_mul_eq_one _ h1
  refine ⟨hu.unit, fun i => (x : Mt g (m + 1)) i.castSucc (Fin.last m), ?_⟩
  ext1
  rw [E_coe, hu.unit_spec]
  exact eq_Em hx

theorem sum_mir (Φ : Gn g (m + 1) → ℂ) (hΦ : ∀ y : Gn g (m + 1), ¬ InMir (y : Mt g (m + 1)) → Φ y = 0) :
    ∑ y, Φ y = ∑ h : Gn g m, ∑ v, Φ (E h v) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_of_injOn (fun p : Gn g m × (Fin m → ZMod g) => E p.1 p.2) ?_ (fun _ _ => by simp) ?_
    (fun _ _ => rfl)
  · rintro ⟨h, v⟩ - ⟨k, w⟩ - hh
    have h0 : Em (h : Mt g m) v = Em (k : Mt g m) w := congrArg Units.val hh
    refine Prod.ext (Units.ext ?_) ?_
    · simpa using congrArg (tl m) h0
    · ext i
      simpa using congrFun (congrFun h0 i.castSucc) (Fin.last m)
  · intro y _ hy
    apply hΦ
    intro hy'
    obtain ⟨h, v, rfl⟩ := exists_E hy'
    exact hy ⟨(h, v), by simp, rfl⟩

theorem toG_coe {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  simp [toG]

theorem uni_iff {b : ℕ} (hb : b = 1) (M : Mt g b) : IsUniUp M ↔ M = 1 := by
  subst hb
  constructor
  · intro h
    ext i j
    rw [(h i j).2 (Subsingleton.elim _ _), Matrix.one_apply, if_pos (Subsingleton.elim _ _)]
  · rintro rfl a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp

theorem wh_one (ψ : AddChar (ZMod g) ℂ) {b : ℕ} (hb : b = 1) (χ : Gn g b → ℂ) : wh ψ χ = χ 1 := by
  have hf : (Finset.univ.filter fun u : Gn g b => IsUniUp (u : Mt g b)) = {1} := by
    ext u
    simp [uni_iff hb]
  subst hb
  simp only [wh, tr, eU, eDat]
  have hf' : ∀ inst : DecidablePred fun u : Gn g 1 => IsUniUp (u : Mt g 1), @Finset.filter _ (fun u : Gn g 1 => IsUniUp (u : Mt g 1)) inst Finset.univ = {1} := by
    intro inst
    convert hf
  rw [hf']
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem inR_iff (M : Mt g (m + 1)) : InR m M ↔ InMir M := by
  rw [InR, uni_iff (by omega)]
  have hb : br m (m + 1 - m) M = 1 ↔ M (Fin.last m) (Fin.last m) = 1 := by
    have : ∀ i j : Fin (m + 1 - m), br m (m + 1 - m) M i j = M (Fin.last m) (Fin.last m) := by
      intro i j
      have hi := i.2
      have hj := j.2
      simp only [br, entN]
      rw [dif_pos ⟨by omega, by omega⟩]
      congr 1 <;> exact Fin.ext (by simp; omega)
    constructor
    · intro h
      rw [← this ⟨0, by omega⟩ ⟨0, by omega⟩, h, Matrix.one_apply_eq]
    · intro h
      ext i j
      have hi := i.2
      have hj := j.2
      rw [this, h, Matrix.one_apply, if_pos (Fin.ext (by omega))]
  rw [hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hi
    have : i = Fin.last m := Fin.ext (by simp; omega)
    subst this
    induction j using Fin.lastCases with
    | last => simpa using h2
    | cast j => rw [h1 _ _ (by simp) (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last _).symm]
  · intro h
    refine ⟨fun i j hj hi => ?_, by rw [h _ _ (by simp), Matrix.one_apply_eq]⟩
    have := i.2
    rw [h i j (by omega), Matrix.one_apply_ne (by intro e; subst e; omega)]

theorem exists_row (l : Fin m) (r : Fin m → ZMod g) (hr : r ≠ 0) :
    ∃ k : Gn g m, Pi.single l 1 ᵥ* (k : Mt g m) = r := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  have hd : (((1 : Mt g m).updateRow i r).submatrix (Equiv.swap i l) id).det ≠ 0 := by
    rw [Matrix.det_permute, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i l)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
  rw [Matrix.single_one_vecMul]
  ext j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.row_apply]

theorem exists_psi_ne {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {u : Fin m → ZMod g} (hu : u ≠ 0) :
    ∃ r, ψ (u ⬝ᵥ r) ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ
  refine ⟨Pi.single i (a / u i), ?_⟩
  rwa [dotProduct_single, mul_div_cancel₀ _ hi]

theorem psi_ne_zero (ψ : AddChar (ZMod g) ℂ) (a : ZMod g) : ψ a ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul a (-a)
  simp [h] at this

theorem q_ne_zero : ((g : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)

theorem orth {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (u : Fin m → ZMod g) :
    ∑ r, ψ (r ⬝ᵥ u) = if u = 0 then (g : ℂ) ^ m else 0 := by
  split_ifs with hu
  · subst hu
    simp [ZMod.card]
  · obtain ⟨r₀, h₀⟩ := exists_psi_ne hψ hu
    have h1 : ∑ r, ψ (r ⬝ᵥ u) = (∑ r, ψ (r ⬝ᵥ u)) * ψ (u ⬝ᵥ r₀) := by
      rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight r₀)]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [Equiv.coe_addRight]
      rw [add_dotProduct, ψ.map_add_eq_mul, dotProduct_comm r₀]
    have h2 : (∑ r, ψ (r ⬝ᵥ u)) * (1 - ψ (u ⬝ᵥ r₀)) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h₀.symm)

def fc (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (r : Fin m → ZMod g) : ℂ :=
  ((g : ℂ) ^ m)⁻¹ * ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹

theorem inversion {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (v) :
    ∑ r, fc ψ F h r * ψ (r ⬝ᵥ v) = F (E h v) := by
  have : ∀ r, fc ψ F h r * ψ (r ⬝ᵥ v) = ((g : ℂ) ^ m)⁻¹ * ∑ u, F (E h u) * ψ (r ⬝ᵥ (v - u)) := by
    intro r
    rw [fc, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [dotProduct_sub, AddChar.map_sub_eq_div]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth hψ, sub_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have := q_ne_zero (g := g) (m := m)
  field_simp

theorem F_conj {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (v w) :
    F (E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w))) = F (E h v) := by
  rw [← E_conj]
  have := hF (E k w)⁻¹ (E h v) (by rw [E_inv]; exact inMir_Em _ _) (inMir_Em _ _)
  rwa [inv_inv] at this

theorem fc_conj (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (r) :
    fc ψ F (k⁻¹ * h * k) r = fc ψ F h (r ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) := by
  unfold fc
  congr 1
  symm
  refine Fintype.sum_bijective (fun v => ((k⁻¹ : Gn g m) : Mt g m) *ᵥ v) ?_ _ _ fun v => ?_
  · refine Finite.injective_iff_bijective.1 fun a b hab => ?_
    have := congrArg (fun v => (k : Mt g m) *ᵥ v) hab
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this
  · rw [← F_conj hF h k v 0, dotProduct_mulVec]
    simp

theorem fc_eq_zero {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F)
    (h : Gn g m) (r) (hr : r ᵥ* (h : Mt g m) ≠ r) : fc ψ F h r = 0 := by
  obtain ⟨w, hw⟩ := exists_psi_ne hψ (sub_ne_zero.2 hr)
  have h1 : ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹ =
      (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹ := by
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight ((h : Mt g m) *ᵥ w - w))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := F_conj hF h 1 v w
    simp only [inv_one, one_mul, mul_one, Units.val_one, Matrix.one_mulVec] at this
    simp only [Equiv.coe_addRight]
    rw [show v + ((h : Mt g m) *ᵥ w - w) = (h : Mt g m) *ᵥ w + v - w by abel, this,
      show (h : Mt g m) *ᵥ w + v - w = v + ((h : Mt g m) *ᵥ w - w) by abel, dotProduct_add, ψ.map_add_eq_mul,
      dotProduct_sub, dotProduct_mulVec, sub_dotProduct]
    ring
  have h2 : (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (1 - (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹) = 0 := by
    linear_combination h1
  rw [fc, (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (by simpa [eq_comm] using hw)), mul_zero]

theorem sum_fib (Φ : Gn g (m + 1) → ℂ) (h : Gn g m) :
    (∑ x : Gn g (m + 1), if InR m (x : Mt g (m + 1)) ∧ tl m (x : Mt g (m + 1)) = (h : Mt g m) then Φ x else 0) =
      ∑ v, Φ (E h v) := by
  rw [sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh.1)]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, Units.val_inj]
  rw [Finset.sum_comm]
  simp

theorem der_eq (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) : der ψ m F h = fc ψ F h 0 := by
  rw [der, wh_one ψ (by omega), res, fc]
  have e : m * (m + 1 - m) = m := by simp
  rw [e]
  congr 1
  simp only [zero_dotProduct, AddChar.map_zero_eq_one, inv_one, mul_one]
  rw [← sum_fib]
  refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
  rw [InR, uni_iff (by omega), Units.val_one]
  tauto

theorem entN_Em (l : Fin m) (hl : (l : ℕ) + 1 = m) (h : Mt g m) (v) :
    entN (Em h v) (m - 1) m = Pi.single l 1 ⬝ᵥ v := by
  rw [single_dotProduct, one_mul, ← Em_cl h v l, entN, dif_pos ⟨by omega, by omega⟩]
  congr 1
  exact Fin.ext (by simp; omega)

theorem tail_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) :
    tail ψ m F h = fc ψ F h (Pi.single l 1) := by
  rw [tail, fc, sum_fib (fun x => F x * (ψ (supFrom (m - 1) (x : Mt g (m + 1))))⁻¹)]
  have e : m * (m + 1 - m) + (m + 1 - m) * (m + 1 - m - 1) / 2 = m := by simp
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← entN_Em l hl (h : Mt g m) v, supFrom]
  have : Finset.Ico (m - 1) (m + 1 - 1) = {m - 1} := by
    ext j
    simp
    omega
  rw [this, Finset.sum_singleton, show m - 1 + 1 = m by omega, E_coe]

theorem indR_eq (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indR ψ m (m + 1) (der ψ m F) (E h v) = fc ψ F h 0 := by
  unfold indR
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh),
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, if_true, toG_coe, der_eq, fc_conj ψ hF,
    supFrom, Nat.add_sub_cancel, Finset.Ico_self, Finset.sum_empty, AddChar.map_zero_eq_one, mul_one,
    Matrix.zero_vecMul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Gn g m) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem sum_rows (l : Fin m) (hl : (l : ℕ) + 1 = m) (φ : (Fin m → ZMod g) → ℂ) :
    ∑ k : Gn g m, φ (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) =
      (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) * ∑ r, if r = 0 then 0 else φ r := by
  refine (Equiv.sum_comp (Equiv.inv (Gn g m)) fun k : Gn g m => φ (Pi.single l 1 ᵥ* (k : Mt g m))).trans ?_
  rw [Finset.mul_sum,
    ← Finset.sum_fiberwise Finset.univ fun k : Gn g m => Pi.single l 1 ᵥ* (k : Mt g m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with hr
  · subst hr
    rw [mul_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) (Finset.mem_filter.1 hk).2
    simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    simpa using congrFun this l
  · obtain ⟨k₀, rfl⟩ := exists_row l r hr
    rw [Finset.sum_filter, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight k₀)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Pi.single l 1 ᵥ* ((k * k₀ : Gn g m) : Mt g m) = Pi.single l 1 ᵥ* (k₀ : Mt g m) ↔ InMir (k : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, ← Matrix.vecMul_vecMul]
      refine ⟨fun e => ?_, fun e => by rw [e]⟩
      have := congrArg (fun v => v ᵥ* ((k₀⁻¹ : Gn g m) : Mt g m)) e
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, mul_assoc, mul_one] using this
    by_cases hk : InMir (k : Mt g m)
    · refine (if_pos (this.2 hk)).trans ?_
      rw [if_pos hk, one_mul]
      exact congrArg φ (this.2 hk)
    · refine (if_neg (fun e => hk (this.1 e))).trans ?_
      rw [if_neg hk, zero_mul]

theorem indV_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1)
    {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indV ψ m (tail ψ m F) (E h v) = ∑ r, if r = 0 then 0 else fc ψ F h r * ψ (r ⬝ᵥ v) := by
  unfold indV
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy hh.1,
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inMir_Em, tl_Em, true_and, toG_coe, tail_eq l hl, fc_conj ψ hF, entN_Em l hl]
  have key : ∀ (k : Gn g m) (w : Fin m → ZMod g),
      (if InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) then fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ (Pi.single l 1 ⬝ᵥ ((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) else 0) =
      fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ ((Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ⬝ᵥ v) := by
    intro k w
    have hiff : InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) ↔
        (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ᵥ* (h : Mt g m) =
          Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, Units.val_mul]
      constructor
      · intro e
        have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.mul_inv, mul_assoc, mul_one] using this
      · intro e
        have := congrArg (fun v => v ᵥ* (k : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one] using this
    split_ifs with hk
    · rw [dotProduct_mulVec, dotProduct_sub, dotProduct_add, dotProduct_mulVec, hiff.1 hk, add_sub_cancel_left]
    · rw [fc_eq_zero hψ hF h _ (fun e => hk (hiff.2 e)), zero_mul]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_rows l hl fun r => fc ψ F h r * ψ (r ⬝ᵥ v)]
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 : (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) ≠ 0 := by
    rw [← Finset.natCast_card_filter, Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp [inMir_one]⟩
  field_simp

theorem mir_step : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ),
    1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) →
      F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  intro g _ ψ hψ m F hm hF p hp
  obtain ⟨h, v, rfl⟩ := exists_E hp
  rw [indR_eq ψ hF, indV_eq ⟨m - 1, by omega⟩ (by simp; omega) hψ hF, ← inversion hψ F h v]
  have : fc ψ F h 0 = ∑ r, if r = 0 then fc ψ F h r * ψ (r ⬝ᵥ v) else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

end GlobalTheory.GLm.MirStep
