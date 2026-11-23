import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.OpenSlice

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GroundTheory.Automorphic ValuativeRel

namespace PositivityTheory.RgUd.T.Desc.SLT.Bi

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev pi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : k :=
  (GLnLocal.uniformizer k : k)

def Lat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) k) where
  carrier := {x | x ∈ Bz Z ∧ ∀ i j, valuation k (x i j) ≤ valuation k (pi k) ^ m}
  zero_mem' := ⟨fun a _ => by simp, fun i j => by simp⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun a ha => ?_, fun i j => ?_⟩
    · rw [mul_add, add_mul, hx1 a ha, hy1 a ha]
    · rw [Matrix.add_apply]
      exact Valuation.map_add_le _ (hx2 i j) (hy2 i j)
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun a ha => ?_, fun i j => ?_⟩
    · rw [mul_neg, neg_mul, hx1 a ha]
    · rw [Matrix.neg_apply, Valuation.map_neg]
      exact hx2 i j

theorem mem_Lat {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {m : ℕ} {x : Matrix (Fin n) (Fin n) k} :
    x ∈ Lat Z m ↔ x ∈ Bz Z ∧ ∀ i j, valuation k (x i j) ≤ valuation k (pi k) ^ m := Iff.rfl

def smulA (c : k) : Matrix (Fin n) (Fin n) k →+ Matrix (Fin n) (Fin n) k := DistribSMul.toAddMonoidHom _ c

def conjA (g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k →+ Matrix (Fin n) (Fin n) k where
  toFun x := g.val * x * g⁻¹.val
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

@[simp] theorem smulA_apply (c : k) (x : Matrix (Fin n) (Fin n) k) : smulA c x = c • x := rfl
@[simp] theorem conjA_apply (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : conjA g x = g.val * x * g⁻¹.val := rfl

theorem valuation_pi_ne_zero : valuation k (pi k) ≠ 0 := GLnLocal.valuation_uniformizer_ne_zero k

theorem Lat_anti (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m m' : ℕ} (h : m ≤ m') : Lat Z m' ≤ Lat Z m :=
  fun _ hx => ⟨hx.1, fun i j => (hx.2 i j).trans
    (pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le h)⟩

theorem exists_scale (c : k) : ∃ N : ℕ, valuation k (pi k) ^ N * valuation k c ≤ 1 := by
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  have hv : valuation k c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  obtain ⟨N, hN⟩ := exists_pow_lt₀ (GLnLocal.valuation_uniformizer_lt_one k) (Units.mk0 _ (inv_ne_zero hv))
  refine ⟨N, ?_⟩
  have h1 : valuation k (pi k) ^ N ≤ (valuation k c)⁻¹ := by simpa using hN.le
  calc valuation k (pi k) ^ N * valuation k c ≤ (valuation k c)⁻¹ * valuation k c := mul_le_mul' h1 le_rfl
    _ = 1 := inv_mul_cancel₀ hv

theorem val_mul_le {A B : Matrix (Fin n) (Fin n) k} {α β : ValueGroupWithZero k}
    (hA : ∀ i j, valuation k (A i j) ≤ α) (hB : ∀ i j, valuation k (B i j) ≤ β) (i j : Fin n) :
    valuation k ((A * B) i j) ≤ α * β := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul]
  exact mul_le_mul' (hA i l) (hB l j)

theorem mul_mem_Lat {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {h x : Matrix (Fin n) (Fin n) k}
    (hh : h ∈ Lat Z 0) {m : ℕ} (hx : x ∈ Lat Z m) : h * x ∈ Lat Z m := by
  refine ⟨fun a ha => ?_, fun i j => ?_⟩
  · rw [← mul_assoc, hh.1 a ha, mul_assoc, hx.1 a ha, mul_assoc]
  · simpa using val_mul_le hh.2 hx.2 i j

private theorem exists_mat_scale (A : Matrix (Fin n) (Fin n) k) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ i j, valuation k (pi k) ^ a * valuation k (A i j) ≤ 1 := by
  choose N hN using fun p : Fin n × Fin n => exists_scale (A p.1 p.2)
  refine ⟨Finset.univ.sup N + 1, by omega, fun i j => ?_⟩
  have hle : N (i, j) ≤ Finset.univ.sup N + 1 :=
    (Finset.le_sup (f := N) (Finset.mem_univ (i, j))).trans (Nat.le_succ _)
  calc valuation k (pi k) ^ (Finset.univ.sup N + 1) * valuation k (A i j)
      ≤ valuation k (pi k) ^ N (i, j) * valuation k (A i j) :=
        mul_le_mul' (pow_le_pow_right_of_le_one' (GLnLocal.valuation_uniformizer_lt_one k).le hle) le_rfl
    _ ≤ 1 := hN (i, j)

private theorem le_inv_of_scale {a : ℕ} {y : ValueGroupWithZero k}
    (h : valuation k (pi k) ^ a * y ≤ 1) : y ≤ (valuation k (pi k) ^ a)⁻¹ := by
  have hp : valuation k (pi k) ^ a ≠ 0 := pow_ne_zero _ valuation_pi_ne_zero
  calc y = (valuation k (pi k) ^ a)⁻¹ * (valuation k (pi k) ^ a * y) := by
        rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    _ ≤ (valuation k (pi k) ^ a)⁻¹ * 1 := mul_le_mul' le_rfl h
    _ = _ := mul_one _

private theorem conj_mem_Bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {u : GL (Fin n) k} (hu : u ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : conjA u x ∈ Bz Z := by
  intro a ha
  have h1 := hu a ha
  have h2 : a * u⁻¹.val = u⁻¹.val * a := (GzS Z).inv_mem (x := u) hu a ha
  have h3 := hx a ha
  simp only [conjA_apply]
  calc a * (u.val * x * u⁻¹.val) = (a * u.val) * x * u⁻¹.val := by simp only [mul_assoc]
    _ = u.val * (a * x) * u⁻¹.val := by rw [h1]; simp only [mul_assoc]
    _ = u.val * x * (a * u⁻¹.val) := by rw [h3]; simp only [mul_assoc]
    _ = u.val * x * u⁻¹.val * a := by rw [h2]; simp only [mul_assoc]

private theorem conj_val_le (u : GL (Fin n) k) {a b t : ℕ}
    (hu : ∀ i j, valuation k (pi k) ^ a * valuation k (u i j) ≤ 1)
    (hu' : ∀ i j, valuation k (pi k) ^ b * valuation k ((u⁻¹ : GL (Fin n) k) i j) ≤ 1)
    {x : Matrix (Fin n) (Fin n) k} (hx : ∀ i j, valuation k (x i j) ≤ valuation k (pi k) ^ (t + (a + b)))
    (i l : Fin n) : valuation k ((conjA u x) i l) ≤ valuation k (pi k) ^ t := by
  have hpa : valuation k (pi k) ^ a ≠ 0 := pow_ne_zero _ valuation_pi_ne_zero
  have hpb : valuation k (pi k) ^ b ≠ 0 := pow_ne_zero _ valuation_pi_ne_zero
  have h1 := val_mul_le (A := u.val) (fun i j => le_inv_of_scale (hu i j)) hx
  have h2 := val_mul_le h1 (fun i j => le_inv_of_scale (hu' i j)) i l
  refine h2.trans (le_of_eq ?_)
  rw [pow_add, pow_add]
  calc (valuation k (pi k) ^ a)⁻¹ * (valuation k (pi k) ^ t * (valuation k (pi k) ^ a * valuation k (pi k) ^ b)) *
        (valuation k (pi k) ^ b)⁻¹
      = valuation k (pi k) ^ t * ((valuation k (pi k) ^ a)⁻¹ * valuation k (pi k) ^ a) *
        (valuation k (pi k) ^ b * (valuation k (pi k) ^ b)⁻¹) := by ac_rfl
    _ = valuation k (pi k) ^ t := by rw [inv_mul_cancel₀ hpa, mul_inv_cancel₀ hpb, mul_one, mul_one]

theorem exists_shift (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ j : ℕ, ∀ x ∈ Lat Z (j + c), conjA g x ∈ Lat Z j ∧ conjA g⁻¹ x ∈ Lat Z j := by
  obtain ⟨a, ha1, ha⟩ := exists_mat_scale (g.val)
  obtain ⟨b, -, hb⟩ := exists_mat_scale ((g⁻¹ : GL (Fin n) k).val)
  have hg' : g⁻¹ ∈ Gz Z := (GzS Z).inv_mem (x := g) hg
  refine ⟨a + b, by omega, fun t x hx => ⟨⟨conj_mem_Bz hg hx.1, ?_⟩, ⟨conj_mem_Bz hg' hx.1, ?_⟩⟩⟩
  · exact conj_val_le g ha hb hx.2
  · refine conj_val_le (a := b) (b := a) g⁻¹ hb (by simpa using ha) (fun i l => ?_)
    rw [add_comm b a]; exact hx.2 i l

theorem Lat_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m r : ℕ) :
    Lat Z (m + r) = (Lat Z r).map (smulA (pi k ^ m)) := by
  have hc : pi k ^ m ≠ 0 := pow_ne_zero _ (by
    intro h; exact valuation_pi_ne_zero (k := k) (by rw [h, map_zero]))
  have hvc : valuation k (pi k ^ m) ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  ext x
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨(pi k ^ m)⁻¹ • x, ⟨fun a ha => ?_, fun i j => ?_⟩, ?_⟩
    · rw [Matrix.mul_smul, Matrix.smul_mul, hx1 a ha]
    · rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_inv₀]
      calc (valuation k (pi k ^ m))⁻¹ * valuation k (x i j)
          ≤ (valuation k (pi k ^ m))⁻¹ * valuation k (pi k) ^ (m + r) := mul_le_mul' le_rfl (hx2 i j)
        _ = valuation k (pi k) ^ r := by
          rw [map_pow, pow_add, ← mul_assoc, inv_mul_cancel₀ (by simpa using hvc), one_mul]
    · rw [smulA_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    refine ⟨fun a ha => ?_, fun i j => ?_⟩
    · rw [smulA_apply, Matrix.mul_smul, Matrix.smul_mul, hy1 a ha]
    · rw [smulA_apply, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul, map_pow, pow_add]
      exact mul_le_mul' le_rfl (hy2 i j)

theorem smulA_injective {c : k} (hc : c ≠ 0) : Function.Injective (smulA (n := n) c) :=
  fun _ _ h => smul_right_injective _ hc h

theorem conjA_inv_conjA (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : conjA g⁻¹ (conjA g x) = x := by
  simp [mul_assoc]

theorem conjA_injective (g : GL (Fin n) k) : Function.Injective (conjA g) := fun x y h => by
  rw [← conjA_inv_conjA g x, h, conjA_inv_conjA]

theorem conjA_smulA (g : GL (Fin n) k) (c : k) (x : Matrix (Fin n) (Fin n) k) :
    conjA g (smulA c x) = smulA c (conjA g x) := by
  simp

end PositivityTheory.RgUd.T.Desc.SLT.Bi
