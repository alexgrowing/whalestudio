import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.OneDim

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.BasePf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

abbrev Wt (e : Matrix (Fin n) (Fin n) k) : Type := {w : Fin n → k // e *ᵥ w = w}

def Gs (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) : Subgroup (GL (Fin n) k) where
  carrier := {g | g ∈ Gz Z ∧ g.val * e = e * g.val ∧ g.val * (1 - e) = 1 - e}
  mul_mem' := by
    rintro g h ⟨hg, hge, hg'⟩ ⟨hh, hhe, hh'⟩
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · simp only [Units.val_mul]; rw [← mul_assoc, hg a ha, mul_assoc, hh a ha, mul_assoc]
    · simp only [Units.val_mul]; rw [mul_assoc, hhe, ← mul_assoc, hge, mul_assoc]
    · simp only [Units.val_mul]; rw [mul_assoc, hh', hg']
  one_mem' := ⟨fun a _ => by simp, by simp, by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hge, hg'⟩
    have comm : ∀ a, a * g.val = g.val * a → a * g⁻¹.val = g⁻¹.val * a := fun a h1 =>
      calc a * g⁻¹.val = g⁻¹.val * (g.val * a) * g⁻¹.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = g⁻¹.val * (a * g.val) * g⁻¹.val := by rw [h1]
        _ = g⁻¹.val * a := by rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨fun a ha => comm a (hg a ha), (comm e hge.symm).symm, ?_⟩
    calc g⁻¹.val * (1 - e) = g⁻¹.val * (g.val * (1 - e)) := by rw [hg']
      _ = 1 - e := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem Gs_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {e : Matrix (Fin n) (Fin n) k} (g : Gs Z e) :
    (g : GL (Fin n) k) ∈ Gz Z ∧ (g : GL (Fin n) k).val * e = e * (g : GL (Fin n) k).val ∧
      (g : GL (Fin n) k).val * (1 - e) = 1 - e := g.2

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    MulAction (Gs Z e) (Wt e) where
  smul g w := ⟨(g : GL (Fin n) k).val *ᵥ w.1, by rw [mulVec_mulVec, ← (Gs_mem g).2.1, ← mulVec_mulVec, w.2]⟩
  one_smul w := Subtype.ext (by
    show ((1 : Gs Z e) : GL (Fin n) k).val *ᵥ w.1 = w.1
    simp)
  mul_smul g h w := Subtype.ext (by
    show ((g * h : Gs Z e) : GL (Fin n) k).val *ᵥ w.1 = (g : GL (Fin n) k).val *ᵥ ((h : GL (Fin n) k).val *ᵥ w.1)
    simp [mulVec_mulVec])

theorem smul_val (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (g : Gs Z e)
    (w : Wt e) : (g • w).1 = (g : GL (Fin n) k).val *ᵥ w.1 := rfl

theorem Gs_comm (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (h0 : dB0 Z = 0)
    (e : Matrix (Fin n) (Fin n) k) (g h : Gs Z e) : g * h = h * g := by
  have hsub : Z ≤ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := fun a ha =>
    (Subalgebra.mem_centralizer_iff k).mpr (fun b hb => hZ.1 b hb a ha)
  have hle : Module.finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) ≤
      Module.finrank k Z := by
    have h0' := h0
    unfold dB0 at h0'
    omega
  have heq : Subalgebra.toSubmodule Z =
      Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
    Submodule.eq_of_le_of_finrank_le hsub hle
  have hmem : ∀ x : Gs Z e, ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Z := by
    intro x
    have hc : ((x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
        Subalgebra.toSubmodule (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) :=
      (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => (Gs_mem x).1 a ha)
    rw [← heq] at hc
    exact hc
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact hZ.1 _ (hmem g) _ (hmem h)

def sm (γ : (ValueGroupWithZero k)ˣ) (A : Matrix (Fin n) (Fin n) k) : Prop :=
  ∀ i j, valuation k (A i j) < γ ∧ valuation k (A i j) < 1

theorem ent_lt (c : ValueGroupWithZero k) (hc : c ≠ 0) (a b : Matrix (Fin n) (Fin n) k)
    (ha : ∀ i j, valuation k (a i j) < c) (hb : ∀ i j, valuation k (b i j) < c)
    (hb1 : ∀ i j, valuation k (b i j) ≤ 1) (i j : Fin n) : valuation k ((a * b + a + b) i j) < c := by
  simp only [Matrix.add_apply, Matrix.mul_apply]
  refine (valuation k).map_add_lt ((valuation k).map_add_lt ?_ (ha i j)) (hb i j)
  refine (valuation k).map_sum_lt hc (fun l _ => ?_)
  rw [map_mul]
  calc valuation k (a i l) * valuation k (b l j) ≤ valuation k (a i l) * 1 := by
        gcongr
        exact hb1 l j
    _ = valuation k (a i l) := mul_one _
    _ < c := ha i l

theorem sm_mul (γ : (ValueGroupWithZero k)ˣ) (A B : Matrix (Fin n) (Fin n) k) (hA : sm γ (A - 1))
    (hB : sm γ (B - 1)) : sm γ (A * B - 1) := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  unfold sm at *
  intro i j
  rw [e]
  exact ⟨ent_lt _ γ.ne_zero _ _ (fun i j => (hA i j).1) (fun i j => (hB i j).1) (fun i j => (hB i j).2.le) i j,
    ent_lt _ one_ne_zero _ _ (fun i j => (hA i j).2) (fun i j => (hB i j).2) (fun i j => (hB i j).2.le) i j⟩

theorem sm_zero (γ : (ValueGroupWithZero k)ˣ) : sm γ (0 : Matrix (Fin n) (Fin n) k) := by
  intro i j
  simp only [Matrix.zero_apply, map_zero]
  exact ⟨zero_lt_iff.mpr γ.ne_zero, zero_lt_one⟩

def Ks (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) (γ : (ValueGroupWithZero k)ˣ) :
    Subgroup (Gs Z e) where
  carrier := {g | sm γ ((g : GL (Fin n) k).val - 1) ∧ sm γ ((g : GL (Fin n) k)⁻¹.val - 1)}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul]
      exact sm_mul γ _ _ hg hh
    · simp only [Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
      exact sm_mul γ _ _ hh' hg'
  one_mem' := ⟨by simpa using sm_zero γ, by simpa using sm_zero γ⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨?_, ?_⟩
    · simpa using hg'
    · simpa using hg

theorem int_of_sm {γ : (ValueGroupWithZero k)ˣ} {A : Matrix (Fin n) (Fin n) k} (hA : sm γ (A - 1)) (i j : Fin n) :
    valuation k (A i j) ≤ 1 := by
  have h1 : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) k) i j := by simp
  rw [h1]
  refine ((valuation k).map_add _ _).trans (max_le (hA i j).2.le ?_)
  rw [Matrix.one_apply]
  split_ifs <;> simp

end PositivityTheory.RgUd.T.Nil.BasePf
