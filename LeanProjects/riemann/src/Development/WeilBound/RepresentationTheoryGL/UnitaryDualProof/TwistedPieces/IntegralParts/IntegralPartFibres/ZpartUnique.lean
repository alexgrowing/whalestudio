import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.Zpart
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CompactPowers.ExistsPowSmulMemOfIsCompact

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem zpart_spec {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ CC Z) :
    zpart Z x ∈ Z ∧ IsNilpotent (x - zpart Z x) := by
  have h : ∃ c ∈ Z, IsNilpotent (x - c) := hx.1
  unfold zpart
  rw [dif_pos h]
  exact h.choose_spec

theorem Z_sub_Bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) : (Z : Set (Matrix (Fin n) (Fin n) k)) ⊆ Bz Z :=
  fun c hc a ha => hZ.1 a ha c hc

theorem zpart_unique {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {x c : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hc : c ∈ Z) (hn : IsNilpotent (x - c)) : zpart Z x = c := by
  have hxc : x ∈ CC Z := ⟨⟨c, hc, hn⟩, hx⟩
  obtain ⟨h0, hn0⟩ := zpart_spec hxc
  set c0 := zpart Z x
  have hcomm : Commute (x - c) (x - c0) := by
    have h1 : Commute x c := (hx c hc).symm
    have h2 : Commute x c0 := (hx c0 h0).symm
    have h3 : Commute c c0 := hZ.1 c hc c0 h0
    exact ((Commute.refl x).sub_right h2).sub_left (h1.symm.sub_right h3)
  have hd : IsNilpotent (c0 - c) := by
    have := hcomm.isNilpotent_sub hn hn0
    simpa [sub_sub_sub_cancel_left] using this
  have := PositivityTheory.RgUd.T.Nil.Orb.Ozn.eq_zero_of_mem_of_isNilpotent hZ (Z.sub_mem h0 hc) hd
  exact sub_eq_zero.1 this

theorem cc_smul {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (t : k) {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ CC Z) : t • x ∈ CC Z ∧ zpart Z (t • x) = t • zpart Z x := by
  obtain ⟨h0, hn0⟩ := zpart_spec hx
  have hB : t • x ∈ Bz Z := fun a ha => by rw [mul_smul_comm, smul_mul_assoc, hx.2 a ha]
  have hn : IsNilpotent (t • x - t • zpart Z x) := by
    rw [← smul_sub]
    obtain ⟨m, hm⟩ := hn0
    exact ⟨m, by rw [smul_pow, hm, smul_zero]⟩
  have hc : t • zpart Z x ∈ Z := Z.smul_mem h0 t
  exact ⟨⟨⟨_, hc, hn⟩, hB⟩, zpart_unique hZ hB hc hn⟩

theorem cc_add {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c x : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) :
    (x + c ∈ CC Z ↔ x ∈ CC Z) ∧ (x ∈ CC Z → zpart Z (x + c) = zpart Z x + c) := by
  have hcB := Z_sub_Bz hZ hc
  have hBz : x + c ∈ Bz Z ↔ x ∈ Bz Z := by
    constructor
    · intro h a ha
      have e1 := h a ha
      have e2 := hcB a ha
      rw [mul_add, add_mul, e2] at e1
      exact add_right_cancel e1
    · intro h a ha
      rw [mul_add, add_mul, h a ha, hcB a ha]
  refine ⟨⟨fun h => ⟨?_, hBz.1 h.2⟩, fun h => ⟨?_, hBz.2 h.2⟩⟩, fun h => ?_⟩
  · obtain ⟨c1, hc1, hn⟩ := h.1
    exact ⟨c1 - c, Z.sub_mem hc1 hc, by simpa [sub_sub_eq_add_sub, add_sub_add_right_eq_sub] using hn⟩
  · obtain ⟨c1, hc1, hn⟩ := h.1
    exact ⟨c1 + c, Z.add_mem hc1 hc, by simpa [add_sub_add_right_eq_sub] using hn⟩
  · obtain ⟨h0, hn0⟩ := zpart_spec h
    refine zpart_unique hZ (hBz.2 h.2) (Z.add_mem h0 hc) ?_
    simpa [add_sub_add_right_eq_sub] using hn0

theorem cc_conj {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ CC Z) :
    g.val * x * g⁻¹.val ∈ CC Z ∧ zpart Z (g.val * x * g⁻¹.val) = zpart Z x := by
  obtain ⟨h0, hn0⟩ := zpart_spec hx
  have hgi : ∀ a ∈ Z, a * g⁻¹.val = g⁻¹.val * a := by
    intro a ha
    have e := hg a ha
    calc a * g⁻¹.val = g⁻¹.val * (g.val * a) * g⁻¹.val := by simp [← mul_assoc]
      _ = g⁻¹.val * (a * g.val) * g⁻¹.val := by rw [e]
      _ = g⁻¹.val * a := by simp [mul_assoc]
  have hB : g.val * x * g⁻¹.val ∈ Bz Z := fun a ha => by
    rw [← mul_assoc, ← mul_assoc, hg a ha, mul_assoc (g.val), hx.2 a ha, mul_assoc, mul_assoc, hgi a ha, ← mul_assoc,
      ← mul_assoc]
  have hcz : g.val * zpart Z x * g⁻¹.val = zpart Z x := by
    rw [← hg _ h0, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hn : IsNilpotent (g.val * x * g⁻¹.val - zpart Z x) := by
    have e : g.val * x * g⁻¹.val - zpart Z x = g.val * (x - zpart Z x) * g⁻¹.val := by
      rw [mul_sub, sub_mul, hcz]
    rw [e]
    obtain ⟨m, hm⟩ := hn0
    refine ⟨m, ?_⟩
    have : ∀ j : ℕ, (g.val * (x - zpart Z x) * g⁻¹.val) ^ j = g.val * (x - zpart Z x) ^ j * g⁻¹.val := by
      intro j
      induction j with
      | zero => simp [← Units.val_mul]
      | succ j ih =>
        rw [pow_succ, ih, pow_succ]
        simp only [mul_assoc]
        rw [← mul_assoc (g⁻¹.val) (g.val), ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [this, hm, mul_zero, zero_mul]
  exact ⟨⟨⟨_, h0, hn⟩, hB⟩, zpart_unique hZ hB h0 hn⟩

theorem sub_mem_NB {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {x : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ CC Z) : x - zpart Z x ∈ NB Z := by
  obtain ⟨h0, hn0⟩ := zpart_spec hx
  refine ⟨fun a ha => ?_, hn0⟩
  rw [mul_sub, sub_mul, hx.2 a ha, Z_sub_Bz hZ h0 a ha]

theorem cc_of_NB {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c m : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (hm : m ∈ NB Z) : c + m ∈ CC Z ∧ zpart Z (c + m) = c := by
  have hB : c + m ∈ Bz Z := fun a ha => by rw [mul_add, add_mul, Z_sub_Bz hZ hc a ha, hm.1 a ha]
  have hn : IsNilpotent (c + m - c) := by simpa using hm.2
  exact ⟨⟨⟨c, hc, hn⟩, hB⟩, zpart_unique hZ hB hc hn⟩

theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Bz Z) := by
  have e : Bz Z = ⋂ a ∈ (Z : Set (Matrix (Fin n) (Fin n) k)), {x | a * x = x * a} := by
    ext x; simp [Bz]
  rw [e]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

theorem isClosed_NB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (NB Z) :=
  (isClosed_Bz Z).inter PositivityTheory.RgUd.T.Nil.Orb.Ozn.isClosed_nilpotent

end PositivityTheory.RgUd.TP.Nil.Fib1
