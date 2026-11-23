import Mathlib

open scoped ENNReal

namespace GlobalTheory

open MulAction

theorem encard_fiber_orbit_mul_stabilizer {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by
  classical
  have hx0 : π (g • x) = y := by rw [hπ, hg]
  have hset : (orbit (stabilizer Γ y) (g • x) : Set L) = {z : L | π z = y ∧ z ∈ orbit Γ x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : Γ) • y = y := mem_stabilizer_iff.mp h.2
      refine ⟨?_, (h : Γ) * g, ?_⟩
      · show π ((h : Γ) • g • x) = y
        rw [hπ, hx0, hh]
      · show ((h : Γ) * g) • x = (h : Γ) • g • x
        rw [mul_smul]
    · rintro ⟨hz, k, rfl⟩
      have hk : k * g⁻¹ ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff]
        calc (k * g⁻¹) • y = (k * g⁻¹) • g • π x := by rw [hg]
          _ = π (k • x) := by rw [mul_smul, inv_smul_smul, hπ]
          _ = y := hz
      exact ⟨⟨k * g⁻¹, hk⟩, show (k * g⁻¹) • g • x = k • x by rw [mul_smul, inv_smul_smul]⟩
  have e : stabilizer (stabilizer Γ y) (g • x) ≃ stabilizer Γ x :=
    { toFun := fun s => ⟨g⁻¹ * ((s : stabilizer Γ y) : Γ) * g, by
        have hs : ((s : stabilizer Γ y) : Γ) • g • x = g • x := mem_stabilizer_iff.mp s.2
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hs, inv_smul_smul]⟩
      invFun := fun t => ⟨⟨g * (t : Γ) * g⁻¹, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          rw [mem_stabilizer_iff, ← hg, mul_smul, mul_smul, inv_smul_smul, ← hπ, ht]⟩, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          show (g * (t : Γ) * g⁻¹) • g • x = g • x
          rw [mul_smul, mul_smul, inv_smul_smul, ht]⟩
      left_inv := fun s => by
        apply Subtype.ext; apply Subtype.ext
        show g * (g⁻¹ * ((s : stabilizer Γ y) : Γ) * g) * g⁻¹ = ((s : stabilizer Γ y) : Γ)
        group
      right_inv := fun t => by
        apply Subtype.ext
        show g⁻¹ * (g * (t : Γ) * g⁻¹) * g = (t : Γ)
        group }
  have key := ENat.card_congr
    (Subgroup.groupEquivQuotientProdSubgroup (s := stabilizer (stabilizer Γ y) (g • x)))
  rw [ENat.card_prod, ← ENat.card_congr (orbitEquivQuotientStabilizer (stabilizer Γ y) (g • x)),
    ENat.card_congr e] at key
  rw [← hset]
  exact key.symm

theorem encard_eq_tsum_fibers {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by
  classical
  have h1 : ∑' _ : F, (1 : ℝ≥0∞) = ∑' _ : (Σ o : Q, {z : F // q z = o}), (1 : ℝ≥0∞) :=
    ((Equiv.sigmaFiberEquiv (fun z : F => q z)).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
  rw [← ENNReal.tsum_set_one F, h1, ENNReal.tsum_sigma']
  refine tsum_congr fun o => ?_
  simp only [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma inv_coe_mul_mul_coe_eq_inv_coe (a b : ℕ∞) (h0 : a * b ≠ 0) (ht : a * b ≠ ⊤) :
    (((a * b : ℕ∞) : ℝ≥0∞))⁻¹ * (a : ℝ≥0∞) = (b : ℝ≥0∞)⁻¹ := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  induction a using ENat.recTopCoe with
  | top => exact absurd (ENat.top_mul hb0) ht
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact absurd (by rw [mul_comm]; exact ENat.top_mul ha0) ht
    | coe k =>
      have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha0
      have hk : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb0
      rw [ENat.toENNReal_mul, ENat.toENNReal_coe, ENat.toENNReal_coe,
        ENNReal.mul_inv (Or.inl hm) (Or.inr hk), mul_comm (m : ℝ≥0∞)⁻¹, mul_assoc,
        ENNReal.inv_mul_cancel hm (ENNReal.natCast_ne_top m), mul_one]

private lemma quotient_mk_map_eq_of_mem_orbit {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) {a b : L} (h : a ∈ orbit Γ b) :
    Quotient.mk (orbitRel Γ Y) (π a) = Quotient.mk (orbitRel Γ Y) (π b) := by
  obtain ⟨g, rfl⟩ := h
  apply Quotient.sound
  show π (g • b) ∈ orbit Γ (π b)
  rw [hπ]
  exact mem_orbit _ g

theorem tsum_inv_stabilizer_eq_tsum_mul_fiber {Γ L Y : Type} [Group Γ] [MulAction Γ L]
    [MulAction Γ Y] (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x)
    (hfin : ∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) :
    (∑' o : MulAction.orbitRel.Quotient Γ L,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)
      = ∑' o : MulAction.orbitRel.Quotient Γ Y,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹
          * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  classical
  set φ : orbitRel.Quotient Γ L → orbitRel.Quotient Γ Y :=
    fun o => Quotient.mk (orbitRel Γ Y) (π o.out) with hφ
  have hsplit := ((Equiv.sigmaFiberEquiv φ).tsum_eq
      (fun o : orbitRel.Quotient Γ L => (((stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)).symm.trans
    (ENNReal.tsum_sigma' _)
  refine hsplit.trans (tsum_congr fun O => ?_)
  change ∑' o : {o // φ o = O}, (((stabilizer Γ o.1.out : Set Γ).encard : ℝ≥0∞))⁻¹ = _
  have hsupp : Function.support (fun o : orbitRel.Quotient Γ L =>
      ((({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).encard : ℕ∞) : ℝ≥0∞))
      ⊆ {o | φ o = O} := by
    intro o ho
    obtain ⟨z, hz, hzo⟩ : ({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).Nonempty := by
      rw [← Set.encard_pos, pos_iff_ne_zero]
      intro h0
      exact ho (by simp only [h0, ENat.toENNReal_zero])
    have hzo' : o.out ∈ orbit Γ z := by
      apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hzo.symm
    show Quotient.mk (orbitRel Γ Y) (π o.out) = O
    rw [quotient_mk_map_eq_of_mem_orbit π hπ hzo', show π z = O.out from hz]
    exact Quotient.out_eq O
  rw [encard_eq_tsum_fibers (π ⁻¹' {O.out}) (Quotient.mk (orbitRel Γ L)),
    ← tsum_subtype_eq_of_support_subset hsupp, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun o => ?_
  have hx : Quotient.mk (orbitRel Γ Y) (π o.1.out) = Quotient.mk (orbitRel Γ Y) O.out := by
    rw [Quotient.out_eq O]
    exact o.2
  obtain ⟨h, hh⟩ : π o.1.out ∈ orbit Γ O.out := orbitRel_apply.mp (Quotient.exact hx)
  have hg : h⁻¹ • π o.1.out = O.out := by rw [← hh, inv_smul_smul]
  have hF : {z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o.1}
      = {z : L | π z = O.out ∧ z ∈ orbit Γ o.1.out} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr Iff.rfl ⟨fun hz => ?_, fun hz => ?_⟩
    · apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hz
    · rw [← Quotient.out_eq o.1]
      exact Quotient.sound (orbitRel_apply.mpr hz)
  have hmul := encard_fiber_orbit_mul_stabilizer π hπ o.1.out O.out h⁻¹ hg
  have hfinY : Finite (stabilizer Γ O.out) := hfin O.out ⟨h⁻¹ • o.1.out, by rw [hπ, hg]⟩
  have hY0 : (stabilizer Γ O.out : Set Γ).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.mp ⟨1, (stabilizer Γ O.out).one_mem⟩
  have hYt : (stabilizer Γ O.out : Set Γ).encard ≠ ⊤ := by
    rw [Ne, Set.encard_eq_top_iff, Set.not_infinite]
    exact Set.toFinite _
  rw [hF, ← hmul]
  rw [← hmul] at hY0 hYt
  exact (inv_coe_mul_mul_coe_eq_inv_coe _ _ hY0 hYt).symm

end GlobalTheory
