import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbFib

section
variable {G γ : Type} [Group G] [MulAction G γ]

end

variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]

open NumberField Matrix in
open scoped ENNReal Classical in
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
theorem _root_.GlobalTheory.Mass.OrbFib.key (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : α) (k : G) :
    ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) =
      (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) *
        ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) := by
  have hkx : π (k • x) = k • π x := hπ k x
  have e1 : MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x) ≃
      MulAction.stabilizer G (k • x) :=
    { toFun := fun h => ⟨(h.1 : G), h.2⟩
      invFun := fun g => ⟨⟨g.1, by
          rw [MulAction.mem_stabilizer_iff, ← hkx, ← hπ,
            MulAction.mem_stabilizer_iff.1 g.2]⟩, g.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : MulAction.stabilizer G (k • x) ≃ MulAction.stabilizer G x := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact ((MulAction.stabilizer G x).equivMapOfInjective _
      (MulAut.conj k).injective).toEquiv.symm
  have e3 : MulAction.orbit (MulAction.stabilizer G (k • π x)) (k • x) =
      MulAction.orbit G x ∩ π ⁻¹' {k • π x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨(h : G) * k, ?_⟩, ?_⟩
      · show ((h : G) * k) • x = (h : G) • (k • x)
        exact mul_smul _ _ _
      · show π ((h : G) • (k • x)) = k • π x
        rw [hπ, hkx]
        exact h.2
    · rintro ⟨⟨g, rfl⟩, hz⟩
      have hz' : g • π x = k • π x := by rw [← hπ]; exact hz
      refine ⟨⟨g * k⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_smul, hz']
      · show (g * k⁻¹) • (k • x) = g • x
        rw [mul_smul, inv_smul_smul]
  have e4 : (MulAction.stabilizer G (k • π x) ⧸
      MulAction.stabilizer (MulAction.stabilizer G (k • π x)) (k • x)) ≃
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x} : Set α) :=
    (MulAction.orbitEquivQuotientStabilizer _ (k • x)).symm.trans (Equiv.setCongr e3)
  have hcard : ENat.card (MulAction.stabilizer G (k • π x)) =
      (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard *
        ENat.card (MulAction.stabilizer G x) := by
    rw [Set.encard, ← ENat.card_congr e4, ← ENat.card_congr (e1.trans e2), ← ENat.card_prod]
    exact ENat.card_congr Subgroup.groupEquivQuotientProdSubgroup
  rw [hcard]
  exact ENat.toENNReal_mul _ _

open NumberField Matrix in
open scoped ENNReal Classical in
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
theorem _root_.GlobalTheory.Mass.OrbFib.mem_orbit_out (q : MulAction.orbitRel.Quotient G α) (x : α) :
    x ∈ MulAction.orbit G (Quotient.out q) ↔ (Quotient.mk (MulAction.orbitRel G α) x) = q := by
  constructor
  · intro h
    exact (Quotient.sound h).trans (Quotient.out_eq q)
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq q).symm)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
theorem _root_.GlobalTheory.Mass.OrbFib.encard_orbits (X : Set α) (hX : _root_.GlobalTheory.Mass.Stable G X)
    (S : Set α) :
    (((X ∩ S).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        (((MulAction.orbit G (Quotient.out q.1) ∩ S).encard : ℕ∞) : ℝ≥0∞) := by
  have hmem : ∀ (q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X}) (a : α),
      a ∈ MulAction.orbit G (Quotient.out q.1) → a ∈ X := by
    rintro q a ⟨g, rfl⟩
    exact hX g _ q.2
  have h1 : ∀ T : Set α, ((T.encard : ℕ∞) : ℝ≥0∞) =
      ∑' a : α, T.indicator (fun _ => (1 : ℝ≥0∞)) a := by
    intro T
    rw [← ENNReal.tsum_set_one]
    exact tsum_subtype T (fun _ => (1 : ℝ≥0∞))
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  by_cases haS : a ∈ S
  · by_cases haX : a ∈ X
    · have hq0 : Quotient.out (Quotient.mk (MulAction.orbitRel G α) a) ∈ X := by
        obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel G α) a
        rw [← hg]
        exact hX g a haX
      rw [Set.indicator_of_mem (show a ∈ X ∩ S from ⟨haX, haS⟩), tsum_eq_single
        (⟨Quotient.mk _ a, hq0⟩ : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X})]
      · rw [Set.indicator_of_mem]
        exact ⟨(_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).2 rfl, haS⟩
      · intro q hq
        rw [Set.indicator_of_notMem]
        rintro ⟨h, -⟩
        exact hq (Subtype.ext ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out _ a).1 h).symm)
    · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haX h.1)]
      symm
      refine ENNReal.tsum_eq_zero.2 fun q => ?_
      rw [Set.indicator_of_notMem]
      rintro ⟨h, -⟩
      exact haX (hmem q a h)
  · rw [Set.indicator_of_notMem (fun h : a ∈ X ∩ S => haS h.2)]
    symm
    refine ENNReal.tsum_eq_zero.2 fun q => ?_
    rw [Set.indicator_of_notMem]
    rintro ⟨-, h⟩
    exact haS h

end GlobalTheory.Mass.OrbFib

namespace GlobalTheory.Mass

open NumberField Matrix in
open scoped ENNReal Classical in
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β] in
private theorem tsum_inv_card_stabilizer_mul_encard_orbit_fibre (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (Y : Set β) (hY : _root_.GlobalTheory.Mass.Stable G Y)
    (hfin : ∀ y ∈ Y, Finite (MulAction.stabilizer G y)) (x : α) (hx : π x ∈ Y) :
    ∑' r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ := by
  obtain ⟨k, hk⟩ := Quotient.mk_out (s := MulAction.orbitRel G β) (π x)
  have hr0 : Quotient.out (Quotient.mk (MulAction.orbitRel G β) (π x)) ∈ Y := by
    rw [← hk]
    exact hY k _ hx
  rw [tsum_eq_single ⟨_, hr0⟩]
  · dsimp only
    rw [← hk, _root_.GlobalTheory.Mass.OrbFib.key π hπ x k]
    have hyY : k • π x ∈ Y := hY k _ hx
    have hfy := hfin _ hyY
    have hyT : ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      haveI := hfy
      rw [ENat.card_eq_coe_natCard]
      simp
    rw [_root_.GlobalTheory.Mass.OrbFib.key π hπ x k] at hyT
    have hc0 : ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have : ENat.card (MulAction.stabilizer G x) ≠ 0 := by
        rw [Ne, ENat.card_eq_zero_iff_empty, not_isEmpty_iff]
        exact ⟨1⟩
      simpa using this
    have he0 : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ 0 := by
      have hmem : k • x ∈ MulAction.orbit G x ∩ π ⁻¹' {k • π x} :=
        ⟨⟨k, rfl⟩, by simp [hπ]⟩
      have : (MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard ≠ 0 :=
        Set.encard_ne_zero.2 ⟨_, hmem⟩
      simpa using this
    have heT : (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by
      intro h
      apply hyT
      rw [h, ENNReal.top_mul hc0]
    rw [ENNReal.mul_inv (Or.inl he0) (Or.inl heT), mul_right_comm,
      ENNReal.inv_mul_cancel he0 heT, one_mul]
  · intro r hr
    have hempty : MulAction.orbit G x ∩ π ⁻¹' {Quotient.out r.1} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨g, rfl⟩ hz
      apply hr
      apply Subtype.ext
      rw [hπ] at hz
      have hmem : π x ∈ MulAction.orbit G (Quotient.out r.1) :=
        ⟨g⁻¹, by rw [← hz]; exact inv_smul_smul g (π x)⟩
      exact ((_root_.GlobalTheory.Mass.OrbFib.mem_orbit_out r.1 (π x)).1 hmem).symm
    rw [hempty]
    simp

open NumberField Matrix in
open scoped ENNReal Classical in

theorem _root_.GlobalTheory.Mass.orbMass_eq_orbSum_fibre : ∀ (G α β : Type) [Group G] [MulAction G α]
    [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) →
    _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G Y → Set.MapsTo π X Y →
    (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) →
    _root_.GlobalTheory.Mass.orbMass G X =
      _root_.GlobalTheory.Mass.orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  intro G α β _ _ _ X Y π hπ hX hY hmaps hfin
  unfold _root_.GlobalTheory.Mass.orbMass _root_.GlobalTheory.Mass.orbSum
  dsimp only
  have step : ∀ r : {r : MulAction.orbitRel.Quotient G β // Quotient.out r ∈ Y},
      ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
        (((X ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ((ENat.card (MulAction.stabilizer G (Quotient.out r.1)) : ℕ∞) : ℝ≥0∞)⁻¹ *
          (((MulAction.orbit G (Quotient.out q.1) ∩ π ⁻¹' {Quotient.out r.1}).encard : ℕ∞) :
            ℝ≥0∞) := by
    intro r
    rw [_root_.GlobalTheory.Mass.OrbFib.encard_orbits X hX, ENNReal.tsum_mul_left]
  rw [tsum_congr step, ENNReal.tsum_comm]
  refine tsum_congr fun q => ?_
  rw [mul_one]
  exact (tsum_inv_card_stabilizer_mul_encard_orbit_fibre π hπ Y hY hfin _ (hmaps q.2)).symm

end GlobalTheory.Mass
