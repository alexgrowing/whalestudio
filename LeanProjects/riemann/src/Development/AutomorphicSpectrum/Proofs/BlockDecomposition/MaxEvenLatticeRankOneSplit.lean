import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin.RankOne

section

variable {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]

theorem h_smul_smul {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (r r' : R) (w : V) :
    h (r • w) (r' • w) = r' * (c r * c (h w w)) := by
  rw [hh.smul_right, hh.symm w (r • w), hh.smul_right, map_mul]

theorem phi_h {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (φ : R ≃+* k × k)
    (hc : ∀ r, φ (c r) = (φ r).swap) (r r' : R) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) :
    φ (h (r • w) (r' • w)) = ((φ r').1 * (φ r).2 * δ, (φ r').2 * (φ r).1 * δ) := by
  rw [h_smul_smul hh, map_mul, map_mul, hc, hc, hd]
  ext <;> simp [mul_assoc]

theorem smul_eq_zero_of_unit {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (r : R) (h0 : r • w = 0) : r = 0 := by
  have h1 := hh.smul_right r w w
  have h2 := hh.smul_right 0 w w
  rw [h0] at h1
  rw [zero_smul, zero_mul] at h2
  rw [h2] at h1
  exact hu.mul_left_eq_zero.1 h1.symm

theorem span_comp_false (p : R →+* k) {c : R →+* R} {h : V → V → R} (hh : IsHerm c h) (w : V)
    (hu : IsUnit (h w w)) (𝔬 : Subring R) (L : Submodule 𝔬 V)
    (hspan : Submodule.span R (L : Set V) = ⊤) (hL : ∀ x ∈ L, ∃ r : R, x = r • w ∧ p r = 0) : False := by
  let S : Submodule R V :=
    { carrier := {x | ∃ r : R, x = r • w ∧ p r = 0}
      add_mem' := by
        rintro _ _ ⟨r, rfl, hr⟩ ⟨s, rfl, hs⟩
        exact ⟨r + s, (add_smul _ _ _).symm, by simp [hr, hs]⟩
      zero_mem' := ⟨0, (zero_smul _ _).symm, map_zero p⟩
      smul_mem' := by
        rintro a _ ⟨r, rfl, hr⟩
        exact ⟨a * r, (mul_smul _ _ _).symm, by simp [hr]⟩ }
  have hle : Submodule.span R (L : Set V) ≤ S := Submodule.span_le.2 fun x hx => hL x hx
  rw [hspan] at hle
  obtain ⟨r, hr, h0⟩ : w ∈ S := hle Submodule.mem_top
  have h1 : (1 - r) • w = 0 := by rw [sub_smul, one_smul, ← hr, sub_self]
  have h2 : r = 1 := (sub_eq_zero.1 (smul_eq_zero_of_unit hh w hu _ h1)).symm
  rw [h2, map_one] at h0
  exact one_ne_zero h0

def lat (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (w : V) (a b : k) : Submodule 𝔬 V where
  carrier := {v | ∃ r : R, v = r • w ∧ (∃ x ∈ O, (φ r).1 = a * x) ∧ ∃ y ∈ O, (φ r).2 = b * y}
  add_mem' := by
    rintro _ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ ⟨s, rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    exact ⟨r + s, (add_smul _ _ _).symm, ⟨x + x', O.add_mem _ _ hx hx', by simp [h1, h1', mul_add]⟩,
      y + y', O.add_mem _ _ hy hy', by simp [h2, h2', mul_add]⟩
  zero_mem' := ⟨0, (zero_smul _ _).symm, ⟨0, O.zero_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  smul_mem' := by
    rintro ⟨s, hs⟩ _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    obtain ⟨hs1, hs2⟩ := (h𝔬 s).1 hs
    refine ⟨s * r, ?_, ⟨(φ s).1 * x, O.mul_mem _ _ hs1 hx, ?_⟩, (φ s).2 * y, O.mul_mem _ _ hs2 hy, ?_⟩
    · rw [mul_smul]; rfl
    · simp only [map_mul, Prod.fst_mul, h1]; ring
    · simp only [map_mul, Prod.snd_mul, h2]; ring

theorem lat_even {O : ValuationSubring k} {φ : R ≃+* k × k} {c : R →+* R} {𝔬 : Subring R}
    (hc : ∀ r, φ (c r) = (φ r).swap) (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O)
    {h : V → V → R} (hh : IsHerm c h) (w : V) (δ : k) (hd : φ (h w w) = (δ, δ)) (a b : k)
    (hab : a * b * δ = 1) : IsEvenInt c 𝔬 h (lat O φ 𝔬 h𝔬 w a b) := by
  constructor
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩ _ ⟨r', rfl, ⟨x', hx', h1'⟩, y', hy', h2'⟩
    rw [h𝔬, phi_h hh φ hc r r' w δ hd, h1, h2, h1', h2']
    constructor
    · have : a * x' * (b * y) * δ = x' * y := by
        calc a * x' * (b * y) * δ = (a * b * δ) * (x' * y) := by ring
          _ = x' * y := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hx' hy
    · have : b * y' * (a * x) * δ = y' * x := by
        calc b * y' * (a * x) * δ = (a * b * δ) * (y' * x) := by ring
          _ = y' * x := by rw [hab, one_mul]
      simpa [this] using O.mul_mem _ _ hy' hx
  · rintro _ ⟨r, rfl, ⟨x, hx, h1⟩, y, hy, h2⟩
    have hxy : (φ r).1 * (φ r).2 * δ = x * y := by
      rw [h1, h2]
      calc a * x * (b * y) * δ = (a * b * δ) * (x * y) := by ring
        _ = x * y := by rw [hab, one_mul]
    refine ⟨φ.symm (x * y, 0), ?_, ?_⟩
    · rw [h𝔬]
      simpa using O.mul_mem _ _ hx hy
    · apply φ.injective
      rw [phi_h hh φ hc r r w δ hd, map_add, hc]
      simp only [RingEquiv.apply_symm_apply]
      ext
      · simpa using hxy
      · simpa [mul_comm (φ r).1 (φ r).2] using (by rw [mul_comm (φ r).2 (φ r).1]; exact hxy : (φ r).2 * (φ r).1 * δ = x * y)

end

theorem unimodular_coords : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V] (O : ValuationSubring k) (φ : R ≃+* k × k) (c : R →+* R) (𝔬 : Subring R), (∀ r, φ (c r) = (φ r).swap) → (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ h : V → V → R, IsHerm c h → ∀ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) → IsUnit (h w₀ w₀) → ∀ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L → ∀ α β : k, (∀ r : R, r • w₀ ∈ L ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y)) → α ≠ 0 ∧ β ≠ 0 ∧ ∃ u : k, u ∈ O ∧ u⁻¹ ∈ O ∧ α * β * (φ (h w₀ w₀)).1 = u := by
  intro k R V _ _ _ _ O φ c 𝔬 hc h𝔬 h hh w₀ hw hu L hL α β hmem
  obtain ⟨⟨_, hspan⟩, ⟨hint, _⟩, hmax⟩ := hL
  have hcd : c (h w₀ w₀) = h w₀ w₀ := (hh.symm w₀ w₀).symm
  obtain ⟨δ, hd⟩ : ∃ δ, φ (h w₀ w₀) = (δ, δ) := by
    have h1 := hc (h w₀ w₀)
    rw [hcd] at h1
    exact ⟨(φ (h w₀ w₀)).1, Prod.ext rfl (congrArg Prod.fst h1).symm⟩
  have hδ : δ ≠ 0 := by
    have h1 : IsUnit (φ (h w₀ w₀)) := hu.map φ
    rw [hd, Prod.isUnit_iff] at h1
    exact h1.1.ne_zero
  have hα : α ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.fst k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨⟨y, _, hy⟩, _⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  have hβ : β ≠ 0 := by
    rintro rfl
    refine span_comp_false ((RingHom.snd k k).comp (φ : R →+* k × k)) hh w₀ hu 𝔬 L hspan fun x hx => ?_
    obtain ⟨r, rfl⟩ := hw x
    obtain ⟨_, ⟨y, _, hy⟩⟩ := (hmem r).1 hx
    exact ⟨r, rfl, by simpa using hy⟩
  refine ⟨hα, hβ, ?_⟩
  have hγ0 : α * β * δ ≠ 0 := mul_ne_zero (mul_ne_zero hα hβ) hδ
  have hγ : α * β * δ ∈ O := by
    have h1 : φ.symm (α, 0) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
    have h2 : φ.symm (0, β) • w₀ ∈ L :=
      (hmem _).2 ⟨⟨0, O.zero_mem, by simp⟩, 1, O.one_mem, by simp⟩
    have h3 := (h𝔬 _).1 (hint _ h1 _ h2)
    rw [phi_h hh φ hc _ _ w₀ δ hd] at h3
    have h4 := h3.2
    simp only [RingEquiv.apply_symm_apply] at h4
    rwa [mul_comm β α] at h4
  have hab : α / (α * β * δ) * β * δ = 1 := by
    field_simp
  have hle : L ≤ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β := by
    intro v hv
    obtain ⟨r, rfl⟩ := hw v
    obtain ⟨⟨x, hx, h1⟩, y, hy, h2⟩ := (hmem r).1 hv
    refine ⟨r, rfl, ⟨α * β * δ * x, O.mul_mem _ _ hγ hx, ?_⟩, y, hy, h2⟩
    rw [h1]
    field_simp
  have hL₂ := hmax _ (lat_even hc h𝔬 hh w₀ δ hd _ _ hab) hle
  have hmem₂ : φ.symm (α / (α * β * δ), 0) • w₀ ∈ lat O φ 𝔬 h𝔬 w₀ (α / (α * β * δ)) β :=
    ⟨_, rfl, ⟨1, O.one_mem, by simp⟩, 0, O.zero_mem, by simp⟩
  obtain ⟨⟨x, hx, h1⟩, _⟩ := (hmem _).1 (hL₂ hmem₂)
  simp only [RingEquiv.apply_symm_apply] at h1
  refine ⟨α * β * δ, hγ, ?_, ?_⟩
  · have h2 : (α * β * δ)⁻¹ = x := by
      apply mul_left_cancel₀ hα
      rw [← h1, div_eq_mul_inv]
    rwa [h2]
  · rw [hd]

end GlobalTheory.CompanionTheory.KFin.RankOne
