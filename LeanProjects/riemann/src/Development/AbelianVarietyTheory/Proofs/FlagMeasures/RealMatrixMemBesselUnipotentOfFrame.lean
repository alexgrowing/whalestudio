import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
open Matrix

noncomputable section
open Formalism.HermitianLatticeCounting.S6 Formalism.QuantumDeterminants GlobalTheory.DegVol.RealMat

namespace GlobalTheory.DegVol.FrameUnip

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {k r : ℕ} {σ : K →+* ℂ} {Φ : V → Fin (2 * r + k + 1) → ℂ}

theorem phi_zero' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) : Φ 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem phi_sub' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (x y : V) : Φ (x - y) = Φ x - Φ y := by
  have := h.1 (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem phi_sum' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {α : Type} (s : Finset α) (f : α → V) :
    Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phi_zero' h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem span_ind' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (P : (Fin (2 * r + k + 1) → ℂ) → Prop) (h0 : ∀ x, P (Φ x))
    (ha : ∀ u v, P u → P v → P (u + v)) (hs : ∀ (c : ℂ) u, P u → P (c • u)) (u : Fin (2 * r + k + 1) → ℂ) : P u := by
  have hu : u ∈ Submodule.span ℂ (Set.range Φ) := by rw [h.2.2.2]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact h0 y
  | zero => rw [← phi_zero' h]; exact h0 0
  | add x y _ _ hx hy => exact ha _ _ hx hy
  | smul c x _ hx => exact hs _ _ hx

theorem mem_UH' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (e : ∀ x y, herm (Hpk k r) (m *ᵥ Φ x) (m *ᵥ Φ y) = herm (Hpk k r) (Φ x) (Φ y)) : m ∈ UH (Hpk k r) := by
  have h1 : ∀ u w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w := by
    intro u
    refine span_ind' h (fun u => ∀ w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w) (fun x => ?_)
      (fun u v hu hv w => by rw [mulVec_add, herm_add_left, herm_add_left, hu, hv])
      (fun c u hu w => by rw [mulVec_smul, herm_smul_left, herm_smul_left, hu]) u
    exact span_ind' h _ (e x) (fun u v hu hv => by rw [mulVec_add, herm_add_right, herm_add_right, hu, hv])
      (fun c u hu => by rw [mulVec_smul, herm_smul_right, herm_smul_right, hu])
  ext i j
  exact (herm_bvec _ i j).symm.trans (by rw [← herm_mulVec, h1, herm_bvec])

theorem coord_span (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {e : Fin r → V} {ρ : Fin r → ℂ}
    (he : ∀ a, Φ (e a) = ρ a • bvec (eI k r a)) {S : Set (Fin r)} (i : Fin (2 * r + k + 1))
    (hS : ∀ b ∈ S, b.val < i.val) {y : V} (hy : y ∈ Submodule.span K (e '' S)) : Φ y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' := hS b hb
    have : i ≠ eI k r b := fun e => by
      have := congrArg Fin.val e
      simp only [eI] at this; omega
    simp [he, bvec, this]
  | zero => rw [phi_zero' h]; rfl
  | add x y _ _ hx hy => rw [h.1, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [h.2.1, Pi.smul_apply, hx, smul_zero]

theorem mem_Nset : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro K V _ _ _ _ H k r σ Φ h e f ρ ρ' hρ hρ' he hf hef m hm h2 h3 n hn
  refine ⟨mem_UH' h fun x y => by rw [hn, hn, h.2.2.1, h.2.2.1, hm], fun a i hi => ?_, fun i j hj hj' hi => ?_⟩
  · have := coord_span h he i (S := {b | b < a}) (fun b hb => lt_of_lt_of_le (Fin.lt_def.1 hb) hi) (h2 a)
    rw [phi_sub' h, ← hn, he, mulVec_smul, ← smul_sub, Pi.smul_apply, smul_eq_zero, or_iff_right (hρ a), Pi.sub_apply,
      sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this
  · let P : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u =>
      u - ∑ a : Fin r, herm (Hpk k r) u (Φ (e a)) • Φ (f a)
    have hP : ∀ u, (n *ᵥ P u - P u) i = 0 := by
      refine span_ind' h _ (fun x => ?_) (fun u v hu hv => ?_) (fun c u hu => ?_)
      · have ex : P (Φ x) = Φ (x - ∑ a : Fin r, H.B x (e a) • f a) := by
          simp only [P, phi_sub' h, phi_sum' h, h.2.1, h.2.2.1]
        rw [ex, hn, ← phi_sub' h]
        have hperp : ∀ b, H.B (e b) (x - ∑ a : Fin r, H.B x (e a) • f a) = 0 := fun b => by
          rw [map_sub, map_sum]
          simp [hef]
          rw [starRingEnd_apply, H.herm, sub_self]
        have := h3 _ hperp
        rw [← Set.image_univ] at this
        exact coord_span h he i (fun b _ => lt_of_lt_of_le b.2 hi) this
      · have ex : P (u + v) = P u + P v := by
          simp only [P, herm_add_left, add_smul, Finset.sum_add_distrib]; abel
        rw [ex, mulVec_add, add_sub_add_comm, Pi.add_apply, hu, hv, add_zero]
      · have ex : P (c • u) = c • P u := by
          simp only [P, herm_smul_left, smul_sub, Finset.smul_sum, smul_smul]
        rw [ex, mulVec_smul, ← smul_sub, Pi.smul_apply, hu, smul_zero]
    have ex : P (bvec j) = bvec j := by
      simp only [P]
      rw [Finset.sum_eq_zero, sub_zero]
      intro a _
      have hne : esI k r a ≠ j := fun e' => by
        have := congrArg Fin.val e'
        have := a.2
        simp only [esI] at *; omega
      rw [he, herm_smul_right, herm_eI]
      simp [bvec, hne]
    have := hP (bvec j)
    rw [ex, Pi.sub_apply, sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this

end GlobalTheory.DegVol.FrameUnip
