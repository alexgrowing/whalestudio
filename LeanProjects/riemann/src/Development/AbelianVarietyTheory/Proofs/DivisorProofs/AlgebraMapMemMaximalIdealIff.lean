import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainFibFinite
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem algebraMap_mem_maximalIdeal_iff (c : k) :
    algebraMap k S c ∈ maximalIdeal S ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h
    exact h ((isUnit_iff_ne_zero.mpr hc).map (algebraMap k S))
  · rintro rfl
    simp

theorem residue_eq {π : S → k} (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (s : S) (c : k) (h : s - algebraMap k S c ∈ maximalIdeal S) : π s = c := by
  have hm : algebraMap k S (π s - c) ∈ maximalIdeal S := by
    have := sub_mem h (hπ s)
    rw [map_sub]; convert this using 1; ring
  rw [algebraMap_mem_maximalIdeal_iff] at hm
  exact sub_eq_zero.mp hm

def tangentHom (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) :
    S →ₐ[k] DualNumber k where
  toFun s := TrivSqZeroExt.inl (π s) + TrivSqZeroExt.inr (f s)
  map_one' := by
    have : π 1 = 1 := residue_eq hπ 1 1 (by simp)
    ext <;> simp [this, hf1]
  map_mul' s t := by
    have hm : π (s * t) = π s * π t := residue_eq hπ _ _ (by
      rw [map_mul]
      convert add_mem (Ideal.mul_mem_right t _ (hπ s)) (Ideal.mul_mem_left _ (algebraMap k S (π s)) (hπ t))
        using 1
      ring)
    have hfa : ∀ c, f (algebraMap k S c) = 0 := by
      intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    have e : s * t = algebraMap k S (π s * π t) + π s • (t - algebraMap k S (π t)) +
        π t • (s - algebraMap k S (π s)) +
        (s - algebraMap k S (π s)) * (t - algebraMap k S (π t)) := by
      simp only [Algebra.smul_def, map_mul]; ring
    have hf : f (s * t) = π s * f t + π t * f s := by
      have huv := hf2 _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hπ s) (hπ t))
      rw [e, map_add, map_add, map_add, map_smul, map_smul, huv, map_sub, map_sub, hfa, hfa, hfa]
      simp
    ext <;> simp [hm, hf] <;> ring
  map_zero' := by
    have : π 0 = 0 := residue_eq hπ 0 0 (by simp)
    ext <;> simp [this]
  map_add' s t := by
    have : π (s + t) = π s + π t := residue_eq hπ _ _ (by
      rw [map_add]; convert add_mem (hπ s) (hπ t) using 1; ring)
    ext <;> simp [this]
  commutes' c := by
    have : π (algebraMap k S c) = c := residue_eq hπ _ _ (by simp)
    have h0 : f (algebraMap k S c) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_zero]
    ext <;> simp [this, h0, TrivSqZeroExt.algebraMap_eq_inl]

theorem tangentHom_snd (π : S → k) (hπ : ∀ s, s - algebraMap k S (π s) ∈ maximalIdeal S)
    (f : S →ₗ[k] k) (hf1 : f 1 = 0) (hf2 : ∀ y ∈ maximalIdeal S ^ 2, f y = 0) (s : S) :
    (tangentHom π hπ f hf1 hf2 s).snd = f s := by
  simp [tangentHom]

theorem epsScaleR_snd (c : k) (x : DualNumber k) : (epsScaleR c x).snd = c * x.snd := by
  simp [epsScaleR]

end GlobalTheory.LocalTangent

namespace GlobalTheory.LocalTangent

open IsLocalRing

variable {k S : Type} [Field k] [CommRing S] [IsLocalRing S] [Algebra k S]

theorem exists_form {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S)
    (h : ∀ c : k, a - c • b ∉ maximalIdeal S ^ 2) :
    ∃ f : S →ₗ[k] k, f 1 = 0 ∧ (∀ y ∈ maximalIdeal S ^ 2, f y = 0) ∧ f b = 0 ∧ f a = 1 := by
  let P : Submodule k S := Submodule.span k {1, b} ⊔ (maximalIdeal S ^ 2).restrictScalars k
  have haP : a ∉ P := by
    intro hP
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hP
    obtain ⟨l, r, rfl⟩ := Submodule.mem_span_pair.mp hy
    have hz2 : z ∈ maximalIdeal S ^ 2 := hz
    have hz' : z ∈ maximalIdeal S := Ideal.pow_le_self two_ne_zero hz2
    have hl : l = 0 := by
      rw [← algebraMap_mem_maximalIdeal_iff (S := S)]
      have e : algebraMap k S l = a - r • b - z := by
        rw [← hyz, Algebra.algebraMap_eq_smul_one]; abel
      rw [e]
      exact sub_mem (sub_mem ha (Submodule.smul_of_tower_mem _ r hb)) hz'
    apply h r
    have e : a - r • b = z := by rw [← hyz, hl]; simp
    rw [e]; exact hz2
  obtain ⟨g, hga, hgP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem haP (by infer_instance)
  have hg0 : ∀ y ∈ P, g y = 0 := fun y hy => by
    have : g y ∈ P.map g := Submodule.mem_map_of_mem hy
    rw [hgP] at this; exact (Submodule.mem_bot k).mp this
  refine ⟨(g a)⁻¹ • g, ?_, ?_, ?_, ?_⟩
  · simp [hg0 1 (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · intro y hy
    simp [hg0 y (Submodule.mem_sup_right hy)]
  · simp [hg0 b (Submodule.mem_sup_left (Submodule.subset_span (by simp)))]
  · simp [hga]

theorem pair_dependent
    (h1 : ∀ a : S, ∃ c : k, a - algebraMap k S c ∈ maximalIdeal S)
    (h3 : ∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k))
    {a b : S} (ha : a ∈ maximalIdeal S) (hb : b ∈ maximalIdeal S) :
    ∃ c : k, a - c • b ∈ maximalIdeal S ^ 2 ∨ b - c • a ∈ maximalIdeal S ^ 2 := by
  by_contra hne
  push_neg at hne
  choose π hπ using h1
  obtain ⟨f₁, h11, h12, h13, h14⟩ := exists_form ha hb (fun c => (hne c).1)
  obtain ⟨f₂, h21, h22, h23, h24⟩ := exists_form hb ha (fun c => (hne c).2)
  obtain ⟨c, hc | hc⟩ := h3 (tangentHom π hπ f₁ h11 h12) (tangentHom π hπ f₂ h21 h22)
  · have := congrArg (fun φ : S →+* DualNumber k => (φ a).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h14, h23, mul_zero] at this
    exact one_ne_zero this
  · have := congrArg (fun φ : S →+* DualNumber k => (φ b).snd) hc
    simp only [RingHom.coe_coe, RingHom.comp_apply, epsScaleR_snd, tangentHom_snd] at this
    rw [h24, h13, mul_zero] at this
    exact one_ne_zero this

theorem maximalIdeal_isPrincipal : ∀ (k : Type) [Field k] (S : Type) [CommRing S] [IsLocalRing S] [Algebra k S],
    (∀ a : S, ∃ c : k, a - algebraMap k S c ∈ IsLocalRing.maximalIdeal S) →
    IsNilpotent (IsLocalRing.maximalIdeal S) →
    (∀ ψ₁ ψ₂ : S →ₐ[k] DualNumber k, ∃ c : k,
      (ψ₁ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₂ : S →+* DualNumber k) ∨
      (ψ₂ : S →+* DualNumber k) = (epsScaleR c).comp (ψ₁ : S →+* DualNumber k)) →
    (IsLocalRing.maximalIdeal S).IsPrincipal := by
  intro k _ S _ _ _ h1 hnil h3
  set m := maximalIdeal S with hm
  have hx : ∃ x ∈ m, m ≤ Ideal.span {x} ⊔ m ^ 2 := by
    by_cases hle : m ≤ m ^ 2
    · exact ⟨0, zero_mem _, le_sup_of_le_right hle⟩
    · obtain ⟨x, hxm, hx2⟩ := Set.not_subset.mp hle
      refine ⟨x, hxm, fun a ha => ?_⟩
      have key : ∃ c : k, a - c • x ∈ m ^ 2 := by
        obtain ⟨c, hc | hc⟩ := pair_dependent h1 h3 ha hxm
        · exact ⟨c, hc⟩
        · have hc0 : c ≠ 0 := by
            rintro rfl; apply hx2; simpa using hc
          refine ⟨c⁻¹, ?_⟩
          have e : a - c⁻¹ • x = (-c⁻¹) • (x - c • a) := by
            rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hc0, neg_smul, neg_smul, one_smul]; abel
          rw [e]; exact Submodule.smul_of_tower_mem _ _ hc
      obtain ⟨c, hc⟩ := key
      have e : a = c • x + (a - c • x) := by abel
      rw [e]
      refine Submodule.add_mem_sup ?_ hc
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x)
  obtain ⟨x, hxm, hle⟩ := hx
  set I := Ideal.span {x}
  have hstep : ∀ n : ℕ, m ≤ I ⊔ m ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc m ≤ I ⊔ m ^ 2 := hle
        _ = I ⊔ m * m := by rw [pow_two]
        _ ≤ I ⊔ m * (I ⊔ m ^ (n + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
        _ = I ⊔ (m * I ⊔ m ^ (n + 1 + 1)) := by rw [Ideal.mul_sup, ← pow_succ']
        _ ≤ I ⊔ m ^ (n + 1 + 1) := sup_le (le_sup_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
  obtain ⟨n, hn⟩ := hnil
  have hmI : m ≤ I := by
    have := hstep n
    rwa [pow_succ, hn, zero_mul, Ideal.zero_eq_bot, sup_bot_eq] at this
  have hIm : I ≤ m := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  exact ⟨⟨x, le_antisymm hmI hIm⟩⟩

end GlobalTheory.LocalTangent
