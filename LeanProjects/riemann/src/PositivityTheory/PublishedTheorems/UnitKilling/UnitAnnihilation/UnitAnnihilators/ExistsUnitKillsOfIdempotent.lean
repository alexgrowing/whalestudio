import Mathlib

namespace KrullIntersectionUnits.KrullIntersectionLemmas

theorem exists_unit_kills_of_idempotent {A : Type} [CommRing A] (J : Ideal A) (S : Finset A) :
    (∀ x ∈ S, ∃ r ∈ J, r * x = x) → ∃ s : A, s - 1 ∈ J ∧ ∀ x ∈ S, s * x = 0 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨1, by simp, by simp⟩
  · intro x S _ ih h
    obtain ⟨s, hs1, hs2⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    obtain ⟨r, hrJ, hrx⟩ := h x (Finset.mem_insert_self x S)
    refine ⟨s * (1 - r), ?_, ?_⟩
    · have e : s * (1 - r) - 1 = (s - 1) - s * r := by ring
      rw [e]
      exact J.sub_mem hs1 (J.mul_mem_left s hrJ)
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · have e : s * (1 - r) * y = s * (y - r * y) := by ring
        rw [e, hrx, sub_self, mul_zero]
      · have e : s * (1 - r) * y = (1 - r) * (s * y) := by ring
        rw [e, hs2 y hy, mul_zero]

theorem exists_unit_finite_lift {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hf : φ.Finite)
    (J : Ideal A) (hsurj : ∀ b : B, ∃ a : A, b - φ a ∈ Ideal.map φ J) :
    ∃ s : A, s - 1 ∈ J ∧ ∀ b : B, ∃ a : A, φ s * b = φ a := by
  letI : Algebra A B := φ.toAlgebra
  haveI : Module.Finite A B := hf
  let Nr : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have hfg : (⊤ : Submodule A (B ⧸ Nr)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule A (B ⧸ Nr)) ≤ J • (⊤ : Submodule A (B ⧸ Nr)) := by
    intro q _
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective Nr q
    obtain ⟨a, ha⟩ := hsurj b
    have hy : b - φ a ∈ J • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]
      exact ha
    have h0 : Nr.mkQ (φ a) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩
    have e : Nr.mkQ b = Nr.mkQ (b - φ a) := by
      rw [map_sub, h0, sub_zero]
    rw [e]
    have hm := Submodule.mem_map_of_mem (f := Nr.mkQ) hy
    rw [Submodule.map_smul''] at hm
    exact Submodule.smul_mono le_rfl le_top hm
  obtain ⟨s, hsJ, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J _ hfg hle
  refine ⟨s, hsJ, fun b => ?_⟩
  have h1 : Nr.mkQ (s • b) = 0 := by
    rw [map_smul]
    exact hs _ Submodule.mem_top
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨a, ha⟩ := h1
  exact ⟨a, ha.symm⟩

theorem exists_mem_mul_eq_of_mem_pow {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) (x : A)
    (hx : ∀ n : ℕ, x ∈ J ^ n) : ∃ r ∈ J, r * x = x := by
  have h : x ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule A A) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx i
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (I := J) x).mp h
  exact ⟨r, r.2, hr⟩

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] [IsNoetherianRing A] (φ : A →+* B), φ.Finite → ∀ (J : Ideal A), (∀ (b : B), ∃ (a : A), b - DFunLike.coe φ a ∈ Ideal.map φ J) → (∀ (a : A), DFunLike.coe φ a = OfNat.ofNat (nat_lit 0) → ∀ (n : ℕ), a ∈ J ^ n) → ∃ (s : A), s - OfNat.ofNat (nat_lit 1) ∈ J ∧ (∀ (k : A), DFunLike.coe φ k = OfNat.ofNat (nat_lit 0) → s * k = OfNat.ofNat (nat_lit 0)) ∧ ∀ (b : B), ∃ (a : A), DFunLike.coe φ s * b = DFunLike.coe φ a := by
  intro A B _ _ _ φ hf J hsurj hker
  obtain ⟨s1, hs1J, hs1⟩ := exists_unit_finite_lift φ hf J hsurj
  obtain ⟨S, hS⟩ : ∃ S : Finset A, Submodule.span A (S : Set A) = RingHom.ker φ :=
    IsNoetherian.noetherian (RingHom.ker φ)
  have hSk : ∀ x ∈ S, ∃ r ∈ J, r * x = x := by
    intro x hx
    have hxk : x ∈ RingHom.ker φ := by
      rw [← hS]
      exact Submodule.subset_span hx
    exact exists_mem_mul_eq_of_mem_pow J x (hker x (RingHom.mem_ker.mp hxk))
  obtain ⟨s2, hs2J, hs2⟩ := exists_unit_kills_of_idempotent J S hSk
  refine ⟨s1 * s2, ?_, ?_, ?_⟩
  · have e : s1 * s2 - 1 = (s1 - 1) * s2 + (s2 - 1) := by ring
    rw [e]
    exact J.add_mem (J.mul_mem_right s2 hs1J) hs2J
  · intro k hk
    have hle : Submodule.span A (S : Set A) ≤ LinearMap.ker (LinearMap.mulLeft A s2) := by
      rw [Submodule.span_le]
      intro x hx
      show x ∈ LinearMap.ker (LinearMap.mulLeft A s2)
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact hs2 x hx
    have hk' : k ∈ Submodule.span A (S : Set A) := by
      rw [hS]
      exact RingHom.mem_ker.mpr hk
    have h2 := hle hk'
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at h2
    rw [mul_assoc, h2, mul_zero]
  · intro b
    obtain ⟨a, ha⟩ := hs1 b
    refine ⟨s2 * a, ?_⟩
    rw [map_mul, map_mul, ← ha]
    ring

end KrullIntersectionUnits.KrullIntersectionLemmas
