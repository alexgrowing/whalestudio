import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qe19.LiftEquiv :
    Prop :=
    ∀ (Γ X : Type) [inst : Group Γ] [inst_1 : MulAction Γ X],
      (∀ (x : X), Finite ↥(MulAction.stabilizer Γ x)) →
        ∀ (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B),
          Function.Surjective (⇑(Rep.Hom.hom f) : (↑A : Type) → (↑B : Type)) →
            ∀ (φ : X → (↑B : Type)),
              (∀ (g : Γ) (x : X),
                  φ (g • x) = ((B.ρ : Γ → (↑B : Type) →ₗ[ℂ] (↑B : Type)) g : (↑B : Type) → (↑B : Type)) (φ x)) →
                ∃ (ψ : X → (↑A : Type)),
                  (∀ (g : Γ) (x : X),
                      ψ (g • x) = ((A.ρ : Γ → (↑A : Type) →ₗ[ℂ] (↑A : Type)) g : (↑A : Type) → (↑A : Type)) (ψ x)) ∧
                    ∀ (x : X), (Rep.Hom.hom f : (↑A : Type) → (↑B : Type)) (ψ x) = φ x

private theorem UpperTheory.Reformulated.B.Qe19.fixed_lift {Γ : Type} [Group Γ] (H : Subgroup Γ) [Finite H]
    (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B) (hf : Function.Surjective (Rep.Hom.hom f))
    (b : B) (hb : ∀ h ∈ H, B.ρ h b = b) :
    ∃ a : A, (∀ h ∈ H, A.ρ h a = a) ∧ (Rep.Hom.hom f) a = b := by
  classical
  haveI := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hf b
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ k : H, A.ρ k a, ?_, ?_⟩
  · intro h hh
    rw [map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ ?_
    intro k
    simp [map_mul]
  · rw [map_smul, map_sum]
    have h1 : ∀ k : H, (Rep.Hom.hom f) (A.ρ k a) = b := by
      intro k
      rw [Rep.hom_comm_apply, ha, hb k k.2]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.Reformulated.B.Qe19.LiftEquiv := by
  intro Γ X _ _ hfin A B f hf φ hφ
  have h1 : ∀ x : X, ∃ a : A, (∀ h ∈ MulAction.stabilizer Γ x, A.ρ h a = a) ∧
      (Rep.Hom.hom f) a = φ x := by
    intro x
    haveI := hfin x
    refine UpperTheory.Reformulated.B.Qe19.fixed_lift _ A B f hf (φ x) ?_
    intro h hh
    rw [← hφ, MulAction.mem_stabilizer_iff.mp hh]
  choose a ha hfa using h1
  have h2 : ∃ r : X → X, (∀ (g : Γ) (x : X), r (g • x) = r x) ∧ ∀ x, ∃ g : Γ, g • r x = x := by
    refine ⟨fun x => (Quotient.mk (MulAction.orbitRel Γ X) x).out, ?_, ?_⟩
    · intro g x
      have : Quotient.mk (MulAction.orbitRel Γ X) (g • x) = Quotient.mk (MulAction.orbitRel Γ X) x :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g))
      simp only [this]
    · intro x
      have h := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ X) x)).symm
      exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  obtain ⟨r, hr, hg⟩ := h2
  choose s hs using hg
  refine ⟨fun x => A.ρ (s x) (a (r x)), ?_, ?_⟩
  · intro g x
    have hm : (s (g • x))⁻¹ * (g * s x) ∈ MulAction.stabilizer Γ (r x) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hs x, inv_smul_eq_iff, ← hr g x, hs]
    have h3 := congrArg (A.ρ (s (g • x))) (ha (r x) _ hm)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    simp only [hr g x]
    exact h3.symm
  · intro x
    show (Rep.Hom.hom f) (A.ρ (s x) (a (r x))) = φ x
    rw [Rep.hom_comm_apply, hfa, ← hφ, hs]
