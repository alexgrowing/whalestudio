import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
open IsLocalRing Matrix UpperTheory.V.Hi

private def repsRel {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub)
    (c : ℕ) : Setoid (Ga × Gp) where
  r g h := ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * h * ((u : Ga), b)
  iseqv :=
    { refl := fun g => ⟨1, 1, one_mem _, 1, one_mem _, by simp [Prod.mk_one_one]⟩
      symm := by
        rintro g h ⟨γ, u, hu, b, hb, rfl⟩
        refine ⟨γ⁻¹, u⁻¹, inv_mem hu, b⁻¹, inv_mem hb, ?_⟩
        have : (((u⁻¹ : X.Ub) : Ga), b⁻¹) = ((u : Ga), b)⁻¹ := rfl
        rw [this, map_inv]
        group
      trans := by
        rintro g h k ⟨γ, u, hu, b, hb, rfl⟩ ⟨γ', u', hu', b', hb', rfl⟩
        refine ⟨γ * γ', u' * u, mul_mem hu' hu, b' * b, mul_mem hb' hb, ?_⟩
        have : (((u' * u : X.Ub) : Ga), b' * b) = ((u' : Ga), b') * ((u : Ga), b) := rfl
        rw [this, map_mul]
        group }

theorem UpperTheory.exists_finite_iwahori_doubleCoset_representatives :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (U : Subgroup X.Ub), X.FinLevel U → ∀ c : ℕ, ∃ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) ∧ (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) := by
  intro Γ Ga Gp _ _ _ X U hU c
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).1
  haveI : Finite (Quotient (repsRel X U c)) := by
    refine Finite.of_surjective
      (fun p : s × (X.I.Iw 0 ⧸ (X.I.Iw c).subgroupOf (X.I.Iw 0)) =>
        Quotient.mk (repsRel X U c) ((p.1 : Ga × Gp) * (1, (p.2.out : Gp)))) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.I.Iw c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
      refine ⟨(⟨x, hx⟩, ((⟨b, hb⟩ : X.I.Iw 0) : _ ⧸ _)), ?_⟩
      symm
      refine Quotient.sound ⟨γ, u, hu, ((m : X.I.Iw 0) : Gp)⁻¹, inv_mem (Subgroup.mem_subgroupOf.1 m.2), ?_⟩
      simp only [hm, Subgroup.coe_mul, mul_assoc, Prod.mk_mul_mk, one_mul, mul_inv_cancel, mul_one]
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient (repsRel X U c))
  refine ⟨N, fun i => (e.symm i).out, fun g => ?_, fun i j γ u hu b hb h => ?_⟩
  · obtain ⟨γ, u, hu, b, hb, h⟩ := (repsRel X U c).symm (Quotient.mk_out (s := repsRel X U c) g)
    exact ⟨γ, e (Quotient.mk _ g), u, hu, b, hb, by simpa using h⟩
  · have h1 : Quotient.mk (repsRel X U c) (e.symm j).out = Quotient.mk (repsRel X U c) (e.symm i).out :=
      Quotient.sound ⟨γ, u, hu, b, hb, h⟩
    rw [Quotient.out_eq, Quotient.out_eq] at h1
    exact (e.symm.injective h1).symm
