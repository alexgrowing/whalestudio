import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GLw :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → UpperTheory.Reformulated.B.Gr29.Plc L → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) (w : UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GV :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → {V : Type} → (V → UpperTheory.Reformulated.B.Gr29.Plc L) → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {V : Type} (S : V → UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      (v : V) → UpperTheory.Reformulated.B.Gr29.GLw n (S v)

noncomputable def UpperTheory.Reformulated.B.Gr29.atJ :
    {L : Type} →
      [inst : Field L] →
        [inst_1 : NumberField L] →
          (n : ℕ) →
            {q : ℕ} →
              (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) → (j : Fin q) → UpperTheory.Reformulated.B.Gr29.GLw n (w j) →* UpperTheory.Reformulated.B.Gr29.GV n w :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) (j : Fin q) ↦
      MonoidHom.mulSingle (fun (j : Fin q) ↦ UpperTheory.Reformulated.B.Gr29.GLw n (w j)) j

private def UpperTheory.Reformulated.B.Gr29.stab {A P M : Type} [CommRing A] [Group P] [AddCommGroup M]
    [_root_.Module A M] (ρ : Representation A P M) (m : M) : Subgroup P where
  carrier := {g | ρ g m = m}
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a m = m := ha
    have hb' : ρ b m = m := hb
    change ρ (a * b) m = m
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : ρ a m = m := ha
    change ρ a⁻¹ m = m
    have h : ρ a⁻¹ (ρ a m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha'] at h

private theorem UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff {q : ℕ} {G : Fin q → Type} [∀ j, Group (G j)]
    {A M : Type} [CommRing A] [AddCommGroup M] [_root_.Module A M]
    (ρ : Representation A ((j : Fin q) → G j) M) (H : (j : Fin q) → Subgroup (G j)) (m : M) :
    m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      ∀ j : Fin q, m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (MonoidHom.mulSingle G j)) (H j) := by
  have key : m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      Subgroup.pi Set.univ H ≤ UpperTheory.Reformulated.B.Gr29.stab ρ m := Iff.rfl
  rw [key, Subgroup.pi_le_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h k hk
    exact h (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.Reformulated.B.Gr29.mem_pi :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {n q : ℕ} {w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L} {A M : Type}
      [inst_2 : CommRing A] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module A M]
      (ρ : Representation A (UpperTheory.Reformulated.B.Gr29.GV n w) M) (H : (j : Fin q) → Subgroup (UpperTheory.Reformulated.B.Gr29.GLw n (w j)))
      (m : M),
      m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
        ∀ (j : Fin q), m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (UpperTheory.Reformulated.B.Gr29.atJ n w j)) (H j) := by
  intro L _ _ n q w A M _ _ _ ρ H m
  exact UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff (G := fun j : Fin q => UpperTheory.Reformulated.B.Gr29.GLw n (w j)) ρ H m
