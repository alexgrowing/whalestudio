import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gam_fg (N l : ℕ) [Fact l.Prime] (hN : 0 < N) : Group.FG (Gam N l) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  exact Subgroup.fg_of_index_ne_zero _

theorem module_finite_z1_padicInt : ∀ (N l w : ℕ) [Fact l.Prime], 0 < N → Module.Finite ℤ_[l] (Z1 N l w) := by
  intro N l w _ hN
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.1 (gam_fg N l hN)
  let t : Set (Gam N l) := insert 1 (s ∪ s⁻¹)
  have ht : t.Finite := (hfin.union hfin.inv).insert 1
  haveI : Finite t := ht.to_subtype
  haveI : Module.Finite ℤ_[l] (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  let L : Z1 N l w →ₗ[ℤ_[l]] (t → MvPolynomial.homogeneousSubmodule (Fin 2) ℤ_[l] w) :=
    { toFun := fun c i => ⟨c.1 i.1, c.2.1 i.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L ((injective_iff_map_eq_zero L).2 fun c hc => ?_)
  have h0 : ∀ γ ∈ t, c.1 γ = 0 := fun γ hγ => congrArg Subtype.val (congrFun hc ⟨γ, hγ⟩)
  apply Subtype.ext
  funext γ
  have hγ : γ ∈ Submonoid.closure (s ∪ s⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, hs]; trivial
  show c.1 γ = 0
  induction hγ using Submonoid.closure_induction with
  | mem x hx => exact h0 x (Set.mem_insert_of_mem _ hx)
  | one => exact h0 1 (Set.mem_insert _ _)
  | mul x y _ _ hx hy => rw [c.2.2 x y, hx, hy, map_zero, add_zero]

end GlobalTheory.KZ.BettiB
