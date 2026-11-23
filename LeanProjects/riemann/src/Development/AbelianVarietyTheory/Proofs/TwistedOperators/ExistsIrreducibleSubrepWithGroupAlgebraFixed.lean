import Mathlib

namespace GlobalTheory.FixedVec

theorem exists_irreducible_subrep_fixed : ∀ (G G' W : Type) [Group G] [Finite G] [Fintype G']
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (i : G' → G) (c : G' → ℂ) (x : W),
    x ≠ 0 → ∑ g, c g • ρ (i g) x = x → ∃ U : Subrepresentation ρ,
      FiniteDimensional ℂ U.toSubmodule ∧ U.toRepresentation.IsIrreducible ∧
      ∃ y : U.toSubmodule, y ≠ 0 ∧ ∑ g, c g • U.toRepresentation (i g) y = y := by
  intro G G' W _ _ _ _ _ ρ i c x hx hfix
  classical
  let P : Subrepresentation ρ → Prop := fun S =>
    FiniteDimensional ℂ S.toSubmodule ∧ ∃ y ∈ S.toSubmodule, y ≠ 0 ∧ ∑ g, c g • ρ (i g) y = y
  let S0 : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g => ρ g x), by
      intro g v hv
      have hle : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤
          Submodule.span ℂ (Set.range fun g => ρ g x) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
        exact ⟨g * h, by simp [map_mul]⟩
      exact hle (Submodule.mem_map_of_mem hv)⟩
  have hP0 : P S0 :=
    ⟨FiniteDimensional.span_of_finite ℂ (Set.finite_range _), x,
      Submodule.subset_span ⟨1, by simp⟩, hx, hfix⟩
  have hex : ∃ m : ℕ, ∃ S : Subrepresentation ρ, P S ∧ Module.finrank ℂ S.toSubmodule = m :=
    ⟨_, S0, hP0, rfl⟩
  obtain ⟨S, ⟨hSfd, y, hyS, hy0, hyfix⟩, hm⟩ := Nat.find_spec hex
  have hmin : ∀ T : Subrepresentation ρ, P T →
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    intro T hT
    rw [hm]
    exact Nat.find_min' hex ⟨T, hT, rfl⟩
  haveI := hSfd
  let E : S.toSubmodule →ₗ[ℂ] S.toSubmodule := ∑ g, c g • S.toRepresentation (i g)
  have hEapp : ∀ z, E z = ∑ g, c g • S.toRepresentation (i g) z := by
    intro z
    simp [E, LinearMap.sum_apply]
  have hE : ∀ z : S.toSubmodule, ((E z : S.toSubmodule) : W) = ∑ g, c g • ρ (i g) (z : W) := by
    intro z
    rw [hEapp]
    simp [Subrepresentation.toRepresentation]
  have key : ∀ T : Subrepresentation S.toRepresentation, T.toSubmodule ≠ ⊤ →
      ∀ a ∈ T.toSubmodule, a ≠ 0 → E a = a → False := by
    intro T hT a ha ha0 hafix
    let T' : Subrepresentation ρ := ⟨T.toSubmodule.map S.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨S.toRepresentation g v, T.apply_mem_toSubmodule g hv, rfl⟩⟩
    have hPT : P T' := by
      refine ⟨?_, (a : W), ⟨a, ha, rfl⟩, ?_, ?_⟩
      · exact Submodule.finiteDimensional_of_le (S₂ := S.toSubmodule) (by
          rintro _ ⟨v, -, rfl⟩
          exact v.2)
      · intro h
        exact ha0 (Subtype.ext h)
      · rw [← hE]
        exact congrArg Subtype.val hafix
    have h1 := hmin T' hPT
    have h2 : Module.finrank ℂ T'.toSubmodule = Module.finrank ℂ T.toSubmodule :=
      Submodule.finrank_map_subtype_eq _ _
    have h3 := Submodule.finrank_lt hT
    omega
  let y' : S.toSubmodule := ⟨y, hyS⟩
  have hy'0 : y' ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hy'fix : E y' = y' := Subtype.ext (by rw [hE]; exact hyfix)
  refine ⟨S, hSfd, ?_, y', hy'0, by rw [← hEapp]; exact hy'fix⟩
  haveI : Nontrivial (Subrepresentation S.toRepresentation) :=
    ⟨⊥, ⊤, fun h => by
      have h' : (⊥ : Submodule ℂ S.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
      have hm' : y' ∈ (⊥ : Submodule ℂ S.toSubmodule) := h' ▸ Submodule.mem_top
      exact hy'0 ((Submodule.mem_bot ℂ).1 hm')⟩
  refine ⟨fun T => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hTb, hTt⟩ := hne
  haveI hss : S.toRepresentation.IsSemisimpleRepresentation := by
    rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
    infer_instance
  obtain ⟨T', hc⟩ := exists_isCompl T
  have hsup : T.toSubmodule ⊔ T'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hc.sup_eq_top
  have hinf : T.toSubmodule ⊓ T'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hc.inf_eq_bot
  have hTt' : T.toSubmodule ≠ ⊤ := fun h => hTt (Subrepresentation.toSubmodule_injective h)
  have hT't : T'.toSubmodule ≠ ⊤ := by
    intro h
    apply hTb
    apply Subrepresentation.toSubmodule_injective
    rw [h, inf_top_eq] at hinf
    exact hinf
  have hmemE : ∀ U : Subrepresentation S.toRepresentation, ∀ z ∈ U.toSubmodule,
      E z ∈ U.toSubmodule := by
    intro U z hz
    rw [hEapp]
    exact Submodule.sum_mem _ (fun g _ => Submodule.smul_mem _ _ (U.apply_mem_toSubmodule _ hz))
  have hyin : y' ∈ T.toSubmodule ⊔ T'.toSubmodule := hsup ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hyin
  have hsum : E a + E b = a + b := by rw [← map_add, hab, hy'fix]
  have hd : E a - a ∈ T.toSubmodule ⊓ T'.toSubmodule := by
    refine ⟨Submodule.sub_mem _ (hmemE T a ha) ha, ?_⟩
    have : E a - a = b - E b := by
      rw [sub_eq_sub_iff_add_eq_add, hsum, add_comm]
    rw [this]
    exact Submodule.sub_mem _ hb (hmemE T' b hb)
  rw [hinf, Submodule.mem_bot, sub_eq_zero] at hd
  have hd' : E b = b := by
    have := hsum
    rw [hd] at this
    exact add_left_cancel this
  by_cases ha0 : a = 0
  · have hb0 : b ≠ 0 := by
      intro hb0
      apply hy'0
      rw [← hab, ha0, hb0, add_zero]
    exact key T' hT't b hb hb0 hd'
  · exact key T hTt' a ha ha0 hd

end GlobalTheory.FixedVec
