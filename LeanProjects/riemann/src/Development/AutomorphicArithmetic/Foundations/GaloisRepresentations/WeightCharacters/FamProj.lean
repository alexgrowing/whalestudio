import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famProj_of : EvLem → SumRep → FamProj := by
  intro hEv hSum E _ _ _ a τ W K ν d B hB
  classical
  obtain ⟨S₀, hS₀, hBS₀⟩ := hB.fin
  let S := S₀ ⊓ autU E a
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hBS : ∀ y₁ y₂ v, B y₁ y₂ v ∈ S := fun y₁ y₂ v => ⟨hBS₀ y₁ y₂ v, hB.aut y₁ y₂ v⟩
  obtain ⟨t, ht, hind, hle⟩ := hSum E a S inferInstance fun φ hφ => hφ.2
  have hex : ∀ U : Submodule ℂ (UA E a → ℂ), ∃ p : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ), U ∈ t → (∀ φ, p φ ∈ U) ∧
      (∀ φ ∈ U, p φ = φ) ∧ ∀ V ∈ t, V ≠ U → ∀ φ ∈ V, p φ = 0 := fun U => by
    by_cases hU : U ∈ t
    · obtain ⟨C, hC, hc⟩ := (hind (Finset.mem_coe.2 hU)).symm.exists_isCompl
      refine ⟨U.subtype ∘ₗ Submodule.linearProjOfIsCompl U C hc.symm, fun _ => ⟨fun φ => Subtype.property _, fun φ hφ =>
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc.symm ⟨φ, hφ⟩), fun V hV hne φ hφ => ?_⟩⟩
      have h0 : Submodule.linearProjOfIsCompl U C hc.symm φ = 0 :=
        Submodule.linearProjOfIsCompl_apply_right' hc.symm
          (hC (le_sSup (show V ∈ (t : Set (Submodule ℂ (UA E a → ℂ))) \ {U} from ⟨hV, hne⟩) hφ))
      simp [h0]
    · exact ⟨0, fun h => absurd h hU⟩
  choose p hp using hex
  have key : ∀ φ ∈ S, ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ) := by
    let P : Submodule ℂ (UA E a → ℂ) :=
      { carrier := {φ | ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ)}
        add_mem' := fun h1 h2 => ⟨by simp only [map_add, Finset.sum_add_distrib, h1.1, h2.1], fun U hU x => by
          simp only [map_add, h1.2 U hU x, h2.2 U hU x]⟩
        zero_mem' := ⟨by simp, fun U _ x => by simp⟩
        smul_mem' := fun c φ h => ⟨by simp only [map_smul, ← Finset.smul_sum, h.1], fun U hU x => by
          simp only [map_smul, h.2 U hU x]⟩ }
    refine fun φ hφ => (sSup_le (a := P) fun V hV ψ hψ => ⟨?_, fun U hU x => ?_⟩) (hle hφ)
    · rw [Finset.sum_eq_single_of_mem V hV fun U hU hne => (hp U hU).2.2 V hV hne.symm ψ hψ]
      exact (hp V hV).2.1 ψ hψ
    · have hx := (ht V hV).stable x ψ hψ
      by_cases h : V = U
      · subst h
        rw [(hp V hV).2.1 _ hx, (hp V hV).2.1 _ hψ]
      · rw [(hp U hU).2.2 V hV h _ hx, (hp U hU).2.2 V hV h _ hψ, map_zero]
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ U g, (fun z => p U (Φ z) g) ∈ T := fun T Φ h1 h2 U g =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (LinearMap.proj g ∘ₗ p U ∘ₗ S.subtype)
  refine ⟨t, fun U y₁ y₂ => p U ∘ₗ B y₁ y₂, fun U hU => ⟨ht U hU, ⟨fun y₁ y₂ v => (ht U hU).aut _ ((hp U hU).1 _),
    fun k hk y₁ y₂ v => ?_, fun x y₁ y₂ v => ?_, fun b hb y₁ y₂ v => ?_, fun k x hx y₁ y₂ v g => ?_, fun k x hx y₂ v g => ?_,
    ⟨S.map (p U), inferInstance, fun y₁ y₂ v => ⟨_, hBS y₁ y₂ v, rfl⟩⟩⟩, fun y₁ y₂ v => (hp U hU).1 _⟩,
    fun y₁ y₂ v => (key _ (hBS y₁ y₂ v)).1⟩
  · show RU E a k (p U (B y₁ y₂ v)) = p U (B y₁ y₂ v)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.fix k hk]
  · show RU E a x (p U (B y₁ y₂ v)) = p U (B _ _ _)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.inf x]
  · show p U (B _ y₂ v) = chi ν b • p U (B y₁ y₂ v)
    rw [hB.up b hb, map_smul]
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hx y₁ y₂ v g) U g
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hx y₂ v g) U g

end UpperTheory.Gal.Wt

end
