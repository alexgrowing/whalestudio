import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFormsGlOfOpenLevelInductionStatement
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviCT

theorem exists_finset_eq_zero {K : Type} (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V] :
    ∃ s : Finset K, ∀ w ∈ V, (∀ k ∈ s, w k = 0) → w = 0 := by
  classical
  let ev : K → (V →ₗ[ℂ] ℂ) := fun k => (LinearMap.proj k).comp V.subtype
  let f : Finset K → Submodule ℂ V := fun s => ⨅ k ∈ s, LinearMap.ker (ev k)
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min (Set.range f) ⟨_, ⟨∅, rfl⟩⟩
  have hle : ∀ k, f s ≤ LinearMap.ker (ev k) := fun k => by
    by_contra hk
    refine hmin (f (insert k s)) ⟨_, rfl⟩ (lt_of_le_of_ne ?_ fun heq => hk ?_)
    · exact le_iInf₂ fun j hj => iInf₂_le j (Finset.mem_insert_of_mem hj)
    · rw [← heq]; exact iInf₂_le k (Finset.mem_insert_self _ _)
  refine ⟨s, fun w hw h0 => funext fun k => ?_⟩
  have hmem : (⟨w, hw⟩ : V) ∈ f s := by
    simp only [f, Submodule.mem_iInf]
    intro j hj
    exact h0 j hj
  exact hle k hmem

def slices {M₁ M₂ : Type} (V₁ : Submodule ℂ (M₁ → ℂ)) (V₂ : Submodule ℂ (M₂ → ℂ)) : Submodule ℂ (M₁ × M₂ → ℂ) where
  carrier := {F | (∀ m₂, (fun m₁ => F (m₁, m₂)) ∈ V₁) ∧ ∀ m₁, (fun m₂ => F (m₁, m₂)) ∈ V₂}
  add_mem' ha hb := ⟨fun m₂ => V₁.add_mem (ha.1 m₂) (hb.1 m₂), fun m₁ => V₂.add_mem (ha.2 m₁) (hb.2 m₁)⟩
  zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
  smul_mem' c _ hF := ⟨fun m₂ => V₁.smul_mem c (hF.1 m₂), fun m₁ => V₂.smul_mem c (hF.2 m₁)⟩

theorem finiteDimensional_slices {M₁ M₂ : Type} (V₁ : Submodule ℂ (M₁ → ℂ)) (V₂ : Submodule ℂ (M₂ → ℂ))
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] : FiniteDimensional ℂ (slices V₁ V₂) := by
  obtain ⟨s, hs⟩ := exists_finset_eq_zero V₂
  let T : slices V₁ V₂ →ₗ[ℂ] (s → V₁) :=
    { toFun := fun F j => ⟨fun m₁ => F.1 (m₁, j.1), F.2.1 j.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T fun F G hFG => Subtype.ext (funext fun p => ?_)
  have h := hs (fun m₂ => F.1 (p.1, m₂) - G.1 (p.1, m₂)) (V₂.sub_mem (F.2.2 p.1) (G.2.2 p.1)) fun k hk => by
    have := congrArg (fun u : s → V₁ => (u ⟨k, hk⟩).1 p.1) hFG
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, sub_self]
  exact sub_eq_zero.1 (congrFun h p.2)

end GlobalTheory.LeviCT

open GlobalTheory.LeviCT in

theorem GlobalTheory.LeviCT.finiteDimensional_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ a' : ℕ, a' < a → ∀ (L' : Subgroup (GL (Fin a') (Af E))), IsOpen (L' : Set (GL (Fin a') (Af E))) → ∀ W' : Submodule ℂ (Kinf E a' → ℂ), FiniteDimensional ℂ W' → ∀ X' : Set (Module.End ℂ (Sm E a') → ℂ), X'.Finite → ∀ N' : ℕ, FiniteDimensional ℂ (Submodule.span ℂ (GlobalTheory.HCF.formsGL E a' L' W' X' N'))) → ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ (r : ℕ), 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun φ : Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N) => fun m : {m : GA E a // (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0)} => ∫ x in 𝓕, φ.1.1 (unip x * (m.1 * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ)) := by
  intro E _ _ _ a hind L hL W hW X hX N r h0 hra _ _ μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨V₁, hV₁, h₁⟩ := GlobalTheory.T.finiteDimensional_forms_gl_of_open_level E a hind L hL W hW X hX N r h0 hra μ 𝓕 hμ h𝓕 h1 t κ
  obtain ⟨V₂, hV₂, h₂⟩ := GlobalTheory.T.finiteDimensional_forms_gl_of_open_level_induction E a hind L hL W hW X hX N r h0 hra μ 𝓕 hμ h𝓕 h1 t κ
  let blocks : {m : GA E a // ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0} → GA E r × GA E (a - r) :=
    fun m => Classical.choose (GlobalTheory.LeviGA.exists_blkGL hra.le m.1 m.2)
  have hb : ∀ m, GlobalTheory.LeviGA.blkGL hra.le (blocks m) = m.1 := fun m =>
    Classical.choose_spec (GlobalTheory.LeviGA.exists_blkGL hra.le m.1 m.2)
  haveI := finiteDimensional_slices V₁ V₂
  refine Submodule.finiteDimensional_of_le (S₂ := (slices V₁ V₂).map (LinearMap.funLeft ℂ ℂ blocks))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ, rfl⟩
  refine ⟨fun p => ∫ x in 𝓕, φ.1.1 (unip x * (GlobalTheory.LeviGA.blkGL hra.le p * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ,
    ⟨fun m₂ => h₁ φ.1 φ.2 m₂, fun m₁ => h₂ φ.1 φ.2 m₁⟩, ?_⟩
  funext m
  simp only [LinearMap.funLeft_apply, hb]
