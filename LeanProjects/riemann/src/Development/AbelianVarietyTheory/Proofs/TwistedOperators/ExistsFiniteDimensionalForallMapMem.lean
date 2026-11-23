import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructureStatement

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.KHomFinite

theorem isKC_Eab_of_sameBlock {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  unfold Eab
  rw [Matrix.single_apply]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd h hcd
  · rfl

theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> first | trivial | exact h.elim

theorem map_mem_hwSub {p q : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (act' : Mat p q →ₗ[ℂ] Module.End ℂ V')
    (φ : V →ₗ[ℂ] V') (hφ : ∀ Z, IsKC Z → ∀ v, φ (act Z v) = act' Z (φ v))
    (μ : Ix p q → ℚ) (v : V) (hv : v ∈ hwSub act μ) : φ v ∈ hwSub act' μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨hw, hhi⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_self a)), ← map_smul, ← map_sub, hw a, map_zero]
  · rw [← hφ _ (isKC_Eab_of_sameBlock (sameBlock_of_posC hab)), hhi a b hab, map_zero]

theorem kStable_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {A B : Submodule ℂ V} (hA : KStable act A)
    (hB : KStable act B) : KStable act (A ⊔ B) := by
  intro X hX w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup (hA X hX y hy) (hB X hX z hz)

theorem exists_kStable_ge {p q : ℕ} (M : GKMod p q) (H : Submodule ℂ M.V)
    (hH : FiniteDimensional ℂ H) :
    ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ H ≤ E ∧ KStable M.act E := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional H).mpr hH
  have key : ∀ t : Finset M.V, ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧
      Submodule.span ℂ (t : Set M.V) ≤ E ∧ KStable M.act E := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · refine ⟨⊥, inferInstance, by simp, ?_⟩
      intro X _ w hw
      rw [Submodule.mem_bot] at hw ⊢
      rw [hw, map_zero]
    · intro x t _ ih
      obtain ⟨E₁, hE₁, hx, hK₁⟩ := M.kfin x
      obtain ⟨E₂, hE₂, ht, hK₂⟩ := ih
      refine ⟨E₁ ⊔ E₂, inferInstance, ?_, kStable_sup hK₁ hK₂⟩
      rw [Finset.coe_insert, Submodule.span_insert]
      exact sup_le_sup ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) ht
  obtain ⟨E, hE, hsE, hK⟩ := key s
  refine ⟨E, hE, ?_, hK⟩
  rw [← hs]
  exact hsE

theorem exists_finiteDimensional_forall_map_mem :
    ∀ (p q : ℕ) (M : GKMod p q), AdmGK M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V, (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ W, φ v ∈ E := by
  intro p q M hM V _ _ act hact W hW hWK hWwt
  suffices key : ∀ n : ℕ, ∀ U : Submodule ℂ V, U ≤ W → KStable act U → Module.finrank ℂ U = n →
      ∃ E : Submodule ℂ M.V, FiniteDimensional ℂ E ∧ ∀ φ : V →ₗ[ℂ] M.V,
        (∀ Z, IsKC Z → ∀ v, φ (act Z v) = M.act Z (φ v)) → ∀ v ∈ U, φ v ∈ E from
    key _ W le_rfl hWK rfl
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih U hUW hUK hn
  have hUfd : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUW
  obtain ⟨hsplit, hhw, -, -⟩ := GlobalTheory.T.glBlock_finiteDim_module_structure p q V act hact U hUfd hUK
    (fun v hv => hWwt v (hUW hv))
  by_cases hU0 : U = ⊥
  · refine ⟨⊥, inferInstance, fun φ _ v hv => ?_⟩
    rw [hU0, Submodule.mem_bot] at hv
    rw [hv, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨μ, v, hvU, hv⟩ := hhw hU0
  set N : Submodule ℂ V := sInf {N | v ∈ N ∧ KStable act N} with hN
  have hNK : KStable act N := by
    intro X hX w hw
    rw [Submodule.mem_sInf] at hw ⊢
    intro N' hN'
    exact hN'.2 X hX w (hw N' hN')
  have hvN : v ∈ N := Submodule.mem_sInf.mpr fun N' hN' => hN'.1
  have hNU : N ≤ U := sInf_le ⟨hvU, hUK⟩
  obtain ⟨U', hU'K, hdisj, hsup⟩ := hsplit N hNU hNK
  have hU'U : U' ≤ U := by
    rw [← hsup]
    exact le_sup_right
  have hvU' : v ∉ U' := by
    intro h
    have hmem : v ∈ N ⊓ U' := ⟨hvN, h⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    exact hv.1 hmem
  have hlt : Module.finrank ℂ U' < n := by
    rw [← hn]
    exact Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne hU'U fun h => hvU' (by rw [h]; exact hvU))
  obtain ⟨E', hE', hE'mem⟩ := ih _ hlt U' (hU'U.trans hUW) hU'K rfl
  obtain ⟨Eμ, hEμ, hle, hEμK⟩ := exists_kStable_ge M (hwSub M.act μ) (hM μ)
  refine ⟨Eμ ⊔ E', inferInstance, fun φ hφ w hw => ?_⟩
  have hNφ : N ≤ Submodule.comap φ Eμ := by
    refine sInf_le ⟨?_, ?_⟩
    · exact hle (map_mem_hwSub act M.act φ hφ μ v hv.2)
    · intro X hX x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [hφ X hX x]
      exact hEμK X hX _ hx
  rw [← hsup] at hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup (hNφ hx) (hE'mem φ hφ y hy)

end GlobalTheory.KHomFinite
