import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Layers

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem layer_le_succ (k : ℕ) : layer ε E V k ≤ layer ε E V (k + 1) := by
  show layer ε E V k ≤ layer ε E V k ⊔ _
  exact le_sup_left

theorem layer_mono {k l : ℕ} (hkl : k ≤ l) : layer ε E V k ≤ layer ε E V l := by
  exact monotone_nat_of_le_succ (fun k => layer_le_succ (ε := ε) (E := E) (V := V) k) hkl

theorem apply_mem_layer_succ_nc {a b : Fin n} (hab : ε a ≠ ε b) {k : ℕ} {v : M}
    (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  have h1 : (layer ε E V k).map (E a b) ≤ layer ε E V (k + 1) := by
    show _ ≤ layer ε E V k ⊔ ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b)
    exact le_sup_of_le_right (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)))
  exact h1 (Submodule.mem_map_of_mem hv)

theorem layer_le_of_stable {T : Submodule ℂ M} (hVT : V ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) (k : ℕ) : layer ε E V k ≤ T := by
  induction k with
  | zero => exact hVT
  | succ k ih =>
    show layer ε E V k ⊔ _ ≤ T
    refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact hT a b v (ih hv)

theorem layer_le_genSub (k : ℕ) : layer ε E V k ≤ genSub E V := by
  refine layer_le_of_stable (le_sInf fun T hT => hT.1) ?_ k
  intro a b v hv
  simp only [genSub, Submodule.mem_sInf, Set.mem_setOf_eq] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem layer_kStable (hE : IsGlRep E) (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε E (layer ε E V k) := by
  induction k with
  | zero => exact hV
  | succ k ih =>
    intro a b hab
    have key : layer ε E V (k + 1) ≤ (layer ε E V (k + 1)).comap (E a b) := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun v hv => layer_le_succ k (ih a b hab v hv))
        (iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_)
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      rw [Submodule.mem_comap, Submodule.mem_comap]
      have h := congrArg (fun f : Module.End ℂ M => f v) (hE a b c d)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      have h2 : E a b (E c d v) = E c d (E a b v) +
          ((if b = c then E a d else 0) v - (if d = a then E c b else 0) v) := by
        rw [← h]
        abel
      rw [h2]
      refine Submodule.add_mem _ (apply_mem_layer_succ_nc hcd (ih a b hab v hv))
        (Submodule.sub_mem _ ?_ ?_)
      · split_ifs with hbc
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [← hbc, ← hab, h'])) hv
        · simp
      · split_ifs with hda
        · exact apply_mem_layer_succ_nc (fun h' => hcd (by rw [hda, hab]; exact h')) hv
        · simp
    intro v hv
    exact key hv

theorem apply_mem_layer_succ (hE : IsGlRep E) (hV : IsKStableSub ε E V) (a b : Fin n) {k : ℕ}
    {v : M} (hv : v ∈ layer ε E V k) : E a b v ∈ layer ε E V (k + 1) := by
  by_cases hab : ε a = ε b
  · exact layer_le_succ k (layer_kStable hE hV k a b hab v hv)
  · exact apply_mem_layer_succ_nc hab hv

theorem genSub_eq_iSup_layer (hE : IsGlRep E) (hV : IsKStableSub ε E V) :
    genSub E V = ⨆ k, layer ε E V k := by
  have hmono : Monotone (layer ε E V) := monotone_nat_of_le_succ fun k => layer_le_succ k
  refine le_antisymm (sInf_le ⟨le_iSup_of_le 0 le_rfl, fun a b v hv => ?_⟩) (iSup_le layer_le_genSub)
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hv
  exact (le_iSup (layer ε E V) (k + 1)) (apply_mem_layer_succ hE hV a b hk)

theorem finiteDimensional_layer (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (layer ε E V k) := by
  induction k with
  | zero => exact hV
  | succ k ih =>
    show FiniteDimensional ℂ ↥(layer ε E V k ⊔
      ⨆ (a : Fin n) (b : Fin n) (_ : ε a ≠ ε b), (layer ε E V k).map (E a b))
    infer_instance

theorem casimir_genSub (hE : IsGlRep E) {c : ℂ} (hc : ∀ v ∈ V, casimir E v = c • v) :
    ∀ v ∈ genSub E V, casimir E v = c • v := by
  intro v hv
  have hle : genSub E V ≤ LinearMap.ker (casimir E - c • LinearMap.id) := by
    refine sInf_le ⟨fun w hw => ?_, fun a b w hw => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hc w hw, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hw ⊢
      have h := congrArg (fun f : Module.End ℂ M => f w) (casimir_comm hE a b)
      simp only [Module.End.mul_apply] at h
      rw [h, hw, map_smul]
  have h := hle hv
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at h

end Layers

end ReciprocityTheory.ChartRestriction.DS
