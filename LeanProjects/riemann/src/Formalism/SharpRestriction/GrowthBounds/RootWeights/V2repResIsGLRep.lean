import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repExistsHwv

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_Umon_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨⟨a, b⟩, rfl⟩ := hu; exact hW a b
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem v2rep_isoIn_stable (E : GLOps n K V) (W : Submodule K V) (mu : Fin n → ℤ) :
    IsStableUnderOperators E (isotypicPartIn E W mu) := by
  intro a b x hx
  unfold isotypicPartIn at hx ⊢
  have h : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, hhw, rfl⟩
    exact Submodule.subset_span
      ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, hhw, rfl⟩
  exact h hx

theorem v2rep_iSup_stable (E : GLOps n K V) {ι : Sort*} (p : ι → Submodule K V) (hp : ∀ i, IsStableUnderOperators E (p i)) :
    IsStableUnderOperators E (⨆ i, p i) := by
  intro a b x hx
  exact Submodule.iSup_induction (motive := fun y => E a b y ∈ ⨆ i, p i) p hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (hp i a b y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

def restrictToStableSubmodule (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

theorem v2rep_res_apply (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (a b : Fin n) (x : W) :
    ((restrictToStableSubmodule E W hW a b x : W) : V) = E a b x := rfl

theorem v2rep_res_weightSp (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (mu : Fin n → ℤ) :
    weightSp (restrictToStableSubmodule E W hW) mu = (weightSp E mu).comap W.subtype := by
  ext x
  simp only [weightSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.subtype_apply]
  refine forall_congr' fun a => ?_
  rw [← Submodule.coe_eq_zero, Submodule.coe_sub, Submodule.coe_smul, v2rep_res_apply]
  simp

theorem v2rep_res_isGLRep [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V)
    [FiniteDimensional K W] (hW : IsStableUnderOperators E W) (hw : W ≤ ⨆ ν, weightSp E ν) : IsGLRep (restrictToStableSubmodule E W hW) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := v2rep_comm E hR a b c d (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, v2rep_res_apply]
    rw [h, add_sub_cancel_left]
    congr 1
    · split_ifs <;> simp [v2rep_res_apply]
    · split_ifs <;> simp [v2rep_res_apply]
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · rw [eq_top_iff]
    intro y _
    have h1 := v2rep_graded E W (fun a => hW a a) y y.2 (hw y.2)
    have h2 : (⨆ ν, weightSp E ν ⊓ W) = (⨆ ν, weightSp (restrictToStableSubmodule E W hW) ν).map W.subtype := by
      rw [Submodule.map_iSup]
      refine iSup_congr fun ν => ?_
      rw [v2rep_res_weightSp, Submodule.map_comap_subtype, inf_comm]
    rw [h2] at h1
    obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'

theorem stable_subspace_complete_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : StableSubspaceCompleteReducibility := by
  intro K V _ _ _ _ n E hR W hfd hW hw
  have := hfd
  set W' : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  obtain ⟨P2, hcompl, hP2⟩ := h2 K W n (restrictToStableSubmodule E W hW) (v2rep_res_isGLRep E hR W hW hw)
    (W'.comap W.subtype) (fun a b x hx => hW'st a b x hx)
  have hbot : P2 = ⊥ := by
    by_contra hne
    let Z : Submodule K V := P2.map W.subtype
    have hZW : Z ≤ W := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZW
    have hZst : IsStableUnderOperators E Z := by
      rintro a b _ ⟨y, hy, rfl⟩
      exact ⟨restrictToStableSubmodule E W hW a b y, hP2 a b y hy, rfl⟩
    have hZne : Z ≠ ⊥ := by
      intro h
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h5 : (y : V) ∈ Z := ⟨y, hy, rfl⟩
      rw [h] at h5
      exact hy0 (Subtype.ext h5)
    obtain ⟨mu, v, hvZ, hhw⟩ := v2rep_exists_hwv E hR Z hZst (hZW.trans hw) hZne
    obtain ⟨y, hy, rfl⟩ := hvZ
    have h1 : (y : V) ∈ W' :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, y, y.2, hhw, rfl⟩)
    have h3 : y ∈ (W'.comap W.subtype) ⊓ P2 := ⟨h1, hy⟩
    rw [hcompl.inf_eq_bot] at h3
    have h4 : y = 0 := h3
    exact hhw.1 (by rw [h4]; rfl)
  have htop : W'.comap W.subtype = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  intro x hx
  have : (⟨x, hx⟩ : W) ∈ W'.comap W.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

end Formalism.MainNotions.G.GLWeightTheory
