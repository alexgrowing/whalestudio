import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DifferentLatIndex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField GroundTheory.Heights₂.Heights.LowerBoundFree

theorem fg_of_isNzFamily {Em : Type} [Field Em] [NumberField Em] {N : ℕ} {I : Submodule (𝓞 Em) (Fin N → Em)}
    {ρ : ℕ} {v : Fin ρ → Fin N → Em} (hv : IsNzFamily I ρ v) : I.FG := by
  set J := Submodule.span (𝓞 Em) (Set.range v) with hJdef
  have hJ : J.FG := Submodule.fg_span (Set.finite_range v)
  set m := J.toAddSubgroup.relIndex I.toAddSubgroup with hmdef
  have hm : m ≠ 0 := hv.2.2.2
  have hmem : ∀ u ∈ I, m • u ∈ J := by
    intro u hu
    have h := AddSubgroup.nsmul_index_mem (J.toAddSubgroup.addSubgroupOf I.toAddSubgroup) ⟨u, hu⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    exact h
  have : IsNoetherian (𝓞 Em) J := isNoetherian_of_fg_of_noetherian J hJ
  let f : I →ₗ[𝓞 Em] J :=
    { toFun := fun u => ⟨m • (u : Fin N → Em), hmem u u.2⟩
      map_add' := fun a b => by ext1; simp [smul_add]
      map_smul' := fun c a => by ext1; simp [smul_comm] }
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : m • (a : Fin N → Em) = m • (b : Fin N → Em) := congrArg Subtype.val hab
    rw [← Nat.cast_smul_eq_nsmul Em, ← Nat.cast_smul_eq_nsmul Em] at h1
    exact Subtype.ext (smul_right_injective _ (by exact_mod_cast hm) h1)
  exact (Submodule.fg_top I).1 (fg_of_injective (N := ⊤) f hf)

theorem TorusIndex.proof (hA : EigenLatDifferent.Statement) (hB : DifferentLatIndex.Statement) :
    TorusIndex.Statement := by
  intro Em _ _ K _ _ ι hι N I ρ v hv s
  rw [hA Em K ι hι N I (fg_of_isNzFamily hv) s]
  exact hB Em K N I ρ v hv s

end GroundTheory.Heights₂.Heights.NineStatements
