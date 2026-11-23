import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.DifferentLatIndex
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentExtNorm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section IdealLat

variable {F : Type} [Field F] [NumberField F] {N ρ : ℕ}

def idealLat (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) : Submodule (𝓞 F) (Fin N → F) :=
  Submodule.map (Fintype.linearCombination (𝓞 F) w) (Submodule.pi Set.univ fun _ => a)

theorem linearCombination_injective {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) :
    Function.Injective (Fintype.linearCombination (𝓞 F) w) := by
  have hw' : LinearIndependent (𝓞 F) w := (LinearIndependent.iff_fractionRing (𝓞 F) F).2 hw
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  funext i
  exact Fintype.linearIndependent_iff.1 hw' c (by rwa [Fintype.linearCombination_apply] at hc) i

omit [NumberField F] in
theorem idealLat_toAddSubgroup (w : Fin ρ → Fin N → F) (a : Ideal (𝓞 F)) :
    (idealLat w a).toAddSubgroup = AddSubgroup.map (Fintype.linearCombination (𝓞 F) w).toAddMonoidHom
      (AddSubgroup.pi Set.univ fun _ => a.toAddSubgroup) := by
  ext x
  simp [idealLat, Submodule.mem_pi, AddSubgroup.mem_pi]

theorem idealLat_relIndex {w : Fin ρ → Fin N → F} (hw : LinearIndependent F w) {a b : Ideal (𝓞 F)}
    (hab : a ≤ b) :
    (idealLat w a).toAddSubgroup.relIndex (idealLat w b).toAddSubgroup * Ideal.absNorm b ^ ρ =
      Ideal.absNorm a ^ ρ := by
  rw [idealLat_toAddSubgroup, idealLat_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (linearCombination_injective hw)]
  have h := AddSubgroup.relIndex_mul_index (H := AddSubgroup.pi Set.univ fun _ : Fin ρ => a.toAddSubgroup)
    (K := AddSubgroup.pi Set.univ fun _ : Fin ρ => b.toAddSubgroup) (fun x hx i hi => hab (hx i hi))
  rw [AddSubgroup.index_pi, AddSubgroup.index_pi] at h
  simpa [Ideal.absNorm_eq_index] using h

omit [NumberField F] in

theorem idealLat_smul (w : Fin ρ → Fin N → F) (r : 𝓞 F) (a : Ideal (𝓞 F)) :
    idealLat (fun i => r • w i) a = idealLat w (Ideal.span {r} * a) := by
  ext x
  simp only [idealLat, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => r * c i, fun i => Ideal.mem_span_singleton_mul.2 ⟨c i, hc i, rfl⟩, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro ⟨c, hc, rfl⟩
    choose d hd hdc using fun i => Ideal.mem_span_singleton_mul.1 (hc i)
    refine ⟨d, hd, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← hdc i, smul_smul, mul_comm]

omit [NumberField F] in

theorem idealLat_top (w : Fin ρ → Fin N → F) :
    idealLat w ⊤ = Submodule.span (𝓞 F) (Set.range w) := by
  rw [idealLat, Submodule.pi_top, Submodule.map_top, Fintype.range_linearCombination]

end IdealLat

section DiffLatSpan

variable {Em K : Type} [Field Em] [NumberField Em] [Field K] [NumberField K] {N ρ : ℕ}

omit [NumberField K] in

theorem diffLat_mono (s : Em →+* K) {M M' : Submodule (𝓞 Em) (Fin N → Em)} (h : M ≤ M') :
    diffLat s M ≤ diffLat s M' :=
  Submodule.span_mono (Set.image_mono fun _ ⟨x, hx, y, hy, hu⟩ => ⟨x, hx, y, h hy, hu⟩)

theorem diffLat_span (s : Em →+* K) (w : Fin ρ → Fin N → Em) :
    diffLat s (Submodule.span (𝓞 Em) (Set.range w)) = idealLat (fun a i => s (w a i)) (extDifferent s) := by
  apply le_antisymm
  · rw [diffLat, Submodule.span_le]
    rintro _ ⟨u, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 Em)).1 hy
    refine ⟨fun a => RingOfIntegers.mapRingHom s (x * c a),
      fun a _ => Ideal.mem_map_of_mem _ (Ideal.mul_mem_right _ _ hx), ?_⟩
    funext i
    simp [Fintype.linearCombination_apply, Finset.sum_apply, map_sum, Algebra.smul_def, mul_assoc,
      Finset.mul_sum]
  · rw [idealLat, Submodule.map_le_iff_le_comap]
    intro c hc
    simp only [Submodule.mem_comap, Fintype.linearCombination_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    have key : extDifferent s ≤ (diffLat s (Submodule.span (𝓞 Em) (Set.range w))).comap
        (LinearMap.toSpanSingleton (𝓞 K) _ (fun i => s (w a i))) := by
      rw [extDifferent, Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      apply Submodule.subset_span
      refine ⟨(x : Em) • w a, ⟨x, hx, w a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
      funext i
      simp [Algebra.smul_def]
    exact key (hc a (Set.mem_univ a))

end DiffLatSpan

end GroundTheory.Heights₂.Heights.NineStatements
