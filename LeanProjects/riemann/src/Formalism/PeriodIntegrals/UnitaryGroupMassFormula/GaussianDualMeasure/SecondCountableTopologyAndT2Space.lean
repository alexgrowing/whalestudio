import Mathlib

open ValuativeRel MeasureTheory

noncomputable section

namespace PI.GI

section Top

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem secondCountableTopology_and_t2Space : SecondCountableTopology F ∧ T2Space F :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  ⟨inferInstance, inferInstance⟩

instance secondCountable : SecondCountableTopology F := (secondCountableTopology_and_t2Space F).1

instance t2Space : T2Space F := (secondCountableTopology_and_t2Space F).2

end Top

section Meas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

example (d : ℕ) : BorelSpace (Fin d → F) := inferInstance

end Meas

section Char

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_mul_integer (x : F) : IsCompact ((fun u => x * u) '' (𝒪[F] : Set F)) := by
  have h : IsCompact (𝒪[F] : Set F) :=
    isCompact_iff_compactSpace.mpr (by exact (inferInstance : CompactSpace 𝒪[F]))
  exact h.image (continuous_const.mul continuous_id)

theorem norm_psi_pow_le (ψ : AddChar F ℂ) (hc : Continuous ψ) (x : F) :
    ∃ C : ℝ, ∀ n : ℕ, ‖ψ x‖ ^ n ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_mul_integer x).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun n => ?_⟩
  have hmem : (n • x) ∈ (fun u => x * u) '' (𝒪[F] : Set F) :=
    ⟨(n : F), natCast_mem _ n, by simp [nsmul_eq_mul, mul_comm]⟩
  have := hC _ hmem
  rwa [AddChar.map_nsmul_eq_pow, norm_pow] at this

theorem norm_psi (ψ : AddChar F ℂ) (hc : Continuous ψ) (x : F) : ‖ψ x‖ = 1 := by
  have key : ∀ z : F, ‖ψ z‖ ≤ 1 := by
    intro z
    by_contra h
    rw [not_le] at h
    obtain ⟨C, hC⟩ := norm_psi_pow_le ψ hc z
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (hC n) (not_le.mpr hn)
  have hmul : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul]; simp
  have h1 := key x
  have h2 := key (-x)
  have hn : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]

end Char

end PI.GI
