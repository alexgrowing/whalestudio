import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EmbeddingTypes

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions nonZeroDivisors

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.smul_bot, sup_bot_eq] at h2
  exact bot_ne_top h2

theorem one_mem_inverse_halfDifferent (D : D7) : (1 : D.host.E) ∈ D.host.AA0 :=
  FractionalIdeal.one_mem_inv_coe_ideal (b_ne_bot D)

theorem normK_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈
      (D.host.ccE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [FractionalIdeal.mem_coeIdeal]
    refine ⟨((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E), ?_, by simp⟩
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    simpa [Host.ccE] using this
  have := FractionalIdeal.mul_mem_mul hN (one_mem_inverse_halfDifferent D)
  rw [mul_one] at this
  exact this

theorem normK_ne_zero (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact D.host.ccK_ne_bot

theorem exists_smul_mem_base_lattice_alt (D : D7) (j : ℕ) (y : (D.sp.W j).V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ (D.sp.W j).L0 :=
  _root_.UpperTheory.Reformulated.B.EmbeddingTypes.exists_smul_mem_base_lattice_alt D j y

theorem exists_smul_mem_latW (D : D7) (j : ℕ) (y : (D.sp.W j).V) :
    ∃ s ∈ (𝓞 D.host.E)⁰, s • y ∈ latW D j := by
  obtain ⟨s, hs, hsy⟩ := exists_smul_mem_base_lattice_alt D j y
  set n : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E)
  have hn : algebraMap (𝓞 D.host.E) D.host.E n = ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    simp [n]
  have hn0 : n ∈ (𝓞 D.host.E)⁰ := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    apply normK_ne_zero D
    rw [← hn, h0, map_zero]
  refine ⟨n * s, mul_mem hn0 hs, ?_⟩
  rw [mul_smul, ← algebraMap_smul D.host.E n, hn]
  exact Submodule.subset_span ⟨_, normK_mem_AA D, s • y, hsy, rfl⟩

instance latW_isLocalized (D : D7) (j : ℕ) :
    IsLocalizedModule (𝓞 D.host.E)⁰ (latW D j).subtype where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : algebraMap (𝓞 D.host.E) D.host.E x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    have e : ∀ v : (D.sp.W j).V, algebraMap (𝓞 D.host.E) (Module.End (𝓞 D.host.E) (D.sp.W j).V) x v =
        algebraMap (𝓞 D.host.E) D.host.E x • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    constructor
    · intro v w h
      rw [e, e] at h
      exact smul_right_injective _ hx0 h
    · intro v
      refine ⟨(algebraMap (𝓞 D.host.E) D.host.E x)⁻¹ • v, ?_⟩
      rw [e, smul_smul, mul_inv_cancel₀ hx0, one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := exists_smul_mem_latW D j y
    exact ⟨(⟨s • y, hsy⟩, ⟨s, hs⟩), rfl⟩
  exists_of_eq {x₁ x₂} h := ⟨1, by rw [one_smul, one_smul]; exact Subtype.ext h⟩

theorem latW_finrank (D : D7) (j : ℕ) :
    Module.finrank (𝓞 D.host.E) (latW D j) = Module.finrank D.host.E (D.sp.W j).V := by
  rw [IsFractionRing.finrank_right_eq (R := 𝓞 D.host.E) (S := D.host.E) (N := (D.sp.W j).V)]
  exact (IsLocalizedModule.finrank_eq (p := (𝓞 D.host.E)⁰) (f := (latW D j).subtype) le_rfl).symm

theorem latW_rank (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) :
    Module.finrank (𝓞 D.host.E) (latW D j) = (D.R.sigW j).1 + (D.R.sigW j).2 := by
  rw [latW_finrank, (D.sp.W j).rank_eq, D.sp.W_rank j hj.1 hj.2]
  have := D.R.m_add_three_le_k
  simp only [Ranks.sigW, Ranks.r]
  omega

end Formalism.L2.Pj
