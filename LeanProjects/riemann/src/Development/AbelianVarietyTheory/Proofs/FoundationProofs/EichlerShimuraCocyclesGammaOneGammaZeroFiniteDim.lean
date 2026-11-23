import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem polySlash_one_of_mem (w : ℕ) (p : Polynomial ℂ) (hp : p ∈ Polynomial.degreeLT ℂ (w + 1)) :
    GlobalTheory.HeckeFamilyMatrices.slP w (1 : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  simp [GlobalTheory.HeckeFamilyMatrices.slP]
  rw [Polynomial.mem_degreeLT] at hp
  have hn : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hp
  conv_rhs => rw [p.as_sum_range' (w + 1) hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.smul_X_eq_monomial]

theorem eichlerShimuraCocycle_eq_zero_of_closure (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (z : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) (S : Set Γ)
    (hS : Subgroup.closure S = ⊤) (hz : ∀ s ∈ S, (z : Γ → Polynomial ℂ) s = 0) :
    (z : Γ → Polynomial ℂ) = 0 := by
  obtain ⟨hdeg, hco⟩ := z.2
  have hone : (z : Γ → Polynomial ℂ) 1 = 0 := by
    have h := hco 1 1
    rw [mul_one] at h
    have hid : GlobalTheory.HeckeFamilyMatrices.slP w (GlobalTheory.HeckeFamilyMatrices.mat (1 : Γ)) ((z : Γ → Polynomial ℂ) 1) = (z : Γ → Polynomial ℂ) 1 := by
      have : GlobalTheory.HeckeFamilyMatrices.mat ((1 : Γ) : SL(2, ℤ)) = 1 := by simp [GlobalTheory.HeckeFamilyMatrices.mat]
      rw [this]
      exact polySlash_one_of_mem w _ (hdeg 1)
    rw [hid] at h
    have : (z : Γ → Polynomial ℂ) 1 + (z : Γ → Polynomial ℂ) 1 - (z : Γ → Polynomial ℂ) 1 = 0 := by
      rw [← h]; ring
    simpa using this
  let K : Subgroup Γ :=
    { carrier := {γ | (z : Γ → Polynomial ℂ) γ = 0}
      mul_mem' := by
        intro a b ha hb
        show (z : Γ → Polynomial ℂ) (a * b) = 0
        rw [hco, ha.out, hb.out, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := by
        intro a ha
        show (z : Γ → Polynomial ℂ) a⁻¹ = 0
        have h := hco a a⁻¹
        rw [mul_inv_cancel, hone, ha.out, map_zero, zero_add] at h
        exact h.symm }
  have hle : Subgroup.closure S ≤ K := (Subgroup.closure_le K).2 hz
  rw [hS] at hle
  funext γ
  exact hle (Subgroup.mem_top γ)

theorem eichlerShimuraCocycles_finiteDimensional_of_fg (Γ : Subgroup SL(2, ℤ)) [Group.FG Γ] (w : ℕ) :
    FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w) := by
  obtain ⟨S, hS⟩ := (Group.fg_def).1 (inferInstance : Group.FG Γ)
  haveI : Module.Finite ℂ (Polynomial.degreeLT ℂ (w + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ (w + 1)).symm
  let g : GlobalTheory.HeckeFamilyMatrices.Z1 Γ w →ₗ[ℂ] (S → Polynomial.degreeLT ℂ (w + 1)) :=
    LinearMap.pi fun s => LinearMap.codRestrict (Polynomial.degreeLT ℂ (w + 1))
      ((LinearMap.proj (s : Γ)).comp (GlobalTheory.HeckeFamilyMatrices.Z1 Γ w).subtype) (fun z => z.2.1 s)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 := eichlerShimuraCocycle_eq_zero_of_closure Γ w z (S : Set Γ) hS (fun s hs => by
      have := congrArg Subtype.val (congrFun hz ⟨s, hs⟩)
      exact this)
    exact Subtype.ext h0
  exact Module.Finite.of_injective g hg

theorem lev_fd : ∀ (N l w : ℕ), 0 < N → 0 < l → FiniteDimensional ℂ (GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w) := by
  intro N l w hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (GlobalTheory.HeckeFamilyMatrices.Lev N l).FiniteIndex := by unfold GlobalTheory.HeckeFamilyMatrices.Lev; infer_instance
  haveI : Group.FG (GlobalTheory.HeckeFamilyMatrices.Lev N l) := Subgroup.fg_of_index_ne_zero _
  exact eichlerShimuraCocycles_finiteDimensional_of_fg _ w

end GlobalTheory.KZ.H3
