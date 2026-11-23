import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem exists_kur_of_actQ_fixed (K : FinExt l) (b : P.R.B) (hb : ∀ g ∈ GK K, P.actQ g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = b := by
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by rw [P.PD_actB]; exact hb g g.2
  exact ⟨_, hc⟩

theorem exists_kur_of_actSt_fixed (K : FinExt l)
    (hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (p : Bst P) (hp : ∀ g ∈ GK K, actSt P g p = p) :
    ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = p := by
  have hC : ∀ b : P.R.B, (∀ g ∈ GK K, actSt P g (C b) = C b) →
      ∃ c : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c = C b := by
    intro b hb
    obtain ⟨c, hc⟩ := exists_kur_of_actQ_fixed P K b fun g hg =>
      C_injective (by rw [← actSt_C]; exact hb g hg)
    exact ⟨c, by rw [Polynomial.algebraMap_apply, hc]⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases h0 : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero h0] at hp ⊢
      exact hC _ hp
    · have hN : ∀ g ∈ GK K, actSt P g (monSt P p) = monSt P p := fun g hg => by
        rw [← monSt_actSt, hp g hg]
      obtain ⟨c, hc⟩ := ih (monSt P p).natDegree (by
        rw [monSt_apply, natDegree_neg, ← hn]; exact natDegree_derivative_lt h0) _ hN rfl
      rw [Polynomial.algebraMap_apply] at hc
      set a := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c with ha
      have hfa : ∀ g ∈ GK K, P.actQ g a = a := fun g hg =>
        C_injective (by rw [← actSt_C, hc]; exact hN g hg)
      obtain ⟨b, hb⟩ := (monSt_eq_zero_iff P (p + C a * X)).mp (by
        rw [map_add, ← hc]; simp)
      have hpb : p = C b - C a * X := by rw [← hb]; ring
      by_cases hc0 : c = 0
      · have : p = C b := by rw [hpb, ha, hc0]; simp
        rw [this] at hp ⊢
        exact hC _ hp
      · exfalso
        set a' := algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c⁻¹ with ha'
        have haa : a' * a = 1 := by rw [ha, ha', ← map_mul, inv_mul_cancel₀ hc0, map_one]
        refine hK (a' * b) fun g hg => ?_
        have h1 := hp g hg
        rw [hpb, map_sub, map_mul, actSt_C, actSt_C, actSt_X, hfa g hg] at h1
        have h2 : P.actQ g b - a * ((kummer P g : ℚ_[l]) • P.tB) = b :=
          C_injective (by rw [map_sub, map_mul]; linear_combination h1)
        have h3 : P.actQ g a' * a = 1 := by
          have := congrArg (P.actQ g) haa
          rwa [map_mul, map_one, hfa g hg] at this
        have h4 : P.actQ g a' = a' := by
          linear_combination a' * h3 - P.actQ g a' * haa
        rw [map_mul, h4]
        linear_combination a' * h2 + ((kummer P g : ℚ_[l]) • P.tB) * haa

theorem isPst_one_of_kummer (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (h : ∀ (K : FinExt l) (b : P.R.B), ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (K : FinExt l) : IsPst P (1 : Representation ℚ_[l] ↥(GK K) ℚ_[l]) := by
  have := nontrivial_B P
  rw [IsPst, rank_self, rank_eq_one_iff]
  have hmem : ((1 : ℚ_[l]) ⊗ₜ[ℚ_[l]] (1 : Bst P)) ∈ Dpst P (1 : Representation ℚ_[l] ↥(GK K) ℚ_[l]) :=
    (mem_Dpst P _).mpr ⟨K, fun g _ => by simp⟩
  refine ⟨toUr P _ ⟨_, hmem⟩, fun h0 => ?_, fun x => ?_⟩
  · have h1 : ((1 : ℚ_[l]) ⊗ₜ[ℚ_[l]] (1 : Bst P)) = 0 := congrArg Subtype.val h0
    have h2 := congrArg (TensorProduct.lid ℚ_[l] (Bst P)) h1
    simp at h2
  · obtain ⟨⟨x, hx⟩, rfl⟩ := (toUr P _).surjective x
    obtain ⟨p, rfl⟩ := (TensorProduct.lid ℚ_[l] (Bst P)).symm.surjective x
    obtain ⟨K', hK'⟩ := (mem_Dpst P _).mp hx
    obtain ⟨c, hc⟩ := exists_kur_of_actSt_fixed P (supExt K K') (h _) p fun g hg => by
      have h1 := hK' ⟨g, GK_le (K' := supExt K K') le_sup_left hg⟩
        (GK_le (K' := supExt K K') le_sup_right hg)
      rw [lid_symm_apply, stRep_tmul] at h1
      simpa using congrArg (TensorProduct.lid ℚ_[l] (Bst P)) h1
    refine ⟨c, ?_⟩
    rw [smul_toUr]
    congr 1
    apply Subtype.ext
    rw [coe_mulD]
    simp [hc]

end GlobalTheory.Pst
