import Formalism.GradedWeylDivisibility.StatementB
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_weight_sum {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) :
    ∑ s : Fin n, Finsupp.weight (colW r n) m s = Finsupp.weight (1 : Fin r × Fin n → ℕ) m := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [colW, Pi.single_apply]

theorem lclosedeq_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  classical
  have hS : Set.Finite {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin r × Fin n => ν v.2))).subset ?_
    intro d hd
    have hd' : Finsupp.weight (colW r n) d = ν := hd
    show d ≤ _
    rw [Finsupp.le_def]
    intro v
    have h1 : d v ≤ Finsupp.weight (colW r n) d v.2 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      by_cases hv : v ∈ d.support
      · refine le_trans ?_ (Finset.single_le_sum
          (f := fun u => (d u • colW r n u) v.2) (fun _ _ => Nat.zero_le _) hv)
        simp [colW]
      · have : d v = 0 := by
          by_contra h
          exact hv (Finsupp.mem_support_iff.mpr h)
        rw [this]
        exact Nat.zero_le _
    rw [hd'] at h1
    simpa using h1
  haveI := hS.to_subtype
  haveI hfd : FiniteDimensional ℚ (weightedHomogeneousSubmodule ℚ (colW r n) ν) := by
    rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp
      {d : Fin r × Fin n →₀ ℕ | Finsupp.weight (colW r n) d = ν}).symm
  exact Submodule.finiteDimensional_of_le (fun f hf => (Submodule.mem_inf.mp hf).1)

def lclosedeq_B {σ : Type} (h2 : FockQPos) (h3 : FockQBilin) :
    LinearMap.BilinForm ℚ (MvPolynomial σ ℚ) :=
  LinearMap.mk₂ ℚ fockQ (fun f f' g => (h3 σ f f' g 1).1)
    (fun c f g => by rw [(h3 σ f f g c).2, smul_eq_mul])
    (fun f g g' => by rw [(h2 σ f _).1, (h3 σ g g' f 1).1, (h2 σ g f).1, (h2 σ g' f).1])
    (fun c f g => by rw [(h2 σ f _).1, (h3 σ g g f c).2, (h2 σ g f).1, smul_eq_mul])

theorem closedEqNabla_of (h1 : HWInClosed) (h2 : FockQPos) (h3 : FockQBilin) (h4 : FockQRowDivAdj) :
    ClosedEqNabla := by
  intro r n hn ν hν M hMV hMc hhw
  have hfdV : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := lclosedeq_fd r n ν
  have hfdM : FiniteDimensional ℚ M := Submodule.finiteDimensional_of_le hMV
  let B := lclosedeq_B (σ := Fin r × Fin n) h2 h3
  have hB : ∀ f g, B f g = fockQ f g := fun _ _ => rfl
  let N : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ) :=
    { carrier := {x | x ∈ dualWeyl ℚ r n ν ∧ ∀ g ∈ M, fockQ x g = 0}
      add_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨Submodule.add_mem _ hx hy, fun g hg => ?_⟩
        rw [← hB, map_add, LinearMap.add_apply, hB, hB, hx' g hg, hy' g hg, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by rw [← hB, map_zero, LinearMap.zero_apply]⟩
      smul_mem' := by
        rintro c x ⟨hx, hx'⟩
        refine ⟨Submodule.smul_mem _ c hx, fun g hg => ?_⟩
        rw [← hB, map_smul, LinearMap.smul_apply, hB, hx' g hg, smul_zero] }
  have hNV : N ≤ dualWeyl ℚ r n ν := fun x hx => hx.1
  have hNc : RowDivClosed N := by
    intro a b k f hf
    obtain ⟨hf1, hf2⟩ := hf
    refine ⟨rowDivStable ℚ r n ν a b k f hf1, fun g hg => ?_⟩
    rw [h4, hf2 _ (hMc b a k g hg)]
  have hN : N = ⊥ := by
    by_contra hne
    have hmem := h1 r n hn ν hν N hNV hNc hne
    have h0 := hmem.2 _ hhw
    have hpos := (h2 _ (hw ℚ hn ν) 0).2 (hwNe ℚ r n hn ν)
    linarith
  let BM := B.restrict M
  have hBM : ∀ x y : M, BM x y = fockQ (x : MvPolynomial (Fin r × Fin n) ℚ) y := fun _ _ => rfl
  have key : ∀ x : M, (∀ y : M, BM x y = 0) → x = 0 := by
    intro x hx
    by_contra hne
    have hx0 : (x : MvPolynomial (Fin r × Fin n) ℚ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := (h2 _ (x : MvPolynomial (Fin r × Fin n) ℚ) 0).2 hx0
    have h0 := hx x
    rw [hBM] at h0
    linarith
  have hnd : BM.Nondegenerate := by
    refine ⟨key, fun y hy => key y fun x => ?_⟩
    rw [hBM, (h2 _ _ _).1, ← hBM]
    exact hy x
  apply le_antisymm hMV
  intro f hf
  let φ : Module.Dual ℚ M := (B f).domRestrict M
  let p : M := (BM.toDual hnd).symm φ
  have hp : ∀ g : M, fockQ (p : MvPolynomial (Fin r × Fin n) ℚ) g = fockQ f g := by
    intro g
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) φ g
    exact this
  have hd : f - p ∈ N := by
    refine ⟨Submodule.sub_mem _ hf (hMV p.2), fun g hg => ?_⟩
    rw [← hB, map_sub, LinearMap.sub_apply, hB, hB, ← hp ⟨g, hg⟩, sub_self]
  rw [hN] at hd
  have hfp : f = p := sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp hd)
  rw [hfp]
  exact p.2

end Formalism.GradedWeylDivisibility
