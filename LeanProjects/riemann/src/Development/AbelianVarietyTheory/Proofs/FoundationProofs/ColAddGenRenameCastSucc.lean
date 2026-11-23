import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching.AddColumn

theorem weight_mapDomain (r n : ℕ) (u : Fin r × Fin n →₀ ℕ) :
    (∀ i : Fin n, Finsupp.weight (colW r (n + 1))
        (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) i.castSucc = Finsupp.weight (colW r n) u i) ∧
      Finsupp.weight (colW r (n + 1)) (Finsupp.mapDomain (Prod.map id Fin.castSucc) u) (Fin.last n) = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finsupp.mapDomain_add, map_add, map_add, Pi.add_apply, Pi.add_apply, ha.1, hb.1]
    · rw [Finsupp.mapDomain_add, map_add, Pi.add_apply, ha.2, hb.2]
  | single v k =>
    refine ⟨fun i => ?_, ?_⟩
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply]
    · simp [Finsupp.mapDomain_single, Finsupp.weight_single, colW, Pi.single_apply,
        (Fin.castSucc_lt_last v.2).ne']

theorem colAddGen_rename_castSucc (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n)
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l.castSucc j.castSucc
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename (Option.map (Prod.map id Fin.castSucc)) (colAddGen R l j f) := by
  have e : (colAddGen R (r := r) l.castSucc j.castSucc).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename (Option.map (Prod.map id Fin.castSucc))).comp (colAddGen R (r := r) l j) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    by_cases hv : s = j
    · simp [colAddGen, hv]
    · simp [colAddGen, hv]
  exact DFunLike.congr_fun e f

theorem colAddGen_rename_last (R : Type*) [CommRing R] {r n : ℕ} (l : Fin (n + 1))
    (f : MvPolynomial (Fin r × Fin n) R) :
    colAddGen R l (Fin.last n)
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) =
      rename some (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) := by
  have e : (colAddGen R (r := r) l (Fin.last n)).comp
        (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
      (rename some).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [colAddGen, (Fin.castSucc_lt_last s).ne]
  exact DFunLike.congr_fun e f

theorem add_column : ∀ (r n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → (∀ f ∈ dualWeyl ℂ r n (fun i => ν i.castSucc), rename (Prod.map id Fin.castSucc) f ∈ dualWeyl ℂ r (n + 1) ν) ∧ ∀ (g : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ), rowAct ℂ g (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1)) f) = rename (Prod.map id Fin.castSucc) (rowAct ℂ g f) := by
  intro r n ν hν
  refine ⟨fun f hf => ?_, fun g f => ?_⟩
  · simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf ⊢
    refine ⟨fun d hd => ?_, fun l j hlj => ?_⟩
    · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
      have h := hf.1 hu
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [(weight_mapDomain r n u).2, hν]
      · rw [(weight_mapDomain r n u).1, h]
    · induction j using Fin.lastCases with
      | last => exact colAddGen_rename_last ℂ l f
      | cast j =>
        induction l using Fin.lastCases with
        | last => exact absurd hlj (not_lt.2 (Fin.le_last _))
        | cast l =>
          rw [colAddGen_rename_castSucc, hf.2 l j (Fin.castSucc_lt_castSucc_iff.1 hlj), rename_rename,
            rename_rename]
          rfl
  · have e : (rowAct ℂ g).comp (rename (Prod.map id Fin.castSucc : Fin r × Fin n → Fin r × Fin (n + 1))) =
        (rename (Prod.map id Fin.castSucc)).comp (rowAct ℂ g) := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, s⟩
      simp [rowAct]
    exact DFunLike.congr_fun e f

end GlobalTheory.Branching.AddColumn
