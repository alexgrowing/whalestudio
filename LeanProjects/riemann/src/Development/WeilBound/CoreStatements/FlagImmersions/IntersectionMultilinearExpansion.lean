import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMultilinearOneSlot

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

open Ii in
theorem intersection_multilinear_expansion : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) [Fintype J] [DecidableEq J] (ℓ : J → HermLine ι) (n : Fin d → J → ℤ), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → II K ι P d (fun k => combLine ℓ (n k)) = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J _ _ ℓ n hP hℓ
  have hsm : ∀ c : J → ℤ, IsSmoothHerm (combLine ℓ c) := fun c => (combLine_smooth_conj_invariant K ι J ℓ c).1 hℓ
  have key : ∀ (c : Fin d → J → ℤ) (k : Fin d) (v : J → ℤ),
      II K ι P d (fun i => combLine ℓ (Function.update c k v i)) =
        ∑ j, (v j : ℝ) * II K ι P d (Function.update (fun i => combLine ℓ (c i)) k (ℓ j)) := by
    intro c k v
    have e : (fun i => combLine ℓ (Function.update c k v i)) =
        Function.update (fun i => combLine ℓ (c i)) k (combLine ℓ v) := by
      funext i
      by_cases h : i = k
      · subst h
        simp
      · simp [Function.update_of_ne h]
    rw [e, intersection_multilinear_one_position II hII K ι P d _ k J ℓ v hP (fun i => hsm _) hℓ]
  let f : MultilinearMap ℤ (fun _ : Fin d => J → ℤ) ℝ :=
    { toFun := fun c => II K ι P d (fun i => combLine ℓ (c i))
      map_update_add' := by
        intro inst c k x y
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, ← Finset.sum_add_distrib, Pi.add_apply, Int.cast_add, add_mul]
      map_update_smul' := by
        intro inst c k a x
        obtain rfl := Subsingleton.elim inst (instDecidableEqFin d)
        simp only [key, Finset.smul_sum, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [zsmul_eq_mul]
        push_cast
        ring }
  have hn : (fun k => n k) = fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ) := by
    funext k
    conv_lhs => rw [← Finset.univ_sum_single (n k)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ext j'
    by_cases h : j' = j
    · subst h
      simp
    · simp [Pi.single_apply, h]
  calc II K ι P d (fun k => combLine ℓ (n k))
      = f (fun k => ∑ j, n k j • (Pi.single j (1 : ℤ) : J → ℤ)) := by
        rw [← hn]
        rfl
    _ = ∑ r : Fin d → J, f (fun k => n k (r k) • (Pi.single (r k) (1 : ℤ) : J → ℤ)) := f.map_sum _
    _ = ∑ w : Fin d → J, (∏ k, (n k (w k) : ℝ)) * II K ι P d (fun k => ℓ (w k)) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [f.map_smul_univ, zsmul_eq_mul, Int.cast_prod]
        congr 1
        show II K ι P d (fun k => combLine ℓ (Pi.single (w k) 1)) = _
        simp only [combLine_single]

end RootFieldNumerics
