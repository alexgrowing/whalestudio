import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem upd_congr {J : Type} [DecidableEq J] (p : M →ₗ[R] H) (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0)
    (u : J → M) (j : J) (a b : M) (hab : p a = p b) :
    F (Function.update u j a) = F (Function.update u j b) := by
  have h1 : a = b + (a - b) := by abel
  rw [h1, F.map_update_add, hF (Function.update u j (a - b)) j (by simp [hab]), add_zero]

noncomputable def descend {J : Type} (p : M →ₗ[R] H) (hp : Function.Surjective p)
    (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0) :
    H [⋀^J]→ₗ[R] Q where
  toFun v := F (fun k => Function.surjInv hp (v k))
  map_update_add' := by
    intro _ v j x y
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (Function.surjInv hp x + Function.surjInv hp y)
      (by simp [Function.surjInv_eq hp]), F.map_update_add]
  map_update_smul' := by
    intro _ v j c x
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (c • Function.surjInv hp x)
      (by simp [Function.surjInv_eq hp]), F.map_update_smul]
  map_eq_zero_of_eq' := by
    intro v a b hv hab
    exact F.map_eq_zero_of_eq _ (by simp [hv]) hab

end GlobalTheory.ExtSqKer

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by
  ext k; fin_cases k <;> rfl

theorem congr_two (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp

end GlobalTheory.ExtSqKer

open GlobalTheory.ExtSqKer in

theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
