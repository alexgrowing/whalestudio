import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_ofFn_prod_apply_of_intertwine {M Wp : Type} [AddCommGroup M] [Module ℂ M]
    (l : M → Wp) :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ M) (g : Fin t → Wp → Wp),
      (∀ k v, l (f k v) = g k (l v)) → ∀ v,
      l ((List.ofFn f).prod v) = List.foldr (fun T h => T h) (l v) (List.ofFn g) := by
  intro t
  induction t with
  | zero => intro f g _ v; simp
  | succ t ih =>
    intro f g h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons, Module.End.mul_apply, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun k v => h k.succ v) v]

theorem qminor_block_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  intro M Wp _ _ _ _ n m E l w Pop hw h u v
  unfold Formalism.REAL.qminor Formalism.FourierDecayAlt.Q.qmF
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := map_ofFn_prod_apply_of_intertwine (l : M → Wp) m
    (fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (w (σ k)) (w k))
    (fun k y => (if id (σ k) = id k then (u - ((k : ℕ) : ℂ)) • y else 0) + Pop (id (σ k)) (id k) y)
    (fun k x => by
      unfold Formalism.REAL.Tm
      by_cases hk : σ k = k
      · simp [hk, h, sub_smul, Nat.cast_smul_eq_nsmul]
      · have : w (σ k) ≠ w k := fun e => hk (hw e)
        simp [hk, this, h]) v
  rw [← key, Module.End.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end GlobalTheory
