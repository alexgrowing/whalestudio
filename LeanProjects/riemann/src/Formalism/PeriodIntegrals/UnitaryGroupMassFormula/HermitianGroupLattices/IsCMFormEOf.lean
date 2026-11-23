import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianGroupLattices.AsAlgebraHomEG

noncomputable section

namespace PI.Dv.GLatHermW

open PI.Dv Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem star_cf (hS : StarIsConj K) (T : GoodSet K G) (g : G) : star (cf T g) = cf T g⁻¹ := by
  obtain ⟨σ0, hσ0⟩ := hS
  apply σ0.injective
  rw [hσ0, star_map_cf]

theorem isCM_cf (hS : StarIsConj K) (T : GoodSet K G) (g : G) : IsCM (cf T g) := by
  intro σ
  rw [star_cf hS, star_map_cf]

theorem isCM_add {a b : K} (ha : IsCM a) (hb : IsCM b) : IsCM (a + b) := by
  intro σ
  rw [star_add, map_add, map_add, star_add, ha σ, hb σ]

theorem isCM_zero : IsCM (0 : K) := by
  intro σ
  rw [star_zero, map_zero, star_zero]

theorem isCM_mul {a b : K} (ha : IsCM a) (hb : IsCM b) : IsCM (a * b) := by
  intro σ
  rw [star_mul', map_mul, map_mul, star_mul', ha σ, hb σ]

theorem isCM_sum {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsCM (f i)) :
    IsCM (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isCM_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isCM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isHermE_of (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hH : IsGHerm A ρ h) :
    IsHermE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨h1, h2, fun x y => ?_⟩
  have hinv : ∀ g : G, h (ρ g x) y = h x (ρ g⁻¹ y) := by
    intro g
    have := h3 g x (ρ g⁻¹ y)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  have hl : h ((ρ.asAlgebraHom (eG T)) x) y = ∑ g : G, star (cf T g) * h (ρ g x) y := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hr : h x ((ρ.asAlgebraHom (eG T)) y) = ∑ g : G, cf T g * h x (ρ g y) := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hl, hr]
  calc ∑ g : G, star (cf T g) * h (ρ g x) y = ∑ g : G, cf T g⁻¹ * h x (ρ g⁻¹ y) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [star_cf hS, hinv]
    _ = ∑ g : G, cf T g * h x (ρ g y) :=
        Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

theorem isCMFormE_of (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hC : IsCMForm A ρ h) :
    IsCMFormE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨c1, c2, c3⟩ := hC
  refine ⟨c1, fun i j => ?_, c3⟩
  have he : A.b.repr ((ρ.asAlgebraHom (eG T)) (A.b j)) i =
      ∑ g : G, cf T g * A.b.repr (ρ g (A.b j)) i := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact isCM_sum _ _ fun g _ => isCM_mul (isCM_cf hS T g) (c2 g i j)

theorem glatHerm : PI.Dv.GLatHerm := by
  intro K _ _ _ _ G _ _ T A ρ h hS hH
  exact ⟨isHermE_of T A ρ h hS hH, fun hC => isCMFormE_of T A ρ h hS hC⟩

end PI.Dv.GLatHermW
