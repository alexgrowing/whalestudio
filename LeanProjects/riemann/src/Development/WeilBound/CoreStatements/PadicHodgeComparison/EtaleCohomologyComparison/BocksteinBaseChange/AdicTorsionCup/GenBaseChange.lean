import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.TmulEqSmulToV

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct

namespace CrystallineSemistableComparison.AdicCoh

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem gen_tmul_smul2 {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℚ_[l]) (a : ℤ_[l]) (y : N) :
    c ⊗ₜ[ℤ_[l]] (a • y) = (c * algebraMap ℤ_[l] ℚ_[l] a) • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
  rw [tmul_smul, ← algebraMap_smul ℚ_[l] a, smul_tmul', smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

theorem gen_smul_zero {N : Type*} [AddCommGroup N] [Module ℤ_[l] N] (c : ℤ_[l]) : c • (0 : N) = 0 := smul_zero c

theorem gen_baseChange {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N']
    (f : N →ₗ[ℤ_[l]] N') (y : N) : f.baseChange ℚ_[l] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] f y :=
  LinearMap.baseChange_tmul _ _ _

theorem gen_sum_smul {N N' : Type*} [AddCommGroup N] [Module ℤ_[l] N] [AddCommGroup N'] [Module ℤ_[l] N'] {r : ℕ}
    (a : Fin r → ℤ_[l]) (e : Fin r → N) (f : N →ₗ[ℤ_[l]] N') (t : Fin r) (g : N') (h1 : f (e t) = g)
    (h2 : ∀ s, s ≠ t → f (e s) = 0) : f (∑ s, a s • e s) = a t • g := by
  rw [map_sum, Finset.sum_eq_single t (fun s _ hs => by rw [map_smul, h2 s hs, smul_zero])
    (fun h => absurd (Finset.mem_univ t) h), map_smul, h1]

theorem gen_span (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0)
    (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) :
    Submodule.span ℚ_[l] (Set.range fun s => M.toV n (extS l hI j hj _ 0 s (gen s))) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨c, x, rfl⟩ := Adic.tmul_surj v
  choose a ha using fun s => hgen s (pullHl l (sch.map (j s)) n 0 x)
  have hx : x = ∑ s, a s • extS l hI j hj _ 0 s (gen s) := by
    refine sum_eq l hI j hj _ 0 _ _ fun t => ?_
    rw [ha t]
    exact (gen_sum_smul a _ _ t _ (extS_self l hI j hj _ 0 t (gen t))
      (fun s hs => extS_ne l hI j hj _ 0 s (gen s) (Ne.symm hs))).symm
  rw [hx, tmul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [gen_tmul_smul2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

theorem gal_step (hI : ZIn) (M : Model l K) {r : ℕ} {Y : Fin r → Scheme.{0}}
    (j : ∀ s, Y s ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q) (hj : IsSum j) (hint : ∀ s, IsIntegral (Y s))
    (hperm : ∀ σ : K.fixingSubgroup, ∃ (π : Equiv.Perm (Fin r)) (θ : ∀ s, Y s ≅ Y (π s)),
      ∀ s, j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = (θ s).hom ≫ j (π s))
    (htrans : ∀ s s', ∃ (σ : K.fixingSubgroup) (θ : Y s ⟶ Y s'),
      j s ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ) = θ ≫ j s')
    (n : ℕ) (gen : ∀ s, Hl l (sch.obj (Y s)) (n : ℤ) 0) (hgen : ∀ s x, ∃ c : ℤ_[l], x = c • gen s) (s s' : Fin r) :
    ∃ (σ : K.fixingSubgroup) (c : ℤ_[l]),
      pullHl l (sch.map (GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ))) n 0
        (extS l hI j hj _ 0 s (gen s)) = c • extS l hI j hj _ 0 s' (gen s') := by
  obtain ⟨σ, θ, hθ⟩ := htrans s' s
  obtain ⟨π, θ', hθ'⟩ := hperm σ
  have hπ : π s' = s := by
    have := hint s'
    obtain ⟨y⟩ := (inferInstance : Nonempty (Y s'))
    by_contra hne
    have e1 := congrArg (fun f : Y s' ⟶ GlobalTheory.Et.geom (PadicAlgCl l) M.q => f y) (hθ.symm.trans (hθ' s'))
    simp only [Scheme.Hom.comp_apply] at e1
    exact Set.disjoint_left.1 (hj.2.2 s (π s') (Ne.symm hne)) ⟨_, rfl⟩ ⟨_, e1.symm⟩
  obtain ⟨c, hc⟩ := hgen s' (pullHl l (sch.map θ) n 0 (gen s))
  refine ⟨σ, c, sum_eq l hI j hj _ 0 _ _ fun t => ?_⟩
  rw [← pull_comp_apply, ← Functor.map_comp]
  obtain rfl | ht := eq_or_ne t s'
  · rw [hθ, Functor.map_comp, pull_comp_apply, extS_self, hc, LinearMap.map_smul, extS_self]
  · have hne : π t ≠ s := fun h => ht (π.injective (h.trans hπ.symm))
    rw [hθ' t, Functor.map_comp, pull_comp_apply, extS_ne l hI j hj _ 0 s _ hne, map_zero, LinearMap.map_smul,
      extS_ne l hI j hj _ 0 _ _ ht]
    exact (gen_smul_zero (N := Hl l (sch.obj (Y t)) n 0) c).symm

end CrystallineSemistableComparison.AdicCoh
