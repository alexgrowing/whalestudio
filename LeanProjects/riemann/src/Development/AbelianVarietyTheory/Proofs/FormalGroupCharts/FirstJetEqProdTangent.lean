import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open SqZero TrivSqZeroExt

theorem firstJet_eq_aug_add_sum {R : Type} [CommRing R] {d : ℕ} (a : JetR R (Fin d) 1) :
    a = algebraMap R _ (jetAug R (Fin d) 1 a) +
      ∑ j, algebraMap R _ (dualLift (Pi.single j (1 : R)) a).snd * zR 1 j := by
  let Φ : JetR R (Fin d) 1 →ₐ[R] TrivSqZeroExt R (Fin d → R) :=
    jetLift R (RingHom.ker (fstHom R R (Fin d → R))) (ker_fst_sq _)
      (fun j => inr (Pi.single j 1)) (fun _ => (RingHom.mem_ker).mpr rfl)
  have hΦ : ∀ j, Φ (zR 1 j) = inr (Pi.single j 1) := fun j => jetLift_zR _ _ _ _ j
  have hz : ∀ i j : Fin d, zR (R := R) 1 i * zR 1 j = 0 := fun i j =>
    mul_eq_zero_of_sq (ker_jetAug_pow (R := R) (Fin d) 1) (zR_mem_ker 1 i) (zR_mem_ker 1 j)
  have h₁ : (vecTo (Algebra.ofId R _) (zR 1) hz).comp Φ = AlgHom.id R _ :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, vecTo_single, AlgHom.id_apply]
  have h₂ : (fstHom R R (Fin d → R)).comp Φ = jetAug R (Fin d) 1 :=
    jet_ext fun j => by rw [AlgHom.comp_apply, hΦ, jetAug_zR]; rfl
  have h₃ : ∀ j, (TrivSqZeroExt.map (LinearMap.proj j : (Fin d → R) →ₗ[R] R)).comp Φ =
      dualLift (Pi.single j (1 : R)) := fun j => jet_ext fun i => by
    rw [AlgHom.comp_apply, hΦ, dualLift_zR, map_inr, LinearMap.proj_apply, Pi.single_apply,
      Pi.single_apply]
    simp only [eq_comm]
  conv_lhs => rw [← AlgHom.id_apply (R := R) a, ← h₁, AlgHom.comp_apply, vecTo_apply]
  simp only [← h₂, ← h₃, AlgHom.comp_apply, snd_map, LinearMap.proj_apply]
  rfl

theorem firstJet_eq_prod_tangent : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)),
    IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (ψ : JetR R (Fin d) 1 →ₐ[R] A)
      (e : Fin d → (DualNumber R →ₐ[R] A)), (∀ j, e j (TrivSqZeroExt.inr 1) = ψ (zR 1 j)) →
      spMap ψ ≫ x 1 = ∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G) := by
  intro R _ G _ _ hG d v hv x hx0 hx1 A _ _ ψ e he
  have haug : spMap (jetAug R (Fin d) 1) ≫ x 1 = 1 := by
    have e : jetAug R (Fin d) 1 = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) 1) :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm
    rw [e, ← spMap_comp, Category.assoc, hx0 1, comp_one']
  obtain ⟨c, hc, hcJ, hxc⟩ := (expBij _ hv _ (ker_jetAug_pow (R := R) (Fin d) 1)).2 (x 1)
    (mem_redKer_of_section _ (Algebra.ofId R _) (fun a => (jetAug R (Fin d) 1).commutes a) haug)
  have hs : ∀ j i : Fin d, dualLift (Pi.single j (1 : R)) (c i) =
      inr ((Pi.single j (1 : R) : Fin d → R) i) := fun j => by
    have h₁ := hx1 j
    rw [hxc, comp_lieExp] at h₁
    have h₂ : lieExp v (fun i => (inr ((Pi.single j (1 : R) : Fin d → R) i) : DualNumber R))
        (fun _ => inr_mul_inr _ _ _) = v j := by
      rw [lieExp, Finset.prod_eq_single j]
      · rw [← scaleD_eq, Pi.single_eq_same, scaleD_one, spMap_id]
        exact Category.id_comp _
      · intro i _ hi
        exact epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
          (by rw [Pi.single_eq_of_ne hi, inr_zero]) _
      · exact fun h => absurd (Finset.mem_univ j) h
    have h₃ : ∀ i, dualLift (Pi.single j (1 : R)) (c i) ∈ RingHom.ker (fstD R) := fun i => by
      rw [RingHom.mem_ker, ← AlgHom.comp_apply, fstD_comp_dualLift]
      exact hcJ i
    exact congrFun ((expBij (DualNumber R) hv (RingHom.ker (fstD R)) kerD_sq).1
      (fun i => dualLift (Pi.single j (1 : R)) (c i))
      (fun i => inr ((Pi.single j (1 : R) : Fin d → R) i)) h₃ (fun i => inr_mem_kerD _) _ _
      (h₁.trans h₂.symm))
  have hcz : ∀ i, c i = zR 1 i := fun i => by
    rw [firstJet_eq_aug_add_sum (c i), (hcJ i : jetAug R (Fin d) 1 (c i) = 0), map_zero, zero_add,
      Finset.sum_eq_single i]
    · rw [hs, snd_inr, Pi.single_eq_same, map_one, _root_.one_mul]
    · intro j _ hj
      rw [hs, snd_inr, Pi.single_eq_of_ne hj.symm, map_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [hxc, comp_lieExp, lieExp]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  exact DualNumber.algHom_ext (by rw [epsTo_eps, hcz]; exact (he j).symm)

end GlobalTheory
