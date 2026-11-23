import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.TransportH2

variable {R : Type} [CommRing R] {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ]
  [TopologicalSpace Γ] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem apply_symm' (i : G ≃ₜ* Γ) (y : Γ) : i (i.symm y) = y := i.apply_symm_apply y

theorem symm_apply' (i : G ≃ₜ* Γ) (x : G) : i.symm (i x) = x := i.symm_apply_apply x

noncomputable def cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Z2 rho ≃ₗ[R] Z2 (rho.comp i.toMulEquiv.toMonoidHom) :=
  { restrictCocycles2 rho i.toMulEquiv.toMonoidHom i.continuous with
    invFun := fun f => ⟨fun p => f.1 (i.symm p.1, i.symm p.2),
      f.2.1.comp (i.symm.continuous.prodMap i.symm.continuous), fun g h k => by
        have e := f.2.2 (i.symm g) (i.symm h) (i.symm k)
        have e' : (rho.comp i.toMulEquiv.toMonoidHom) (i.symm g) = rho g := by
          show rho (i (i.symm g)) = rho g
          rw [apply_symm']
        rw [e'] at e
        show rho g (f.1 (i.symm h, i.symm k)) - f.1 (i.symm (g * h), i.symm k) +
          f.1 (i.symm g, i.symm (h * k)) - f.1 (i.symm g, i.symm h) = 0
        rw [map_mul, map_mul]
        exact e⟩
    left_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i (i.symm p.1), i (i.symm p.2)) = f.1 p
      rw [apply_symm', apply_symm']
    right_inv := fun f => by
      apply Subtype.ext; funext p
      show f.1 (i.symm (i p.1), i.symm (i p.2)) = f.1 p
      rw [symm_apply', symm_apply'] }

theorem map_cocycleEquiv (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    ((B2 rho).comap (Z2 rho).subtype).map (cocycleEquiv i rho : Z2 rho →ₗ[R] _) =
      (B2 (rho.comp i.toMulEquiv.toMonoidHom)).comap
        (Z2 (rho.comp i.toMulEquiv.toMonoidHom)).subtype := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨f', hf', rfl⟩
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem rho _).1 hf'
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ i, hc.comp i.continuous, ?_⟩
    funext p
    have e := congrFun hcf (i p.1, i p.2)
    change _ = f'.1 (i p.1, i p.2)
    rw [← e]
    simp [d1]
    rfl
  · intro hf
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hf
    refine ⟨(cocycleEquiv i rho).symm f, (separated_dvr_second_cohomology_mem rho _).2
      ⟨c ∘ i.symm, hc.comp i.symm.continuous, ?_⟩, (cocycleEquiv i rho).apply_symm_apply f⟩
    funext p
    have e := congrFun hcf (i.symm p.1, i.symm p.2)
    change _ = f.1 (i.symm p.1, i.symm p.2)
    rw [← e]
    simp [d1, symm_apply']
    exact congrArg (fun g => rho g (c (i.symm p.2))) (apply_symm' i p.1).symm

theorem natCard_H2_comp (i : G ≃ₜ* Γ) (rho : Representation R Γ M) :
    Nat.card (H2 (rho.comp i.toMulEquiv.toMonoidHom)) = Nat.card (H2 rho) :=
  (Nat.card_congr (Submodule.Quotient.equiv _ _ (cocycleEquiv i rho)
    (map_cocycleEquiv i rho)).toEquiv).symm

end GlobalTheory.TransportH2
