import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2.BaseVol

open GlobalTheory.LocFub.TopDens (dens_smul dens_add dens_zero)

variable {n d : ℕ} {J : Type}

theorem pull_bsL_dz (ε : Fin n ≃ Fin d ⊕ J) (a : Fin d) :
    pull (bsL ε) (dz a) = dz (ε.symm (.inl a)) ∧ pull (bsL ε) (dzb a) = dzb (ε.symm (.inl a)) := by
  rw [(pull_dz _ a).1, (pull_dz _ a).2]
  simp [bsL_apply, coordVec, EuclideanSpace.single_apply]

theorem pull_bsL_prod (ε : Fin n ≃ Fin d ⊕ J) (s : Finset (Fin d)) :
    pull (bsL ε) ((∏ a ∈ s, (Complex.I / 2) • sym (a, a) : Ev d) : Alt d) =
      ((∏ a ∈ s, (Complex.I / 2) • sym (ε.symm (.inl a), ε.symm (.inl a)) : Ev n) : Alt n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ih]
    congr 1
    simp [sym, (pull_bsL_dz ε a).1, (pull_bsL_dz ε a).2]

theorem prod_mem (g : J → Fin n) (s : Finset J) :
    ((∏ j ∈ s, (Complex.I / 2) • sym (g j, g j) : Ev n) : Alt n) ∈ ⋀[ℂ]^(2 * s.card) (Fin n ⊕ Fin n → ℂ) := by
  induction s using Finset.induction_on with
  | empty => simpa using SetLike.one_mem_graded (fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Subalgebra.coe_mul, Finset.card_insert_of_notMem ha,
      show 2 * (s.card + 1) = 1 + 1 + 2 * s.card by ring]
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ih
    rw [Subalgebra.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    change dz (g a) * dzb (g a) ∈ _
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ ?_
    · simp [dz, ExteriorAlgebra.exteriorPower]
    · simp [dzb, ExteriorAlgebra.exteriorPower]

theorem dens_pull_bas [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) {T : Finset (Fin (d + d))} (hT : T ≠ Finset.univ) :
    dens (pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = 0 := by
  have hc : T.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
  have hn : n = d + Fintype.card J := by simpa using Fintype.card_congr ε
  have hm : pull (bsL ε) (bas d T) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) ∈
      ⋀[ℂ]^(T.card + 2 * (Finset.univ : Finset J).card) (Fin n ⊕ Fin n → ℂ) := by
    refine SetLike.mul_mem_graded (A := fun i => ⋀[ℂ]^i (Fin n ⊕ Fin n → ℂ)) ?_ (prod_mem _ _)
    rw [bas, ExteriorAlgebra.basis_apply _ T, CxForm.pull, ExteriorAlgebra.map_apply_ιMulti,
      ← exteriorPower.ιMulti_apply_coe]
    exact Subtype.property _
  have := GlobalTheory.PullTop.repr_eq_zero_of_card_ne
    ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv) ⟨_, hm⟩ (S := Finset.univ)
    (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  rw [dens]
  exact div_eq_zero_iff.2 (Or.inl this)

theorem pull_vol_mul [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) :
    pull (bsL ε) (vol d : Alt d) *
      ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n) = (vol n : Alt n) := by
  rw [vol, pull_bsL_prod, ← Subalgebra.coe_mul, vol, ← ε.symm.prod_comp, Fintype.prod_sum_type]

theorem dens_pull_mul_vol : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (α : Alt d), dens (pull (bsL ε) α * ((∏ j : J, (Complex.I / 2) • sym (ε.symm (.inr j), ε.symm (.inr j)) : Ev n) : Alt n)) = dens α := by
  intro n d J _ ε α
  have hα : α ∈ Submodule.span ℂ (Set.range (bas d)) := by rw [(bas d).span_eq]; trivial
  induction hα using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    by_cases hT : T = Finset.univ
    · obtain ⟨c, hc, e⟩ := vol_eq d
      have e' : bas d T = c⁻¹ • (vol d : Alt d) := by rw [e, hT, inv_smul_smul₀ hc]
      rw [e', map_smul, smul_mul_assoc, dens_smul, dens_smul, dens_vol, pull_vol_mul, dens_vol]
    · rw [dens_pull_bas ε hT]
      simp [dens, hT]
  | zero => simp [dens_zero]
  | add x y _ _ hx hy => rw [map_add, add_mul, dens_add, dens_add, hx, hy]
  | smul c x _ hx => rw [map_smul, smul_mul_assoc, dens_smul, dens_smul, hx]

end GlobalTheory.FlagCell2.BaseVol
