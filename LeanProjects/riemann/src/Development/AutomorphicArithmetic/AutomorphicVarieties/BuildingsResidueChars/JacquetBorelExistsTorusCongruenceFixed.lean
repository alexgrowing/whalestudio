import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetExistsLeviCongruenceFixedOfCharSupport

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_borel_exists_torus_congruence_fixed :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL k)) (γ : (ValueGroupWithZero k)ˣ), γ ≤ 1 → HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    Nontrivial (Jacquet π (unipB k (Fin N))) →
    ∃ y : Jacquet π (unipB k (Fin N)), y ≠ 0 ∧ ∀ t : Fin N → kˣ, (∀ i, valuation k ((t i : k) - 1) < γ) → jacBU π t y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ hnt
  let f := Equiv.sigmaUnique (Fin N) fun _ : Fin N => Fin 1
  have hmono : StrictMono (blk f) := fun a b h => by simpa [blk, f] using h
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k (Fin N)) 1 := by
    rw [EmptyBlocks.unipRad_eq k f hmono]
  let E : Jacquet π (unipRad k f) ≃ₗ[ℂ] Jacquet π (unipB k (Fin N)) := Submodule.quotEquivOfEq _ _ h3
  have hE : ∀ v : V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun _ => rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support hG hZ k N V π s γ hγ hs hχ f E.toEquiv.nontrivial
  refine ⟨E y, E.map_ne_zero_iff.2 hy0, fun t ht => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hγ' : (γ : ValueGroupWithZero k) ≤ 1 := hγ
  have h1 := hy (EmptyBlocks.torusToLevi k f t) fun a i j => by
    rw [EmptyBlocks.val_torusToLevi, Subsingleton.elim i j, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
    exact ht _
  have hv : ∀ i, valuation k (t i : k) = 1 := fun i => by
    have := Valuation.map_one_add_of_lt (valuation k) ((ht i).trans_le hγ')
    rwa [add_sub_cancel] at this
  have hd : deltaHalf k (fun _ : Fin N => Fin 1) (EmptyBlocks.torusToLevi k f t) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => isUnram_absPow k _ _ ?_
    have := (EmptyBlocks.det_torusToLevi k f t a).trans (Fin.prod_univ_one _)
    exact (congrArg (fun u : kˣ => valuation k (u : k)) this).trans (hv _)
  rw [jac_mk, hd, inv_one, Units.val_one, one_smul, EmptyBlocks.leviEmb_torusToLevi] at h1
  have h2 := congrArg E h1
  rw [hE, hE] at h2
  rw [hE, jacBU_mk]
  exact h2
