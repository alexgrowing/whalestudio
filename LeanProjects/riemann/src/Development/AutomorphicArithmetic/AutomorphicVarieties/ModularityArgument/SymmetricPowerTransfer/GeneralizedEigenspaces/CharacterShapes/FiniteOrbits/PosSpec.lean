import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.TrPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.EigVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Extract

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma mul_of_genEig {P M : Type} [CommSemigroup P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (u : P → Module.End ℂ M) (hu : ∀ p q, u (p * q) = u p * u q) (hc : ∀ p q, Commute (u p) (u q))
    (ψ : P → ℂ) (h : IsGenEig u ψ) (p q : P) : ψ (p * q) = ψ p * ψ q := by
  obtain ⟨v, hv0, hv⟩ := (Tf.eigVec P M u hc ψ).1 h
  have h1 := hv (p * q)
  rw [hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul] at h1
  rw [mul_comm (ψ p)]
  exact (smul_left_injective ℂ hv0 h1).symm

theorem UpperTheory.V.Z.Sym.So.posSpec :
    UpperTheory.V.Z.Sym.So.PosSpec := by
  unfold UpperTheory.V.Z.Sym.So.PosSpec
  intro P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex
  have hcu : ∀ j p q, Commute (u j p) (u j q) := fun j p q => by
    unfold Commute SemiconjBy
    rw [← hu, ← hu, mul_comm]
  have hcw : ∀ p q, Commute (w p) (w q) := fun p q => by
    unfold Commute SemiconjBy
    rw [← hw, ← hw, mul_comm]
  by_cases hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v
  · exact Or.inr hN
  left
  choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)
  obtain ⟨XN, dN, hXN, hdN, htrN⟩ := Tf.trPos P N w hcw
  obtain ⟨j0, v0, hv0, hv0'⟩ := hex
  have hχj0 : χ ∈ XX j0 :=
    (hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)
  have hχN : χ ∉ XN := fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))
  let T : Option J → Finset (P → ℂ) := fun o => Option.elim o XN XX
  let S' : Finset (Σ _ : Option J, P → ℂ) := Finset.univ.sigma T
  let b' : (Σ _ : Option J, P → ℂ) → ℂ := fun k =>
    Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))
  let β' : (Σ _ : Option J, P → ℂ) → P → ℂ := fun k => k.2
  refine Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_
  · rintro ⟨o, ψ⟩ hk p q
    simp only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk
    cases o with
    | none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q
    | some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q
  · intro p
    rw [htr p, htrN p]
    simp only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim,
      Finset.mul_sum, mul_assoc]
    exact add_comm _ _
  · open ComplexOrder in
    · refine (Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'
      · rintro ⟨o, ψ⟩ hk
        simp only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, rfl⟩ := hk
        cases o with
        | none => exact absurd hk1 hχN
        | some j =>
          simp only [b', Option.elim]
          exact mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)
      · simp [S', β', T, hχj0]

end
