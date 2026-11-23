import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.ChebOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.chebFam :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)) (q : ℕ) (g : Fin q → G L Ω) (A : Set (Plc (Lp L))), IsOpen (U : Set (G L Ω)) → A.Finite → ∃ (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L) (B : Fin q → ValuationSubring Ω) (σ : Fin q → G L Ω), Function.Injective v ∧ ∀ j, v j ∉ A ∧ IsPlaceOver (B j) (w j) ∧ IsPlaceOver (B j) (v j) ∧ Dec (F := Lp L) (B j) ≤ (resP L Ω).range ∧ IsFrob (F := L) (B j) (normV (w j)) (σ j) ∧ σ j * (g j)⁻¹ ∈ U := by
  intro L Ω _ _ _ _ _ _ U q g A hU hA
  revert g
  induction q with
  | zero =>
    intro g
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun j => j.elim0⟩
  | succ q ih =>
    intro g
    obtain ⟨v, w, B, σ, hinj, hj⟩ := ih (fun i => g i.castSucc)
    obtain ⟨v0, w0, B0, σ0, h1, h2, h3, h4, h5, h6⟩ :=
      chebOne L Ω U (g (Fin.last q)) (A ∪ Set.range v) hU (hA.union (Set.finite_range v))
    refine ⟨fun i => Fin.lastCases v0 v i, fun i => Fin.lastCases w0 w i,
      fun i => Fin.lastCases B0 B i, fun i => Fin.lastCases σ0 σ i, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hij
      · rfl
      · exact (h1 (Or.inr ⟨_, hij.symm⟩)).elim
      · exact (h1 (Or.inr ⟨_, hij⟩)).elim
      · rw [hinj hij]
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact ⟨fun h => h1 (Or.inl h), h2, h3, h4, h5, h6⟩
      | cast i =>
        simp only [Fin.lastCases_castSucc]
        exact hj i
