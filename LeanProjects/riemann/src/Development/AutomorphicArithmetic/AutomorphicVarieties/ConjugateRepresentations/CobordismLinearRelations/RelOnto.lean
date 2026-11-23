import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ImportsVariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.RelFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relOnto :
    UpperTheory.V.Cj.RelOnto := by
  intro hA E _ _ _ a ha σ Ξ Ξ' h hσ q M hM1 hM2 ω ⟨U, uo, uc, hω⟩ dω rω
  obtain ⟨α, a1, a2, a3, a4⟩ := UpperTheory.V.Lit.Geo.g2 E a ha U uo uc Ξ q ω hω dω rω
  obtain ⟨U', -, uo', uc', β, b1, b2, b3⟩ := hA E a ha U uo uc σ Ξ Ξ' h hσ q α a1 a2 a3
  have bL : Lev Ξ' β := ⟨U', uo', uc', b3.2.1⟩
  obtain ⟨β', hβ', hex⟩ := hM2 β bL b1 b2
  obtain ⟨R1, -, -, R4⟩ := UpperTheory.V.Cj.relFacts E a ha σ Ξ Ξ' h hσ q
  obtain ⟨-, -, L, L1, -⟩ := UpperTheory.V.Cj.levSub E a Ξ q
  obtain ⟨-, -, L', L1', -⟩ := UpperTheory.V.Cj.levSub E a Ξ' q
  obtain ⟨B, B1, -⟩ := UpperTheory.V.Cj.exactSub E a Ξ' q
  have dsub : ∀ (Θ : AlgRep E a) (x y : Co Θ q), dCo (smLie Θ) x = 0 → dCo (smLie Θ) y = 0 →
      dCo (smLie Θ) (x - y) = 0 := fun Θ x y hx hy => by
    have e : x - y = (-1 : ℂ) • y + x := by rw [neg_one_smul ℂ y]; abel
    rw [e, dCo_comb, hx, hy, smul_zero, add_zero]
  have hx : Exact Ξ' (β' - β) := (B1 _).1 (by rw [← neg_sub]; exact B.neg_mem ((B1 _).2 hex))
  have r1 : Rel σ h (ω - α) (β' - β) :=
    R4 _ _ ((L1 _).1 (L.sub_mem ((L1 _).2 ⟨U, uo, uc, hω⟩) ((L1 _).2 ⟨U, uo, uc, a1⟩)))
      ((L1' _).1 (L'.sub_mem ((L1' _).2 (hM1 _ hβ').1) ((L1' _).2 bL)))
      (dsub _ _ _ dω a2) (dsub _ _ _ (hM1 _ hβ').2 b1) ⟨U, uo, uc, a4⟩ hx
  have r2 := R1 1 _ _ _ _ r1 ⟨U', uo', uc', b3⟩
  rw [map_one, one_smul, one_smul, sub_add_cancel, sub_add_cancel] at r2
  exact ⟨β', hβ', r2⟩
