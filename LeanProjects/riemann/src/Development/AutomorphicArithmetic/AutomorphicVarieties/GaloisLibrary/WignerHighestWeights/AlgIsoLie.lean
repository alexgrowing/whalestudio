import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MultiHW
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.WtEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HwIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem hw_prod {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ)
    (h : UpperTheory.V.Af.AlgInfChar Ξ τ m) (hgl : Formalism.REAL.GlRel (eEnd Ξ τ)) (ν : Fin a → ℂ) (v : Fin Ξ.d → ℂ)
    (hv : v ≠ 0) (hw : Formalism.REAL.IsHW (eEnd Ξ τ) ν v) (u : ℂ) :
    ∏ k : Fin a, (u - (k : ℂ) + ν k) = (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod := by
  let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
  have hf : ∀ M v, f M v = M *ᵥ v := fun _ _ => rfl
  have h1 := Formalism.REAL.qDetHW _ a (fun i j => f (eL Ξ.dmat τ i j)) ν v hgl hw u
  have h2 : Formalism.REAL.qdet (eL Ξ.dmat τ) u =
      (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
    have h3 := h.2 (u - ((a : ℂ) - 1) / 2)
    rw [sub_add_cancel] at h3
    exact h3
  rw [← map_qdet, h2, hf, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  exact (smul_left_injective ℂ hv h1).symm

theorem UpperTheory.V.AlgRepEndIrreducible.algIsoLie :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
      (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ τ (m τ)) → (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ' τ (m τ)) →
      ∃ T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ), ∀ τ i j v, T (eEnd Ξ τ i j v) = eEnd Ξ' τ i j (T v) := by
  intro E _ _ _ a Ξ Ξ' m h h'
  haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  haveI : Nonempty (Fin Ξ'.d) := ⟨⟨0, Ξ'.pos⟩⟩
  obtain ⟨hM, hS⟩ := algIrr E a Ξ
  obtain ⟨hM', hS'⟩ := algIrr E a Ξ'
  obtain ⟨ν, v, hv, hν⟩ := multiHW _ _ a (eEnd Ξ) hM
  obtain ⟨ν', v', hv', hν'⟩ := multiHW _ _ a (eEnd Ξ') hM'
  obtain rfl : ν = ν' := funext fun τ => wtEq a _ _ (hν τ).2 (hν' τ).2 fun u =>
    (hw_prod Ξ τ _ (h τ) (hM.1 τ) _ v hv (hν τ).1 u).trans
      (hw_prod Ξ' τ _ (h' τ) (hM'.1 τ) _ v' hv' (hν' τ).1 u).symm
  exact hwIso _ _ a (eEnd Ξ) _ (eEnd Ξ') hM hM' hS hS' ν v v' hv hv' (fun τ => (hν τ).1) (fun τ => (hν' τ).1)
