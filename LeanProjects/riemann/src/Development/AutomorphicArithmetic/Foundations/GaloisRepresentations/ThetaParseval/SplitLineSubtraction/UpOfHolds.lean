import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.upOf_holds :
    EmbSplit → WtId → SatId → UpperTheory.Gal.TP.Loc.LiftSatU → UpOf := by
  intro hE hWt hS hLS E _ _ _ n t hn hnt Bs χX χW mX mW U hU lam hl U' hL κ m ψ p hD
  classical
  obtain ⟨hcov, -, hne⟩ := hE E Bs.emb
  choose l' hl'w hl'L using hL.wt
  choose w₀ hw₀ using hcov
  have hn' : 1 ≤ n + t := by omega
  let lam' : (E →+* ℂ) → DomWeight (n + t) := fun τ =>
    if τ = (Bs.emb (w₀ τ)).1 then l' (w₀ τ) else (l' (w₀ τ)).dual
  have key : ∀ τ, (∃ w, τ = (Bs.emb w).1 ∧ lam' τ = l' w) ∨
      ∃ w, τ = ComplexEmbedding.conjugate (Bs.emb w).1 ∧ lam' τ = (l' w).dual := by
    intro τ
    rcases hw₀ τ with h | h
    · exact Or.inl ⟨w₀ τ, h, if_pos h⟩
    · exact Or.inr ⟨w₀ τ, h, if_neg fun h' => hne (w₀ τ) (w₀ τ) (h'.symm.trans h)⟩
  refine ⟨lam', hL.aut, fun τ => ?_, hD.alg, fun τ => ?_, ?_⟩
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact hl'w w
    · rw [h]
      exact GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn' (hl'w w)
  · rcases key τ with ⟨w, rfl, h⟩ | ⟨w, rfl, h⟩
    · rw [h]
      exact (hWt n t _ _ _ _ (hl'L w)).1 _ (fun i => p i _) (hD.m₁ w) fun i => hD.p₁ i w
    · have hd : lam (ComplexEmbedding.conjugate (Bs.emb w).1) = (lam (Bs.emb w).1).dual :=
        GlobalTheory.DefU.hasWeightAt_unique ⟨U, hU⟩ _ (hl _) (GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hl _))
      rw [h, hd]
      exact (hWt n t _ _ _ _ (hl'L w)).2 _ (fun i => p i _) (hD.m₂ w) fun i => hD.p₂ i w
  · intro v hv hκ hψ B hB
    obtain ⟨hX, hW, hk, hc⟩ := hD.loc v hκ hψ
    have h1 := hLS E n (n + t) (by omega) Bs χX χW mX mW _ U U' hU hL v hv hX hW B hB
    rw [Nat.add_sub_cancel_left] at h1
    refine ⟨_, h1, ?_⟩
    exact hS E v n t B _ _ _ (fun i => (((ψ i).val v : ℂˣ) : ℂ)) hk hc
