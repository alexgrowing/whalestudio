import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetHomLeviTgtBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetHomEquivTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationCentralCharDistinctStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellCharacterDistinctStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellIrreducibleSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellMiddleIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL
open scoped TensorProduct

namespace GlobalTheory.IndLineGL

theorem proportional_of_glInd : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ), m + 2 = a + a' → a' < a → ∀ (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) →
    ∀ (P P₁ : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
      (π : Representation ℂ (GL (Fin (a + a')) k) P) (σ₁ : Representation ℂ (GL (Fin m) k) P₁),
      IsSmooth π → Nonempty (π.Equiv (prod₂ (detRep (Fin a) α₀) (detRep (Fin a') β₀))) → σ₁.IsIrreducible →
      ∀ (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin (a + a')) (ξ₁ ξ₂ : kˣ →* ℂˣ)
        (A A' : P →ₗ[ℂ] (GL (Fin (a + a')) k → P₁)),
        IsGLIndMap e π σ₁ ξ₁ ξ₂ A → IsGLIndMap e π σ₁ ξ₁ ξ₂ A' → A = 0 ∨ ∃ c : ℂ, A' = c • A := by
  intro hKP k _ _ _ _ a a' m hm ha α₀ β₀ hαs hβs hαu hβu P P₁ _ _ _ _ π σ₁ _ hπ hσ e ξ₁ ξ₂ A A' hA hA'
  refine GlobalTheory.T.jacquet_hom_leviTgt_bound k _ m e P P₁ π σ₁ ξ₁ ξ₂ ?_ A A' hA hA'
  refine GlobalTheory.T.jacquet_hom_equiv_transfer k _ m e P _ P₁ π _ σ₁ ξ₁ ξ₂ hπ ?_
  rw [prod₂_detRep_eq]
  obtain ⟨N, bb, hbb⟩ := hKP.geometricLemmaFiltration k Bool (Fin 3) (Fin (a + a')) (Two (Fin a) (Fin a'))
    (fun j : Fin 3 => Fin (blk3 m j)) (two (stdSum rfl)) e
  obtain ⟨S, hmono, h0, htop, hstep⟩ := hbb (ℂ ⊗[ℂ] ℂ) (detPair k a a' α₀ β₀) (isSmooth_detPair a a' hαs hβs)
  have hE : ∀ t : Fin N, Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
      (cellFunctor (bb t).nonempty_rows.some (bb t).nonempty_cols.some (detPair k a a' α₀ β₀))) :=
    fun t => hstep t _ _
  refine GlobalTheory.T.filtration_central_char_distinct _ _ N S hmono h0 htop ?_ fun t => ?_
  · intro t t' htt
    have hb : bb t ≠ bb t' := bb.injective.ne htt
    have hcn := GlobalTheory.T.cell_character_distinct k a a' m α₀ β₀ hαu hβu ha (bb t) (bb t') hb
    obtain ⟨t₁, t₂, hne⟩ := hcn
    have hτ : ∀ y, twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹ (torusPt k m t₁ t₂) y =
        ((((deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹ (torusPt k m t₁ t₂) : ℂˣ) : ℂ) *
      ((ξ₁ t₁ * ξ₂ t₂ : ℂˣ) : ℂ)) • y := fun y => by
      rw [twist_apply, leviTgt_torusPt, smul_smul]
    have hcell : ∀ s : Fin N, ∀ y, subQuot (S s.succ) (S s.castSucc) (torusPt k m t₁ t₂) y =
        (cellChar k a a' α₀ β₀ (bb s).1 t₁ t₂ : ℂ) • y := fun s y =>
      smul_of_equiv (hE s).some (GlobalTheory.T.cell_functor_torus_character k a a' m α₀ β₀ (bb s) (bb s).nonempty_rows.some
        (bb s).nonempty_cols.some t₁ t₂) y
    have hne' : (cellChar k a a' α₀ β₀ (bb t).1 t₁ t₂ : ℂ) ≠ cellChar k a a' α₀ β₀ (bb t').1 t₁ t₂ :=
      fun h => hne (Units.val_injective h)
    by_cases h1 : ((((deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹ (torusPt k m t₁ t₂) : ℂˣ) : ℂ) *
      ((ξ₁ t₁ * ξ₂ t₂ : ℂˣ) : ℂ)) = cellChar k a a' α₀ β₀ (bb t).1 t₁ t₂
    · right
      exact ⟨torusPt k m t₁ t₂, _, _, fun h2 => hne' (h1.symm.trans h2), hτ, hcell t'⟩
    · left
      exact ⟨torusPt k m t₁ t₂, _, _, h1, hτ, hcell t⟩
  · refine HomLeOne.of_equiv (hE t).some ?_
    refine GlobalTheory.T.cell_functor_hom_le_one_of_irreducible k hKP a a' m α₀ β₀ hαs hβs P₁ σ₁ hσ ξ₁ ξ₂ (bb t) _ _ ?_
    by_cases hb : (bb t).1 false 0 = (bb t).1 false 2
    · exact GlobalTheory.T.cell_middle_irreducible k hKP a a' m α₀ β₀ hαs hβs hαu hβu (bb t) hb
    · exact GlobalTheory.MidMixedCell.isIrreducible hKP.geometricLemmaFiltration hKP.base.bernsteinZelevinskyFiniteness
        hKP.base.bernsteinUnitaryProductIrreducible k a a' m α₀ β₀ hαs hβs hαu hβu ha (bb t) hb

end GlobalTheory.IndLineGL
