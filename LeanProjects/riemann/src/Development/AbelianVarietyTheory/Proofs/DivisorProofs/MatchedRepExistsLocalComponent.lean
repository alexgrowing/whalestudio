import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepExistsRightTranslationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocRepSplit

theorem locRep : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin (a + a')) (Fv F v)),
      ∃ π : Representation ℂ (GL (Fin (a + a')) (Fv F v)) (Rf.Pi v),
        IsSmooth π ∧ Nonempty (π.Equiv (prod₂ (detRep (Fin a) (chrW X.α t)) (detRep (Fin a') (chrW X.β t)))) ∧
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ₁ = π (GlobalTheory.KSplit.locMat t c h) (Rf.p v φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v t c
  obtain ⟨e, he⟩ := GlobalTheory.T.matched_local_induced_space_iso hKP F E σ B a a' G X om om' R Rf hM v t c
  have hα : IsSmoothChar (chrW X.α t) :=
    (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hM.triple.chars.heckeα v t).1.1
  have hβ : IsSmoothChar (chrW X.β t) :=
    (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hM.triple.chars.heckeβ v t).1.1
  obtain ⟨ρ, hρ, hsm, ⟨E₁⟩⟩ := GlobalTheory.T.induced_rep_exists_right_translation (Fv F v) a a' (chrW X.α t) (chrW X.β t) hα hβ
  let π : Representation ℂ (GL (Fin (a + a')) (Fv F v)) (Rf.Pi v) :=
    { toFun := fun g => e.symm.toLinearMap ∘ₗ ρ g ∘ₗ e.toLinearMap
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [map_mul] }
  have hπ : ∀ g x, π g x = e.symm (ρ g (e x)) := fun _ _ => rfl
  refine ⟨π, ?_, ?_, ?_⟩
  · intro x
    have : {g | π g x = x} = {g | ρ g (e x) = e x} := by
      ext g
      simp only [Set.mem_setOf_eq, hπ]
      exact e.symm_apply_eq
    rw [this]
    exact hsm (e x)
  · refine ⟨(Representation.Equiv.mk e fun g => ?_).trans E₁⟩
    ext x
    simp [hπ]
  · intro h hh φ hφ φ₁ hφ₁ hA
    rw [hπ, LinearEquiv.eq_symm_apply]
    apply Subtype.ext
    funext g
    rw [hρ]
    exact he h hh φ hφ φ₁ hφ₁ hA g

end GlobalTheory.LocRepSplit
