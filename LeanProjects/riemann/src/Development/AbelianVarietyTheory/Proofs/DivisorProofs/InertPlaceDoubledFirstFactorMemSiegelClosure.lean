import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecompositionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.InertDblGen

theorem inlD_mem_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv k hk
  obtain ⟨k₁, hk₁, k₂, hk₂, h₁, h₂, rfl⟩ := GlobalTheory.T.inertPlace_stabilizer_two_factor_decomposition F E σ B a a' G X om om' hT v w hv k hk
  rw [map_mul]
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₁ hk₁ h₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := GlobalTheory.T.unitaryToDoubledFirstFactor_bigCell_inertPlace F E σ B a a' G X om om' hT v w hv k₂ hk₂ h₂
  rw [e₁, e₂]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s _ (Or.inr hn₁)) (s _ (Or.inl hp₁)))
    (Subgroup.mul_mem _ (s _ (Or.inr hn₂)) (s _ (Or.inl hp₂)))

end GlobalTheory.InertDblGen
