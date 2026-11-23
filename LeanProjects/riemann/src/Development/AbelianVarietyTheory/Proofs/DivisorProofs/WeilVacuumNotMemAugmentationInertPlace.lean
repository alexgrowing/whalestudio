import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianInvariantFormInertVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvOfHeisInv
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertVacLag

theorem vac_not_mem_augAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw hvT hmem
  obtain ⟨C, l, hC, hl, hne⟩ := GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum F E σ B a a' G X om om' hT v w hvw hvT
  have hle : augAt om' v ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
    show φ₁ - φ ∈ LinearMap.ker l
    rw [LinearMap.mem_ker, map_sub,
      GlobalTheory.InertVacLag.inv_of_heisInv F E σ B a a' G X om om' hT v w hvw hvT _ C hC l hl g hg φ hφ φ₁ hφ₁ ha, sub_self]
  exact hne (hle hmem)

end GlobalTheory.InertVacLag
end
