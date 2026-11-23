import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRankStatement

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ThK.PolRank
open Module
theorem polarization_rank_le : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hX := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ (X.θ w) (h.herm.sig w) (h.herm.cartan w)
  have hW := fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ (W.θ w) (h.skew.sig w) (h.skew.cartan w)
  choose A hA hAθ using hX
  choose C hC hCθ using hW
  have hfr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [incM_map_piInf, one_smul]; exact hA w
    · rw [incM_map_piInf]; exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb
    (incM F X.J) (incM F W.J) M.co 1 Complex.I A C h.base.cm h.base.std hfr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.T.archActionReadings_compatible GlobalTheory.T.archHeisenbergDerivatives_exist (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist) F E σ n d r s r' s' X W M B.ψ B.emb
    A C Φ h.base.cm h.base.std hfr hAθ hCθ hΦ
  rw [← hr]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')
end GlobalTheory.ThK.PolRank
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_rank_le_dim : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  first | exact @_root_.GlobalTheory.ThK.PolRank.polarization_rank_le | exact _root_.GlobalTheory.ThK.PolRank.polarization_rank_le | (intros; apply _root_.GlobalTheory.ThK.PolRank.polarization_rank_le <;> assumption)
end
