import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.PolRank

open Module

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := Basis.piTensorProduct (fun _ : InfinitePlace F =>
    (MvPolynomial.basisMonomials _ ℂ : Basis _ ℂ (Formalism.BasicNotions.TH.Pol P Q R S)))
  have hb := b.mk_eq_rank
  rw [Cardinal.lift_id, Cardinal.lift_id] at hb
  rw [← hb]
  exact Cardinal.mk_le_aleph0

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}
    (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem rank_pol_le : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
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
