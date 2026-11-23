import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordsConjHermitianAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenbergStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem symplOH_skew' (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH; rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)

theorem mixT_heis_incX {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.incX S ξ) f))) 0 =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) *
        heisO ψ S T (d.incX S (ξ' + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.incX S)]
    congr 1
    · congr 1
      have h1 := d.symplOH_incX_incX S ξ' ξ
      have h2 : symplOH S T (d.inc0 S w₀) (d.incX S ξ) = 0 := by
        rw [symplOH_skew', d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ w₀, neg_zero]
      have h3 := symplOH_skew' S T (d.incAdj S y) (d.incX S ξ)
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, h1, h2, h3,
        symplO_eq_two]
      ring
    · congr 1
      abel
  show ∫ ξ' in 𝓕, _ ∂μ = ψ _ * ∫ ξ' in 𝓕, _ ∂μ
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact covolOne_integral_add hμ (fun ξ' => heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0)
    (d.integrandT_periodic hf y w₀) ξ

theorem mixedModelTarget_heisenberg_anisotropic_part {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (f : WO S T → ℂ) (v : WO S T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S v) f) y = heisO ψ S T₀ v (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.inc0 S v) f))) 0 =
      ψ (symplOH S T₀ w₀ v) *
        heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + v)) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.inc0 S)]
    congr 1
    · congr 1
      have h1 := d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ' v
      have h2 : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := by
        rw [HypDec.incAdj_apply]; exact d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v
      have h3 := d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic S w₀ v
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, h1, h2, h3]
      ring
    · congr 1
      abel
  show ∫ ξ' in 𝓕, _ ∂μ = ψ _ * ∫ ξ' in 𝓕, _ ∂μ
  simp_rw [key]
  rw [integral_const_mul]

end GlobalTheory.HeisTarget

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem hasSum_mixT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    HasSum (fun y : Matrix (Fin S.rank) (Fin ρ) D.host.E => d.mixT S ψ μ 𝓕 f (rat y) 0) (f 0) := by
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hg : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) :=
    ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1 f).2 hf
  have h5 := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hμ'⟩ _ hg).2.2.2.2 0
  have hx : (D.host.xi0 : D.host.E) ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let σ : Matrix (Fin S.rank) (Fin ρ) D.host.E ≃ Matrix (Fin S.rank) (Fin ρ) D.host.E :=
    { toFun := fun y => D.host.xi0⁻¹ • y
      invFun := fun y => D.host.xi0 • y
      left_inv := fun y => by simp only [smul_smul, mul_inv_cancel₀ hx, one_smul]
      right_inv := fun y => by simp only [smul_smul, inv_mul_cancel₀ hx, one_smul] }
  rw [← σ.hasSum_iff] at h5
  have e : ∀ y : Matrix (Fin S.rank) (Fin ρ) D.host.E,
      d.mixS S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (rat (σ y)) 0 =
        starRingEnd ℂ (d.mixT S ψ μ 𝓕 f (rat y) 0) := by
    intro y
    show d.mixS S ψ μ' 𝓕' _ (rat (D.host.xi0⁻¹ • y)) 0 = _
    rw [rat_smul, hsw f (rat y)]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger]
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f (d.ext0 S 0) = starRingEnd ℂ (f 0) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger]
  simp only [Function.comp_def, e, h0] at h5
  exact Complex.hasSum_conj'.1 h5

theorem heisenbergTarget (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := by
  intro ψ hψ S T T₀ ρ d μ 𝓕 hμ f hf
  exact ⟨fun ξ y => mixT_heis_incX d hμ hf ξ y, fun w₀ y => mixedModelTarget_heisenberg_anisotropic_part d f w₀ y, hasSum_mixT hψ d hμ hf⟩

theorem main : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := heisenbergTarget

end GlobalTheory.HeisTarget

end
