import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse

theorem isOpen_posDef_hermitian {X κ : Type} [TopologicalSpace X] [Fintype κ]
    (M : X → Matrix κ κ ℂ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : κ → ℂ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (κ → ℂ) => (dotProduct (star p.2) ((M p.1).mulVec p.2)).re) :=
    Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd))
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : κ → ℂ) 1,
      0 < (dotProduct (star v) ((M x).mulVec v)).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0)).1
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul] at h1
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  have hre : 0 < (dotProduct (star v) ((M x).mulVec v)).re :=
    (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)
  have hstar : star (dotProduct (star v) ((M x).mulVec v)) = dotProduct (star v) ((M x).mulVec v) := by
    conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, (hs x).eq, ← Matrix.dotProduct_mulVec]
  have him : (dotProduct (star v) ((M x).mulVec v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
  exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  have hset : ballDom q = ⋂ τ, {t | (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef} := by
    ext t
    simp [ballDom]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => isOpen_posDef_hermitian _ ?_ fun t => ?_
  · have hm : Continuous fun t : Fin n → ℂ => ballMat q t τ :=
      continuous_matrix fun a b => continuous_apply _
    exact continuous_const.sub (hm.matrix_conjTranspose.matrix_mul hm)
  · exact (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)

theorem exists_inverse : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  intro Ψ _ j j' n q Z G hZ hbij _ _
  have hJ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  obtain ⟨-, Y, hY, hYZ⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof hJ n _ Z
    (isOpen_ballDom q) hZ hbij.injOn
  rw [hbij.image_eq] at hY
  refine ⟨Y, hY, fun t ht => ?_⟩
  obtain ⟨s, hs, hst⟩ := hbij.surjOn ht
  have hYt : Y t = s := by
    rw [← hst]
    exact hYZ s hs
  exact ⟨hYt ▸ hs, by rw [hYt, hst], hYZ t ht⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse
