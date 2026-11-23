import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsExpChart e ex → 0 < ρ → ρ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) → ∃ ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ), IsExpChart ch (fun x v => ex x (P (e x) *ᵥ v)) ∧ (∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ) ∧ ∀ x ∈ ch.source, e x = ρ • ch x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex P ρ hE hρ hρ1 hP hPu
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hE
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  let ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ) :=
    (e.restrOpen _ hSo).transHomeomorph (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0))
  have hch : ∀ x, ch x = (ρ⁻¹ : ℝ) • e x := fun x ↦ rfl
  have hchs : ∀ z, ch.symm z = e.symm (ρ • z) := fun z ↦ by
    show e.symm ((ρ⁻¹ : ℝ)⁻¹ • z) = _
    rw [inv_inv]
  have hsrc : ∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun x ↦ by
    show x ∈ e.source ∩ (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hball : ∀ z : Fin n → ℂ, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    intro z
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hsub : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ρ • z ∈ e.target := fun z hz ↦ by
    rw [htarget]; exact Metric.ball_subset_ball hρ1 ((hball z).2 hz)
  have htgt : ch.target = Metric.ball 0 1 := by
    ext z
    show (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z ∈
      e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    have hz : (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z = ρ • z := by
      show (ρ⁻¹ : ℝ)⁻¹ • z = _
      rw [inv_inv]
    rw [hz]
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, -, h⟩
      rw [e.right_inv h1] at h
      exact (hball z).1 h
    · intro h
      have h2 := hsub z h
      exact ⟨h2, e.map_target h2, by rw [e.right_inv h2]; exact (hball z).2 h⟩
  refine ⟨ch, ⟨htgt, ?_, ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · intro k V _ _ _ B x hB hx hm
    have := hholE k V B x hB hx fun b hb ↦ ((hsrc _).1 (hm hb)).1
    simp only [hch, Pi.smul_apply]
    exact this.const_smul (ρ⁻¹ : ℝ)
  · rw [htgt]
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun z : Fin n → ℂ ↦ ρ • z) hsymmHol Metric.isOpen_ball
      (differentiableOn_id.const_smul ρ) fun z hz ↦ hsub z hz
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun z _ ↦ ?_
    simp only [hchs]
  · intro x hx v w
    simp only [Matrix.mulVec_add]
    exact hadd x ((hsrc x).1 hx).1 _ _
  · rw [htgt]
    have hφ : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ (ρ • zw.1, P (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      refine (differentiableOn_fst.const_smul ρ).prodMk ?_
      refine differentiableOn_pi.2 fun i ↦ ?_
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ ↦ ?_
      exact ((hP i j).comp (differentiableOn_fst.const_smul ρ) fun zw hzw ↦ (hball _).2 hzw.1).mul
        (by fun_prop : Differentiable ℂ fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ zw.2 j).differentiableOn
    have := GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ) hφ
      fun zw hzw ↦ ⟨hsub _ hzw.1, Set.mem_univ _⟩
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun zw hzw ↦ ?_
    dsimp only
    rw [hchs, e.right_inv (hsub _ hzw.1)]
  · intro x hx
    have hxe := (hsrc x).1 hx
    have hhol : IsHolTo Set.univ (fun w ↦ (ex x w).left) := by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ ↦ (e x, w)) hjoint isOpen_univ
        ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w _ ↦ Set.mk_mem_prod (e.map_source hxe.1) (Set.mem_univ w)
      refine GlobalTheory.HolPeriods.isHolTo_congr this fun w _ ↦ ?_
      dsimp only
      rw [e.left_inv hxe.1]
    have hex : IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := ⟨hadd x hxe.1, (htan x hxe.1).1, (htan x hxe.1).2⟩
    have := isExpAt_mulVec H _ Z.t (x.1 ≫ genι Z) g (ex x) (P (e x)) (hPu _ hxe.2) hhol hex
    exact ⟨this.2.1, this.2.2⟩
  · intro x _
    rw [hch, smul_smul, mul_inv_cancel₀ hρ0, one_smul]

end GlobalTheory.ShFam.Hor.LogCh
