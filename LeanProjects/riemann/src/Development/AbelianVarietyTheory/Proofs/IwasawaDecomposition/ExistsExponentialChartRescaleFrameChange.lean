import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (ρ : ℝ) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ → Metric.ball 0 ρ ⊆ e0.target → (∀ j, HolAlong e0.source fun x => e0 x j) → IsHolTo e0.target (fun z => (e0.symm z).1) → IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) → (∀ x ∈ e0.source, ‖e0 x‖ < ρ → IsExpAt Z.t (x.1 ≫ genι Z) (ex x)) → DifferentiableOn ℂ A (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (A z).det) → ∃ (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex' : ExpMaps Z σ g), IsExpChart e ex' ∧ e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} ∧ (∀ x ∈ e.source, e x = ρ⁻¹ • e0 x) ∧ ∀ x ∈ e.source, ∀ w, ex' x w = ex x (A (e0 x) *ᵥ w) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e0 ex ρ A hρ hball hhol hsymm hjoint hexp hA hdet
  have hss : ∀ z : Fin n → ℂ, (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')).symm z = ρ • z := fun z => by
    simp [Homeomorph.smulOfNeZero, Units.smul_def]
  have hnorm : ∀ z : Fin n → ℂ, ‖ρ • z‖ < ρ ↔ ‖z‖ < 1 := fun z => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact mul_lt_iff_lt_one_right hρ
  let e1 := e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)
  let hs : (Fin n → ℂ) ≃ₜ (Fin n → ℂ) := Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ.ne')
  let e := e1.transHomeomorph hs
  have he_app : ∀ x, e x = ρ⁻¹ • e0 x := fun x => rfl
  have he_symm : ∀ z, e.symm z = e0.symm (ρ • z) := fun z => by
    simp [e, e1, hs, Homeomorph.smulOfNeZero, Units.smul_def]
  have he_src : e.source = e0.source ∩ {x | ‖e0 x‖ < ρ} := by
    ext x
    simp [e, e1]
  have hss' : ∀ z, hs.symm z = ρ • z := hss
  have he_tgt : e.target = Metric.ball 0 1 := by
    ext z
    show z ∈ (e1.transHomeomorph hs).target ↔ _
    rw [OpenPartialHomeomorph.transHomeomorph_target, Set.mem_preimage, hss']
    show ρ • z ∈ (e0.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin n → ℂ) ρ) Metric.isOpen_ball)).target ↔ _
    rw [OpenPartialHomeomorph.trans_target]
    show ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ρ • z ∈ e0.target ↔ _
    rw [mem_ball_zero_iff, mem_ball_zero_iff]
    constructor
    · rintro ⟨h, -⟩
      exact (hnorm z).1 h
    · intro h
      exact ⟨(hnorm z).2 h, hball (mem_ball_zero_iff.2 ((hnorm z).2 h))⟩
  have hsrc : ∀ x ∈ e.source, x ∈ e0.source ∧ ‖e0 x‖ < ρ := fun x hx => by
    rw [he_src] at hx
    exact hx
  refine ⟨e, fun x w => ex x (A (e0 x) *ᵥ w), ⟨he_tgt, ?_, ?_, ?_, ?_, ?_⟩, he_src, fun x _ => he_app x, fun _ _ _ => rfl⟩
  · intro k V _ _ _ B x hB hx hm
    have hd := hhol k V B x hB hx fun b hb => (hsrc _ (hm hb)).1
    refine (hd.const_mul ((ρ⁻¹ : ℝ) : ℂ)).congr fun b _ => ?_
    simp [he_app, Complex.real_smul]
  · rw [he_tgt]
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hsymm Metric.isOpen_ball
      (φ := fun z => ρ • z) ?_ ?_) fun z _ => by rw [he_symm]
    · exact differentiableOn_id.const_smul ρ
    · intro z hz
      exact hball (mem_ball_zero_iff.2 ((hnorm z).2 (mem_ball_zero_iff.1 hz)))
  · intro x hx v w
    obtain ⟨h1, h2⟩ := hsrc x hx
    simp only [Matrix.mulVec_add]
    exact (hexp x h1 h2).1 _ _
  · rw [he_tgt]
    have hmaps : Set.MapsTo (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) (Metric.ball 0 ρ ×ˢ Set.univ) := fun zw hzw =>
      ⟨mem_ball_zero_iff.2 ((hnorm _).2 (mem_ball_zero_iff.1 hzw.1)), trivial⟩
    have hdiff : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ρ • zw.1, A (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      have h1 : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => ρ • zw.1) (Metric.ball 0 1 ×ˢ Set.univ) :=
        differentiableOn_fst.const_smul ρ
      refine h1.prodMk (differentiableOn_pi.2 fun i => ?_)
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ => ?_
      have hij : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => A (ρ • zw.1) i j)
          (Metric.ball 0 1 ×ˢ Set.univ) := by
        have hA2 : DifferentiableOn ℂ (fun z => (Matrix.of.symm (A z) : Fin g → Fin g → ℂ)) (Metric.ball 0 ρ) := hA
        have hL : DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 ρ) :=
          differentiableOn_pi.1 (differentiableOn_pi.1 hA2 i) j
        exact hL.comp h1
          fun zw hzw => (hmaps hzw).1
      exact hij.mul (differentiableOn_pi.1 differentiableOn_snd j)
    refine GlobalTheory.HolPeriods.isHolTo_congr (GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ)
      hdiff hmaps) fun zw hzw => ?_
    have hz : ρ • zw.1 ∈ e0.target := hball (hmaps hzw).1
    simp only [he_symm, e0.right_inv hz]
    rw [he_symm]
  · intro x hx
    obtain ⟨h1, h2⟩ := hsrc x hx
    have hU : IsUnit (A (e0 x)).det := hdet _ (mem_ball_zero_iff.2 h2)
    let k := Matrix.toLinearEquiv' (A (e0 x)) (Matrix.invertibleOfIsUnitDet _ hU)
    have hk : ∀ w, k w = A (e0 x) *ᵥ w := fun _ => rfl
    have hD : ∀ w v, IsDerivAt0 (fun u => (ex x (A (e0 x) *ᵥ u)).left) w v ↔
        IsDerivAt0 (fun u => (ex x u).left) (A (e0 x) *ᵥ w) v := fun w v => by
      simpa only [hk] using GlobalTheory.HolPeriods.isDerivAt0_comp_equiv (fun u => (ex x u).left) k w v
    obtain ⟨-, hT1, hT2⟩ := hexp x h1 h2
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · simp only [hD]
      exact hT1 _
    · obtain ⟨w', hw', hu⟩ := hT2 v hv
      refine ⟨k.symm w', ?_, fun w hw => ?_⟩
      · beta_reduce
        rw [hD, ← hk, k.apply_symm_apply]
        exact hw'
      · beta_reduce at hw
        rw [hD, ← hk] at hw
        rw [← hu _ hw, k.symm_apply_apply]

end GlobalTheory.ShFam.Hor.LogCh
