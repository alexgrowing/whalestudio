import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.AbelianLetters

theorem fderiv_eq_zero_of_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F u G : V → ℂ} {c : ℂ} {z : V}
    (hc : c ≠ 0) (hu : DifferentiableAt ℂ u 0) (hu0 : u 0 = 1) (hG : DifferentiableAt ℂ G 0) (hG0 : G 0 ≠ 0)
    (h : (fun t => F (c • t)) =ᶠ[nhds 0] fun t => u t * G t) (e : fderiv ℂ F 0 z = c⁻¹ * fderiv ℂ G 0 z) :
    fderiv ℂ u 0 z = 0 := by
  have e' := congrArg (· z) (h.fderiv_eq (𝕜 := ℂ))
  rw [fderiv_comp_smul, smul_zero, fderiv_fun_mul hu hG, hu0] at e'
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul, _root_.one_mul] at e'
  rw [e, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul, left_eq_add, mul_eq_zero] at e'
  exact e'.resolve_left hG0

theorem fderiv_ratio_eq_zero : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) → (∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex z) x j) {z | ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφ D ℂ (ex z).b x) j}) → 0 < n → ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → (∀ x, DifferentiableAt ℂ (u x) 0) → (∀ x, u x 0 = 1) → ∀ (v : epsR ℂ ⟶ D.P.A) (ν : Out.GtPt D (epsR ℂ)) (z : Fin g → ℂ), Out.GtPt.IsPull (spMap (epsScaleR ((n : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex z).b.left)) z v.left → (∀ x j, ⊤ ≤ LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) ν.b x) j → valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val = TrivSqZeroExt.inl (chiVal (ex 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex z) x j) 0 z)) → ∀ x, fderiv ℂ (u x) 0 z = 0 := by
  intro _ _ D g n ex sB hb _ hpull hadd hol _ hn u hu hud hu0 v ν z hν hv hval x
  have hv' := (HolHom.isDerivAt0_iff _ _ _).1 hv
  have hH := HolHom.holAt_of_isHolTo hol (Set.mem_univ 0)
  have hp := hpull _ _ v (𝟙 _)
  rw [Category.comp_id] at hp
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ (show Sp ℂ ⟶ _ from (ex 0).b.left) ⁻¹ᵁ
      LB.wchart D.P.L (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x) j := by
    choose j hj using fun k => exists_chart D.P.isLB (Out.DegPre.gtφT D D.P.A (sB D.P.A (𝟙 _)).b x k
      ((show Sp ℂ ⟶ _ from (ex 0).b.left) (default : PrimeSpectrum ℂ)))
    exact ⟨j, (HolHom.le_preimage_iff _ _).2 (Set.mem_iInter.2 hj)⟩
  have hvW := (HolHom.le_preimage_dual_iff hv'.1 _).2 hj
  have h1 := (top_le_wchart_pull hp.1 x j).2 hvW
  have h2 := (top_le_wchart_pull hν.1 x j).2 (fun p _ => h1 trivial)
  have e1 := valR_of_isPull hν x j
  have e2 := valR_of_isPull hp x j
  have e3 := HolHom.valR_spMap (epsScaleR ((n : ℂ)⁻¹)) (𝟙 (Sp (DualNumber ℂ)))
    (LB.wchart D.P.L (Out.DegPre.gtφT D (epsR ℂ) (sB (epsR ℂ) v).b x) j) h1 (((sB (epsR ℂ) v).s x).s j).val
  rw [Category.comp_id] at e3
  have e4 := congrArg TrivSqZeroExt.snd ((hval x j h2).symm.trans (e1.trans (e3.trans (congrArg _ e2))))
  have e5 : ∀ a : DualNumber ℂ, TrivSqZeroExt.snd (epsScaleR ((n : ℂ)⁻¹) a) = (n : ℂ)⁻¹ * TrivSqZeroExt.snd a := by
    intro a
    simp [epsScaleR]
  replace e4 := e4.trans ((e5 _).trans (congrArg (_ * ·) (hv'.2 _ hj _)))
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at e4
  obtain ⟨hev, hd⟩ := hH _ hj
  exact fderiv_eq_zero_of_smul (F := fun z' => chiVal (ex z') x j) (Nat.cast_ne_zero.2 hn.ne') (hud x) (hu0 x)
    (hd (((sB D.P.A (𝟙 _)).s x).s j).val)
    ((HolHom.valR_eq _ _ hj _).trans_ne ((((sB D.P.A (𝟙 _)).s x).s j).isUnit.map (HolHom.evalHom _ _ hj)).ne_zero)
    (hev.mono fun z' hz' => hu x z' j ((top_le_wchart_nsmul hadd (hb _ _) z' x j).2 hz')) e4

end GlobalTheory.AbelianLetters
