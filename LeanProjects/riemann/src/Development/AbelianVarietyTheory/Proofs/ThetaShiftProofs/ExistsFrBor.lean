import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedFramedPointTriangularFrameWeightRule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScalingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompareStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ValNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_idx (hσ : GoodEmb c σ) (X : Data E r) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j,
      (X.p0 ≤ ((idx j).2 : ℕ) ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (((idx j).2 : ℕ) < X.p0 ∧ conjEmb (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0)) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < X.p0 then
          hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · exact Or.inl ⟨by omega, b, c'⟩
    · exact Or.inr ⟨by omega, by rw [b]; exact hcc _, c', d⟩
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl

theorem exists_move (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (x b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) :
    ∃ h₀ : Matrix (Fin g) (Fin g) ℂ,
      (∀ v : Fin r → E, (fun j => perFr (U.X k) (rmul x b) v (relab c σ (e j).1) (e j).2) =
        h₀ *ᵥ fun j => perFr (U.X k) x v (relab c σ (e j).1) (e j).2) ∧
      (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∏ j, h₀⁻¹ j j ^ (a ((e j).1, (e j).2) + n / 2) = bchar (laU U a n k) b := by
  obtain ⟨idx, hi, hper⟩ := exists_idx hσ (U.X k) hr hp0 hty e
  obtain ⟨hbij, -, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega)] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
      · omega
    · rw [if_pos a1] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · omega
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (U.X k).p0 idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (U.X k).p0 idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (U.X k).p0 idx b, fun v => ?_, PerBor.inv_support _ _ _ hu hs, fun a n => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (U.X k).Gm x v _ _ (fun j => hper _ _ j) (fun j => hper _ _ j)
  · unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (U.X k).Ψ) (i : Fin r) => b τ i i ^ laU U a n k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, hdiag]
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega), if_pos a1, b1, hinv,
        show ((idx j).2 : ℕ) - (U.X k).p0 = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
    · rw [if_pos a1, if_neg (by omega), b1, hinv,
        show (U.X k).p0 - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring

theorem exists_frBor (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0)
    (x : (U.X k).dom) (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (h : rmul x.1 b ∈ (U.X k).dom) :
    ∃ (t : Ix Dw → (CAt σ)ˣ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)),
      FrBor t (U.un k x) (U.un k ⟨_, h⟩) ∧ FrChg G (t none : CAt σ) (U.un k x) (U.un k ⟨_, h⟩) ∧
      ∀ a n, toC (wchar (ex Dw a n) t) * bchar (laU U 0 n k) b =
        toC (t none : CAt σ) ^ n * bchar (laU U a n k) b := by
  obtain ⟨h₀, hP, htri, hw⟩ := exists_move hσ U k hr hp0 hty Uw.e x.1 b hb
  have hp := Uw.period k x
  have hp' := Uw.period k ⟨_, h⟩
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F (Uw.ik k)
    (Uw.Pm k x) (Uw.Pm k ⟨_, h⟩) (LinearEquiv.refl _ _) h₀ hp hp' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) (fun a => by
      have e1 : Uw.Pm k x a = _ := funext (Uw.Pm_eq k x a)
      have e2 : Uw.Pm k ⟨_, h⟩ a = _ := funext (Uw.Pm_eq k ⟨_, h⟩ a)
      rw [LinearEquiv.refl_apply, e1, e2]
      exact hP _)
  obtain ⟨hy1, hy2⟩ := Uw.lie k x
  obtain ⟨hy1', hy2'⟩ := Uw.lie k ⟨_, h⟩
  have hxx : (U.un k ⟨_, h⟩).x = (U.un k x).x := hy1'.trans (hu.symm.trans hy1.symm)
  have hder : ∀ τ i, IsDerivAt0 (fun z => (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left)
      (h₀⁻¹ *ᵥ Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ((U.un k ⟨_, h⟩).u τ i) := by
    intro τ i
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) hp (Uw.ik k)
      (Uw.Pm k ⟨_, h⟩) (Matrix.mulVecLin h₀) hp' hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy2' τ i
  obtain ⟨G, t₀, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).1 hxx
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := GlobalTheory.NormUnBor.diag_ne_zero Uw.e h₀⁻¹ hinv htri
  let d : Fin Uw.g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (Uw.e.symm p))
  refine ⟨t, G, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (Uw.e.symm ⟨τ, i'⟩) (Uw.e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩,
    hG, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [Uw.e.apply_symm_apply, Uw.e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F _ _ hp _ _ _ (hy2 τ) _ _).2 ?_
    rw [GlobalTheory.NormUnBor.col_eq_sum Uw.e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hG.2.2
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n
    rw [← hw a n, ← hw 0 n]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) * _ = _
    rw [Fintype.prod_option, mul_assoc]
    congr 1
    rw [← Equiv.prod_comp Uw.e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (Uw.e.symm (Uw.e j)) (Uw.e.symm (Uw.e j)) ^ a ((Uw.e j).1, (Uw.e j).2) * _ = _
    rw [Uw.e.symm_apply_apply, ← pow_add, Pi.zero_apply, zero_add]

theorem exists_unit (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ ∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1 := by
  obtain ⟨_, b, hb, hg, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun τ i => ?_⟩
  unfold dmin lminor
  rw [hg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

end GlobalTheory.ValNorm
