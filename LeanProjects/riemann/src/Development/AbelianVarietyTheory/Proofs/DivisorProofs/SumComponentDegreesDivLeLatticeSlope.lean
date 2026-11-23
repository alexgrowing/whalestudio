import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegreeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CovSum

theorem two_le_rdE (D : D7) : 2 ≤ D.host.rdE := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (2 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 2 ≤ D.host.q)
  have hd : (2 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 2 ≤ D.host.d)
  have h4 : (2 : ℝ) ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  linarith

theorem log_two_le (D : D7) (K : Type) [Field K] [NumberField K] (φ : D.host.E →+* K) :
    Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ) := by
  letI : Algebra D.host.E K := φ.toAlgebra
  refine le_trans ?_ (GlobalTheory.FieldSize.log_finrank_rootDiscr_le_of_tower D.host.E K).2
  have h := Real.log_le_log (by norm_num) (two_le_rdE D)
  have hpos : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  unfold Formalism.BasicNotions.Host.rdE at h
  rw [Real.log_rpow (by simpa using hpos)] at h
  simpa [div_eq_inv_mul] using h

theorem slope_sq_nonneg_of_rk_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (hL : L.FG)
    (h0 : Formalism.HN.rkK L = 0) (hK : Real.log 2 ≤ Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) : 0 ≤ slope_sq N L := by
  letI : StarRing K := starRingOfComm
  unfold slope_sq
  split_ifs with h
  · obtain ⟨-, h2, -⟩ := Formalism.HN.plLat K V _ h.some.2.1.1 h.some.2.1.2 (fun v => (h.some.2.2 v).1) L hL
    rw [h0, mul_zero] at h2
    unfold Formalism.HN.rk at h2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [h2]
    simp only [Nat.cast_zero, div_zero, mul_zero]
    linarith
  · exact le_rfl

theorem isComplexData {D : D7} (T : Core D) (hQ : T.Q.Pins) {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o) :
    GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum.IsComplexData Y.U (fun _ => D.sp.W j) Y.dict := by
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [h.lev.1.2.1, hQ.2.1.1]
  refine ⟨h.lev.2, fun σ hσ => ⟨h.unf σ hσ, ?_, (GlobalTheory.FinalJoin2.volPairEx_and_finVol D (D.sp.W j) (D.sp.W_sig j)).2,
    h.xiAbs σ hσ⟩⟩
  obtain ⟨th, hr, h1, h2⟩ := h.dictU σ hσ
  exact ⟨Y.Kf, th, hr, hM ▸ h.levelK, h1, h2⟩

theorem sum_deg_div_le_mu : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  intro D T j Y e o hT _ hY _ _ la hG hfin _
  obtain ⟨h1, h2⟩ := GlobalTheory.T.componentDegrees_sum_le_total_degree D _ _ _ _ _ _ Y.U (fun _ => D.sp.W j) Y.dict (isComplexData _ hT.pins Y hY) _ hG
  have h3 : (∑ᶠ Z, Y.rkC la Z) = (rankW Y.U (wtOf (T.Q.Dw j) la 0) : ℝ) := by
    haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
    rw [h1, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
  rw [h3]
  rcases Nat.eq_zero_or_pos (rankW Y.U (wtOf (T.Q.Dw j) la 0)) with h0 | h0
  · rw [h0, Nat.cast_zero, div_zero, mul_zero]
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact slope_sq_nonneg_of_rk_zero _ _ hG.2.1 h0 (log_two_le D _ (τ.codRestrict Y.d.c₂.F (Y.d.c₂.conj τ)))
  · have hp : (0 : ℝ) < rankW Y.U (wtOf (T.Q.Dw j) la 0) := by exact_mod_cast h0
    rw [degW_eq] at h2
    rw [← mul_div_assoc, div_le_iff₀ hp]
    change 2 * (∑ᶠ Z, degOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) ≤
      slopeW_sq Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtOf (T.Q.Dw j) la 0) * _
    linarith

end GlobalTheory.CovSum

end
