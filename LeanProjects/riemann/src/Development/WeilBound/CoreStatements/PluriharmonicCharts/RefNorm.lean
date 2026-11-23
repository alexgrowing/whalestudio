import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbit
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsValueAtZpow
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem sum_dy (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 := by
  have e1 : ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 =
      ∑ k, if h : ∀ p', M.blk p' ≠ some k then (M.b p ⟨k, h⟩ : ℝ) * L k else 0 :=
    Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun k hk => dif_neg fun h => hk ⟨⟨k, h⟩, rfl⟩) (fun k => by rw [dif_pos k.2])
  have e2 : (M.blk p).elim 0 L = ∑ k, if M.blk p = some k then L k else 0 := by
    cases M.blk p with
    | none => simp
    | some k => simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold FlagModel.dy
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [dif_pos h, dif_pos h, if_neg (h p)]; simp
  · rw [dif_neg h, dif_neg h]; split_ifs <;> simp

theorem Rel.smul
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    Rel M Gr p (torusSmul c z) (r + ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖) := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := htor _ _ _ _ (fun k => c k.1) (fun k => hc _) hG
  have eb : basePart M.blk (torusSmul c z) = torusSmul (fun k => c k.1) (basePart M.blk z) := rfl
  have ev : ∀ s, valAt M.x s (basePart M.blk (torusSmul c z)) = valAt M.x s (basePart M.blk z) := fun s =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit _ _ _ M.x s _ _ (hgood _ _ _ _ hG').2.1
      ⟨fun k => c k.1, fun k => hc _, rfl⟩
  have el : ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk (torusSmul c z) ⟨k', F.c k'⟩‖ =
      ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * Real.log ‖c k'.1‖ +
        ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eb, torusSmul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 (ne_of_notMem (gd.1 k)))]
    ring
  refine ⟨F, G, hG', h, bh, dh, t + (M.blk p).elim 0 (fun k => Real.log ‖c k‖), ?_, ?_⟩
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, c k * a, hk, mul_ne_zero (hc k) ha, fun m => ?_, ?_⟩
      · simp only [ev]
        rw [torusSmul, hz m, mul_assoc]
      · rw [hk, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 ha), Option.elim_some, add_comm]
    · refine Or.inr ⟨hk, ?_⟩
      rw [hk, ev, Option.elim_none, add_zero]
  · rw [el, sum_dy]
    ring

theorem Rel.conj
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) : Rel M Gr p (conjVec z) r := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := hconj _ _ _ _ hG
  have hw' := (hgood _ _ _ _ hG').2.1
  have eb : basePart M.blk (conjVec z) = conjVec (basePart M.blk z) := rfl
  refine ⟨F, _, hG', h.map (starRingEnd ℂ), bh.map _, ?_, t, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 dh
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, starRingEnd ℂ a, hk, (map_ne_zero _).2 ha, fun m => ?_, by simp⟩
      rw [conjVec, hz m, map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, eb, valAt_conj hw hw' (gd.2.1 _ I).1, minorIJ_map]
    · refine Or.inr ⟨hk, ?_⟩
      rw [eb, valAt_conj hw hw' (gd.2.2 p hk).2.1, RCLike.norm_conj]
  · rw [pot_conj]
    simp only [eb, conjVec, RCLike.norm_conj]

theorem exists_hom
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    (p : Ψ × Fin N) : ∃ A : HermLine ι, A.a = M.dy p ∧
      (∀ F w G, Gr F p.1 w G → M.IsInducedAt F w p G A) ∧ ∀ z, A.h (conjVec z) = A.h z := by
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ r, Rel M Gr p z r then Real.exp h.choose else refNorm (M.dy p) z
  have fr : ∀ z r, Rel M Gr p z r → f z = Real.exp r := fun z r h => by
    have hex : ∃ r, Rel M Gr p z r := ⟨r, h⟩
    simp only [f, dif_pos hex]
    rw [Rel.unique hgood hcomp hex.choose_spec h]
  refine ⟨⟨M.dy p, f, fun z hz => ?_, fun c z hc => ?_⟩, rfl, fun F w G hG z hz ho hn h bh dh => ?_, fun z => ?_⟩
  · simp only [f]
    split_ifs
    exacts [Real.exp_pos _, refNorm_pos _ hz]
  · change f (torusSmul c z) = _
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.smul hgood htor hc), Real.exp_add, mul_comm, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hc k)) _)]
    · have h' : ¬ ∃ r, Rel M Gr p (torusSmul c z) r := by
        rintro ⟨r, hr⟩
        have := hr.smul hgood htor (c := fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
        have e : torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
          funext q; simp [torusSmul, hc]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      exact refNorm_smul _ _ _
  · obtain ⟨c, hc, e⟩ := ho
    have hG' : Gr F p.1 (basePart M.blk z) G := by
      rw [e]; exact htor _ _ _ _ c hc hG
    refine ⟨fun k hk hz => ?_, fun hk => ?_⟩
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inl ⟨k, 1, hk, one_ne_zero, fun m => by rw [one_mul, hz m], rfl⟩, rfl⟩,
        Real.log_exp]
      simp [hn]
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inr ⟨hk, rfl⟩, rfl⟩, Real.log_exp]
      simp only [hn, norm_one, Real.log_one, mul_zero, Finset.sum_const_zero]
      ring
  · show f _ = f z
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.conj hgood hconj)]
    · have h' : ¬ ∃ r, Rel M Gr p (conjVec z) r := by
        rintro ⟨r, hr⟩
        have := hr.conj hgood hconj
        have e : conjVec (conjVec z) = z := by
          funext q; simp [conjVec]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      simp [refNorm, conjVec]

end PositivityTheory.Xgp.c_bm_exists_hom
