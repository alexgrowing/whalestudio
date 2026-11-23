import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.LevelLetterCocycles.TwGuard
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

noncomputable section

namespace GlobalTheory.PerRedTw

section Copied

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.Forms Matrix NumberField
open scoped BigOperators

theorem exists_orthonormal_frame_twisted (D : D7) : ∃ o : FrP D, o.IsON := by
  classical
  let _ := D.host.cmStar
  have hY : ∀ τ, ∃ Y : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) ℂ,
      IsUnit Y.det ∧ Yᴴ * (gramP D).map (embT D τ) * Y = 1 := by
    intro τ
    have hs := D.sp.X'_sig (embT D τ)
    rw [D.X'_posDef (embT D τ)] at hs
    dsimp only at hs
    obtain ⟨e, P, hP⟩ := hs
    have hJ : Formalism.UG.Jpq D.sp.X'.rank 0 = 1 := by
      ext i j
      rcases i with i | i
      · rcases j with j | j
        · simp [Formalism.UG.Jpq, Matrix.one_apply]
        · exact j.elim0
      · exact i.elim0
    have hcT : Formalism.UG.cT (starRingEnd ℂ) P.1 = P.1ᴴ := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [hcT, hJ] at hP
    let f : Fin D.sp.X'.rank ≃ Fin (D.R.N D.R.m - 1) := finCongr (rankP D)
    let g : Fin (D.R.N D.R.m - 1) ≃ Fin D.sp.X'.rank ⊕ Fin 0 := f.symm.trans e
    have hG : ((gramP D).map (embT D τ)).submatrix g.symm g.symm = (D.sp.X'.gram.map (embT D τ)).reindex e e := by
      ext i j
      simp [g, f, gramP, Matrix.reindex_apply, Matrix.submatrix_apply]
    refine ⟨P.1.submatrix g g, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self]; exact Matrix.isUnits_det_units P
    · have h1 : (gramP D).map (embT D τ) = (((gramP D).map (embT D τ)).submatrix g.symm g.symm).submatrix g g := by
        ext i j; simp
      rw [Matrix.conjTranspose_submatrix, h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hG, hP]
      exact Matrix.submatrix_one_equiv g
  choose Y hYu hY using hY
  exact ⟨⟨Y, hYu⟩, fun τ => Or.inl (hY τ)⟩

theorem nfAll_zero_tw {D : D7} (n : ℕ) (lam : D.what₂.Tau → DomWeight n) : nfAll lam 0 0 = 0 := by
  simp [nfAll, Formalism.REAL.fockF]

end Copied

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.MainNotions.RT.PeriodPointConditions GlobalTheory.PerQ

attribute [local instance] MemberForms.clsPFin

variable {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
  {Tw : TwForms D} {Y : DivX D}

theorem eW_rep_o_tw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (o : FrP D)
    (z : (D.PTw u μ).Wrow) (hz : z ∈ (Tw.fm u μ).ptC) (c : (Tw.fm u μ).clsP) :
    ∃ Q ∈ CSpan (Tw.fm u μ).sg,
      (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) Q := by
  have hF := ((t.pt.val u μ hμ).ptC z).1 hz
  obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hF
  have hval := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hg).2) ((t.pt.cls u μ hμ).y c) (Set.mem_univ _)
  obtain ⟨Q0, hQ0, hfn⟩ := Submodule.mem_map.1 hval
  have hQ0' : Q0 ∈ CSpan (Tw.fm u μ).sg := by
    have := CSpan_shW (Tw.fm u μ).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
    unfold sgTG at hQ0
    rw [this] at hQ0
    exact hQ0
  have he : (t.pt.val u μ hμ).eW z c = fnOf _ (shiftOf (sgTG (Tw.fm u μ))) 1 Q0 := by
    rw [hfn, ← hres]; rfl
  have hM : ∀ τ, IsUnit ((o.1 τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (o.2 τ).ringInverse
  refine ⟨_, ?_, he.trans (fnOf_change _ _ _ _ hM Q0)⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hQ0')

open Classical in
theorem eW_resCTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) :
    (t.pt.val u μ hμ).eW (resCTw t u μ hμ c z) = fun c' => if c' = c then (t.pt.val u μ hμ).eW z c' else 0 := by
  classical
  unfold resCTw
  rw [LinearEquiv.apply_symm_apply]

theorem petersson_eq_sum_restrict_twist (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (a b : (D.PTw u μ).Wrow) (ha : a ∈ (Tw.fm u μ).ptC) (hb : b ∈ (Tw.fm u μ).ptC) :
    (Tw.fm u μ).ipP a b = ∑ c, (Tw.fm u μ).ipP (resCTw t u μ hμ c a) (resCTw t u μ hμ c b) := by
  classical
  obtain ⟨o, ho⟩ := exists_orthonormal_frame_twisted D
  choose P hP hPe using eW_rep_o_tw t u μ hμ o a ha
  choose Q hQ hQe using eW_rep_o_tw t u μ hμ o b hb
  rw [(t.pt.val u μ hμ).ipP o ho a b P Q hP hQ hPe hQe]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hP' : ∀ c', (if c' = c then P c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hP c'
    · exact Submodule.zero_mem _
  have hQ' : ∀ c', (if c' = c then Q c' else 0) ∈ CSpan (Tw.fm u μ).sg := fun c' => by
    split_ifs
    · exact hQ c'
    · exact Submodule.zero_mem _
  have hPe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c a) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then P c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hPe c'
    · exact (map_zero _).symm
  have hQe' : ∀ c', (t.pt.val u μ hμ).eW (resCTw t u μ hμ c b) c' =
      fnOf _ (shiftOf (sgTG (Tw.fm u μ))) (fun τ => (o.1 τ)⁻¹) (if c' = c then Q c' else 0) := fun c' => by
    rw [eW_resCTw]
    dsimp only
    split_ifs
    · exact hQe c'
    · exact (map_zero _).symm
  rw [(t.pt.val u μ hμ).ipP o ho _ _ _ _ hP' hQ' hPe' hQe', Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    simp [hc', nfAll_zero_tw]
  · intro h; exact absurd (Finset.mem_univ c) h

open Classical in
def pcTw (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (c : (Tw.fm u μ).clsP) (z : (D.PTw u μ).Wrow) (G : (D.PTw u μ).Mt) : ℂ :=
  if z ∈ (Tw.fm u μ).ptC then pcLTw t u μ hμ c z G
  else if h : Nonempty (Tw.fm u μ).clsP then
    (if c = Classical.choice h then ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) * (D.PTw u μ).period z G else 0)
  else 0

theorem perDecTw_of_at (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : PerDecTwT Y t u μ hμ) : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ := by
  classical
  have hcard : ∀ c, ((Nat.card ((Tw.fm u μ).stabilizer₂ c) : ℕ) : ℂ) ≠ 0 := fun c =>
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨pcTw t u μ hμ, fun z G => ?_, fun x hx F hF c => ?_⟩
  · by_cases hz : z ∈ (Tw.fm u μ).ptC
    · have hG : t.ptE.jM u μ G ∈ (Tw.fm u μ).ptC := ((t.ptE.per u μ hμ).2.1) G
      rw [((t.ptE.per u μ hμ).2.2) z G, petersson_eq_sum_restrict_twist t u μ hμ _ _ hG hz]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [pcTw, if_pos hz, pcLTw]
      rw [← mul_assoc, inv_mul_cancel₀ (hcard c), one_mul]
    · by_cases hne : Nonempty (Tw.fm u μ).clsP
      · rw [Finset.sum_eq_single (Classical.choice hne)]
        · simp only [pcTw, if_neg hz, dif_pos hne, ↓reduceIte]
          rw [← mul_assoc, inv_mul_cancel₀ (hcard _), one_mul]
        · intro c _ hc
          simp only [pcTw, if_neg hz, dif_pos hne, if_neg hc, mul_zero]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · have hE : IsEmpty (Tw.fm u μ).clsP := not_nonempty_iff.mp hne
        have hz0 : z = 0 := (t.pt.val u μ hμ).eW.injective (funext fun c => hE.elim c)
        subst hz0
        simp
  · obtain ⟨y, hy, hv⟩ := h x hx F hF c
    have hz : (Tw.fm u μ).ptEmb x ∈ (Tw.fm u μ).ptC := (((t.pt.val u μ hμ).rat _).1 ⟨x, rfl⟩).1
    refine ⟨y, ?_, hv⟩
    simp only [pcTw, if_pos hz]
    exact hy

theorem reduction_perDecTw : ∀ (D : D7) (cf : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (tp : Formalism.L2.Host.TupTied D cf nch) (C : ColsTiedSym D) (Tw : TwForms D) (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (Y : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0), GlobalTheory.PerQ.PerDecTwT Y t u μ hμ → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Y Tw u μ :=
  fun _ _ _ _ _ _ t _ u μ hμ h => perDecTw_of_at t u μ hμ h

end GlobalTheory.PerRedTw
