import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsComponentInChartRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalFrameOfTwistGenerationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfMatrixIdentityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorExpansionOfScaledProductStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CauchyBinetSumPositionedMinorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TMatBlockDiagDetFactorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdXbPowEqXcOfPowStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

section Pure

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

theorem aExt_mem (R : Subring Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (hC : ∀ s j l, C s j l ∈ R) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (a : Fin (p + q)) : aExt C s j a ∈ R := by
  refine R.sum_mem fun l _ => ?_
  split_ifs
  · exact hC _ _ _
  · exact R.zero_mem

theorem coefF_mem (R : Subring Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (hC : ∀ s j l, C s j l ∈ R) (r : Σ k, idx (p := p) (q := q) J₀ n k) (I : Finset (Fin (p + q))) :
    coefF C r I ∈ R := by
  obtain ⟨k | t, i⟩ := r
  · exact R.zero_mem
  · show (if e : I.card = (t.2 : ℕ) + 1 then _ else 0) ∈ R
    split_ifs with e
    · refine det_mem_subring R _ fun a b => ?_
      exact aExt_mem R C hC t.1 _ _
    · exact R.zero_mem

theorem sMin_mem (R : Subring Ω) (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω)
    (hB : ∀ s l j, B s l j ∈ R) (t : StepIx Ψ p q) (I : Finset (Fin (p + q)))
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : sMin B t I J ∈ R := by
  unfold sMin bMin
  split_ifs with e1 e2
  · refine det_mem_subring R _ fun a b => ?_
    simp only [Matrix.submatrix_apply, bExt]
    refine R.sum_mem fun l _ => ?_
    split_ifs
    · exact hB _ _ _
    · exact R.zero_mem
  · exact R.zero_mem
  · exact R.zero_mem

theorem frames_pure (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (R : Subring Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (hc0 : ∀ k, xb A x₀ ⟨k, c k⟩ ≠ 0) (hrat : ∀ k i, xb A x₀ ⟨k, i⟩ / xb A x₀ ⟨k, c k⟩ ∈ R)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (hT : ∀ s, (Ts s).det ≠ 0)
    (hAT : ∀ s, A s * Ts s = (xcOf x₀ c ^ m s) • C s) (hBC : ∀ s, B s * C s = 1)
    (hC : ∀ s j l, C s j l ∈ R) (hB : ∀ s l j, B s l j ∈ R) :
    ∃ F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀), F.c = c ∧
      ((∀ τ, IsBlockDiag p (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ (i : idx J₀ n k) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω),
        IsBlockDiag p h →
        detFac p r.2 (F.T r.1) * ∑ I, coefF A ⟨k, i⟩ I * minorIJ (F.T r.1 * h) I (stepCols (p + q) p r.2) =
          (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * ∑ I, F.u ⟨k, i⟩ I * minorIJ h I (stepCols (p + q) p r.2)) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ I I', IsStepRows (p + q) p r.2 I → IsStepRows (p + q) p r.2 I' →
        ∑ i : idx J₀ n k, F.u' I ⟨k, i⟩ * F.u ⟨k, i⟩ I' = if I = I' then 1 else 0) ∧
      ∀ r, blkF Ψ p q K₀ r = none →
        detFac p r.2 (F.T r.1) * 1 = (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * F.υ r) ∧
      (∀ r I, F.u r I ∈ R ∧ F.u' I r ∈ R) ∧
      ∀ r, blkF Ψ p q K₀ r = none → F.υ r ≠ 0 ∧ F.υ r ∈ R ∧ (F.υ r)⁻¹ ∈ R := by
  classical
  have hx : xcOf x₀ c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc0 (baseInl k)
  have hz : ∀ s, zOf A c s ≠ 0 := fun s => by
    by_cases h : 0 < rk Ψ p q s
    · rw [← xb_rowsOf A x₀ c s h]
      exact hc0 _
    · have h0 : rk Ψ p q s = 0 := by omega
      have : IsEmpty (Fin (rk Ψ p q s)) := by rw [h0]; exact Fin.isEmpty
      simp [zOf, Matrix.det_isEmpty]
  have hr : ∀ s (J : Fin (rk Ψ p q s) → Fin (n s)), ((A s).submatrix J id).det / zOf A c s ∈ R := fun s J => by
    by_cases h : 0 < rk Ψ p q s
    · rw [← xb_rowsOf A x₀ c s h, ← xb_full A x₀ s h J]
      exact hrat _ _
    · have h0 : rk Ψ p q s = 0 := by omega
      have : IsEmpty (Fin (rk Ψ p q s)) := by rw [h0]; exact Fin.isEmpty
      simp [zOf, Matrix.det_isEmpty]
  let υs : Ψ ⊕ Ψ → Ω := fun s => ((C s).submatrix (rowsOf c s) id).det
  have hu : ∀ s, υs s ≠ 0 ∧ υs s ∈ R ∧ (υs s)⁻¹ ∈ R ∧
      zOf A c s * (Ts s).det = (xcOf x₀ c ^ m s) ^ rk Ψ p q s * υs s := fun s =>
    GlobalTheory.T.minor_ratio_regular_of_matrix_identity R (A s) (C s) (B s) (Ts s) _ (hAT s) (pow_ne_zero _ hx) (hT s) (hBC s) (hC s) (hB s) (rowsOf c s)
      (hz s) (hr s)
  have hW : ∀ s, (Ts s).det = (xcOf x₀ c ^ m s) ^ rk Ψ p q s * υs s * (zOf A c s)⁻¹ := fun s => by
    have := (hu s).2.2.2
    have h' := hz s
    field_simp
    linear_combination this
  let wt : StepIx Ψ p q → Ω := fun t => Sum.elim (fun _ => 1) (fun τ => υs (.inl τ)) t.1
  have hwt : ∀ t, wt t ≠ 0 ∧ wt t ∈ R ∧ (wt t)⁻¹ ∈ R := fun t => by
    obtain ⟨s | s, a⟩ := t
    · simp [wt, R.one_mem]
    · exact ⟨(hu _).1, (hu _).2.1, (hu _).2.2.1⟩
  let F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀) :=
    { c := c
      T := tMat Ts
      u := fun r I => match r with
        | ⟨.inl _, _⟩ => 0
        | ⟨.inr t, J⟩ => wt t * cMin C t J I
      u' := fun I r => match r with
        | ⟨.inl _, _⟩ => 0
        | ⟨.inr t, J⟩ => (wt t)⁻¹ * sMin B t I J
      υ := fun r => (if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) *
        (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1) }
  refine ⟨F, rfl, ⟨fun τ => ?_, fun r k hk i h hh => ?_, fun r k hk I I' hI hI' => ?_, fun r hr' => ?_⟩,
    fun r I => ⟨?_, ?_⟩, fun r hr' => ?_⟩
  · obtain ⟨h1, h2, -⟩ := GlobalTheory.T.tMat_blockDiag_det_factors Ts τ
    exact ⟨h1, by show (tMat Ts τ).det ≠ 0; rw [h2]; exact mul_ne_zero (hT _) (hT _)⟩
  · obtain ⟨hp, rfl⟩ : IsProperStep (p + q) p r.2 ∧ k = .inr (stepOf Ψ p q r) := by
      unfold blkF at hk
      split_ifs at hk with hp
      exact ⟨hp, (Option.some.inj hk).symm⟩
    have e1 := GlobalTheory.T.minor_expansion_of_scaled_product A C Ts (xcOf x₀ c) m hAT r.1 (stepOf Ψ p q r) (BlockEmbeddings.stepOf_fst r) i h
      (stepCols (p + q) p r.2) (card_stepCols r)
    have key : detFac p r.2 (tMat Ts r.1) * xcOf x₀ c ^ (m (stepOf Ψ p q r).1 * (((stepOf Ψ p q r).2 : ℕ) + 1)) =
        (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') * wt (stepOf Ψ p q r) := by
      rw [GlobalTheory.T.prod_xb_pow_eq_xcOf_pow, (GlobalTheory.T.tMat_blockDiag_det_factors Ts r.1).2.2]
      have hr2 := r.2.2
      obtain ⟨hp1, hp2⟩ := hp
      by_cases hi : (r.2 : ℕ) < p
      · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, hi⟩⟩ := dif_pos hi
        have w1 : rkW r.2 = (r.2 : ℕ) + 1 := by simp only [rkW]; omega
        have w2 : rkO r.2 = 0 := by simp only [rkO]; omega
        have hn : ¬ p ≤ (r.2 : ℕ) + 1 := by omega
        rw [e, w1, w2]
        simp only [if_neg hn, if_neg hp2]
        simp [wt, mul_comm]
      · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg hi
        have w1 : rkW r.2 = p := by simp only [rkW]; omega
        have w2 : rkO r.2 = (r.2 : ℕ) - p + 1 := by simp only [rkO]; omega
        have hy : p ≤ (r.2 : ℕ) + 1 := by omega
        have h3 : (Ts (.inl r.1)).det = (xcOf x₀ c ^ m (.inl r.1)) ^ p * υs (.inl r.1) * (zOf A c (.inl r.1))⁻¹ :=
          hW _
        rw [e, w1, w2]
        simp only [if_pos hy, if_neg hp2]
        simp only [wt, Sum.elim_inr, mul_one]
        rw [h3]
        ring
    show detFac p r.2 (tMat Ts r.1) * ∑ I, cMin A (stepOf Ψ p q r) i I * minorIJ (tMat Ts r.1 * h) I _ =
      (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') *
        ∑ I, (wt (stepOf Ψ p q r) * cMin C (stepOf Ψ p q r) i I) * minorIJ h I _
    rw [e1]
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [← mul_assoc, key, mul_assoc]
  · obtain ⟨hp, rfl⟩ : IsProperStep (p + q) p r.2 ∧ k = .inr (stepOf Ψ p q r) := by
      unfold blkF at hk
      split_ifs at hk with hp
      exact ⟨hp, (Option.some.inj hk).symm⟩
    have e2 := GlobalTheory.T.cauchyBinet_sum_positioned_minors C B hBC (stepOf Ψ p q r) I I' (hI.1.trans (card_stepCols r)) (hI'.1.trans (card_stepCols r))
      (stepRows_pos r hI) (stepRows_pos r hI')
    have hw := (hwt (stepOf Ψ p q r)).1
    refine Eq.trans ?_ e2
    refine Finset.sum_congr rfl fun J _ => ?_
    show ((wt _)⁻¹ * sMin B _ I J) * (wt _ * cMin C _ J I') = _
    field_simp
  · have hnp : ¬ IsProperStep (p + q) p r.2 := fun hp => by
      unfold blkF at hr'
      rw [if_pos hp] at hr'
      simp at hr'
    have hr2 := r.2.2
    have hpi : p ≤ (r.2 : ℕ) + 1 := by
      by_contra h'
      exact hnp ⟨by omega, by omega⟩
    show detFac p r.2 (tMat Ts r.1) * 1 = (∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k') *
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1))
    rw [GlobalTheory.T.prod_xb_pow_eq_xcOf_pow, (GlobalTheory.T.tMat_blockDiag_det_factors Ts r.1).2.2]
    simp only [if_pos hpi]
    have h3 : (Ts (.inl r.1)).det = (xcOf x₀ c ^ m (.inl r.1)) ^ p * υs (.inl r.1) * (zOf A c (.inl r.1))⁻¹ := hW _
    have h4 : (Ts (.inr r.1)).det = (xcOf x₀ c ^ m (.inr r.1)) ^ q * υs (.inr r.1) * (zOf A c (.inr r.1))⁻¹ := hW _
    have w1 : rkW r.2 = p := by simp only [rkW]; omega
    by_cases hN : (r.2 : ℕ) + 1 = p + q
    · have w2 : rkO r.2 = q := by simp only [rkO]; omega
      simp only [if_pos hN]
      rw [w1, w2, h3, h4]
      ring
    · have w2 : rkO r.2 = 0 := by
        have : (r.2 : ℕ) + 1 = p := by
          by_contra h'
          exact hnp ⟨h', hN⟩
        simp only [rkO]; omega
      simp only [if_neg hN]
      rw [w1, w2, h3]
      ring
  · obtain ⟨k | t, J⟩ := r
    · exact R.zero_mem
    · exact R.mul_mem (hwt t).2.1 (coefF_mem R C hC ⟨.inr t, J⟩ I)
  · obtain ⟨k | t, J⟩ := r
    · exact R.zero_mem
    · exact R.mul_mem (hwt t).2.2 (sMin_mem R B hB t I J)
  · have hnp : ¬ IsProperStep (p + q) p r.2 := fun hp => by
      unfold blkF at hr'
      rw [if_pos hp] at hr'
      simp at hr'
    show ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1)) ≠ 0 ∧
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1)) ∈ R ∧
      ((if p ≤ (r.2 : ℕ) + 1 then υs (.inl r.1) else 1) * (if (r.2 : ℕ) + 1 = p + q then υs (.inr r.1) else 1))⁻¹ ∈ R
    have g : ∀ (P : Prop) [Decidable P] (s : Ψ ⊕ Ψ), (if P then υs s else 1) ≠ 0 ∧ (if P then υs s else 1) ∈ R ∧
        (if P then υs s else 1)⁻¹ ∈ R := fun P _ s => by
      split_ifs
      · exact ⟨(hu s).1, (hu s).2.1, (hu s).2.2.1⟩
      · simp [R.one_mem]
    obtain ⟨a1, a2, a3⟩ := g (p ≤ (r.2 : ℕ) + 1) (.inl r.1)
    obtain ⟨b1, b2, b3⟩ := g ((r.2 : ℕ) + 1 = p + q) (.inr r.1)
    refine ⟨mul_ne_zero a1 b1, R.mul_mem a2 b2, ?_⟩
    rw [mul_inv]
    exact R.mul_mem a3 b3

end Pure

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

theorem frames_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → FramesOK (aOf 𝔐 bW bO φ) x₀ m := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF tie Q hQ hrel hle
  classical
  choose cb hcb using hrel
  obtain ⟨P, hP, hreg⟩ := GlobalTheory.T.exists_component_in_chart_regular _ tie Q hQ hle cb hcb
  have hc0 := TiePrimes.ne_of_seg hP.1
  have hrat : ∀ k i, xb (aOf 𝔐 bW bO φ) x₀ ⟨k, i⟩ / xb (aOf 𝔐 bW bO φ) x₀ ⟨k, cb k⟩ ∈ regAt 𝔐.ξ P :=
    fun k i => TiePrimes.ratio_mem hP ⟨k, i⟩
  have hin : InChart 𝔐.ξ (seg x₀) (fun k => cb (baseInl k)) P := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hc0 (baseInl k), fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat (baseInl k) (c' k)
  choose Ts C B hT hAT hBC hC hB using fun s =>
    GlobalTheory.T.local_frame_of_twist_generation 𝔐.ξ (seg x₀) (LL 𝔐 s) (m s) (n s) (rk (CMType H) D.p D.q s) (VV 𝔐 s) (φ s) (cc 𝔐 bW bO s)
      (hF.1 s) (hF.2.1 s).1 (hF.2.1 s).2 (hF.2.2.1 s) P _ hin
  obtain ⟨F, rfl, h1, h2, h3⟩ := frames_pure (aOf 𝔐 bW bO φ) x₀ m (regAt 𝔐.ξ P) cb hc0 hrat Ts C B hT hAT hBC hC hB
  exact ⟨F, h1, hcb, fun r I => ⟨hreg _ (h2 r I).1, hreg _ (h2 r I).2⟩,
    fun r hr => ⟨(h3 r hr).1, hreg _ (h3 r hr).2.1, hreg _ (h3 r hr).2.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
