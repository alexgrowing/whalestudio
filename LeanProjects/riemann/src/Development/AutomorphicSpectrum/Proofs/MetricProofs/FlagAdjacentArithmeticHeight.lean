import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover

open GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ} {v : ℂ}
    (ho : SameOrbit z' z) (hv : IsValueAt y s z v) : IsValueAt y s z' v := by
  obtain ⟨c, hc, rfl⟩ := ho
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hne : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog h d hh c z]
    exact mul_ne_zero hne hz0
  · rw [eval_smul_homog h d hh c z, eval_smul_homog g d hg c z, mul_div_mul_left _ _ hne]

theorem valAt_eq_of_orbit {y : (Σ k, ι k) → Ω} {s : Ω} {z z' : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hz' : z' ∈ mcPts (mCoordIdeal y)) (ho : SameOrbit z' z)
    (hs : ∃ v, IsValueAt y s z v) : valAt y s z' = valAt y s z := by
  obtain ⟨v, hv⟩ := hs
  rw [valAt_eq hz hv, valAt_eq hz' (isValueAt_of_orbit ho hv)]

end Val

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fstPt_mem {k₀ : K} {P' : Ideal (MRing fun o : Option K => ι (o.getD k₀))} {Q : Ideal (MRing ι)}
    (hI : imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) P' = Q)
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts P') : fstPt k₀ z ∈ mcPts Q := by
  subst hI
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (some k)
    exact ⟨i, hi⟩
  · have := hz.2 _ hf
    exact (CPts.eval_rename_block _ z f).symm.trans this

end Points

section Minors

variable {N j : ℕ}

theorem minorIJ_shear {C : Finset (Fin N)} {ca cb : Fin N} (t : ℂ) (h : cb ∉ C) :
    minorIJ (1 + Matrix.single cb ca t) C C = 1 := by
  have e : (1 + Matrix.single cb ca t).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl) := by
    ext x y
    have hx : cb ≠ C.orderEmbOfFin rfl x := fun e => h (e ▸ Finset.orderEmbOfFin_mem _ _ _)
    simp [Matrix.add_apply, Matrix.single_apply, hx]
  have h1 := CPts.minorIJ_one (R := ℂ) C
  unfold minorIJ at h1 ⊢
  rw [dif_pos rfl] at h1 ⊢
  rw [e, h1]

theorem cb_notMem {a ca cb : Fin N} (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    cb ∉ stepCols N j a := by
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h] at hca
    rw [if_pos h]
    omega
  · simp only [lastCol, if_neg h] at hca
    rw [if_neg h]
    omega

end Minors

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pluck_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) :
    pluck M F zb k w I = A * minorIJ H I (stepCols N j p.2) := by
  let val := CPts.regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → CPts.regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → CPts.regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb = if I = I' then 1 else 0 :=
    fun I' hI' => by
      have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
        apply Subtype.ext
        have := hF.2.2.1 p k hp I I' hI hI'
        split_ifs at this ⊢ <;> simpa [uA, vA] using this
      have e' := congrArg val e
      rw [map_sum] at e'
      simp only [map_mul] at e'
      refine e'.trans ?_
      split_ifs <;> simp
  unfold pluck
  simp only [hw]
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb *
        (A * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') zb * minorIJ H I' (stepCols N j p.2))
      = A * ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * valAt M.x (F.u ⟨k, m⟩ I') zb) *
          minorIJ H I' (stepCols N j p.2) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => by ring
    _ = A * minorIJ H I (stepCols N j p.2) := by
        congr 1
        rw [Finset.sum_eq_single I]
        · rw [rel I hI, if_pos rfl, one_mul]
        · intro I' _ hne
          by_cases hs : IsStepRows N j p.2 I'
          · rw [rel I' hs, if_neg (Ne.symm hne), zero_mul]
          · rw [minorIJ_block_zero hH hs, mul_zero]
        · simp

theorem twMinor_of_flag (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) {w : (Σ k, ι k) → ℂ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : IsBlockDiag j H) {A : ℂ}
    (hw : ∀ m : ι k, w ⟨k, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ H I (stepCols N j p.2))
    (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    twMinor M F zb p.2 k g w J = A * minorIJ (g * H) J (stepCols N j p.2) := by
  unfold twMinor
  rw [minorIJ_mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun I hI => by
    rw [pluck_of_flag M hF hzb hG hp hH hw (Finset.mem_filter.1 hI).2]]
  refine (Finset.sum_congr rfl fun I _ => by ring).trans (Finset.sum_subset (Finset.filter_subset _ _) fun I _ hI => ?_)
  have hs : ¬ IsStepRows N j p.2 I := fun h => hI (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  rw [minorIJ_block_zero hH hs, mul_zero, mul_zero]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ z ∈ mcPts (wP M τ a k₀ ca cb), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ z ∈ wO M Rb τ a k₀ ca cb F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hba hblk hca hcb hA z hz
  obtain ⟨hW, -, -, hImg, -⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA
  obtain ⟨bs, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hz1 : fstPt k₀ z ∈ mcPts (mCoordIdeal y) := fstPt_mem hImg hz
  have hzb : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := bs _ hz1
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (baseOf M k₀ z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (baseOf M k₀ z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (baseOf M k₀ z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ v, IsValueAt M.x s zc v) → valAt M.x s (baseOf M k₀ z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : Option K → ℂ := fun o => o.elim 1 fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ o, c o ≠ 0 := fun o => by
    rcases o with _ | k
    · exact one_ne_zero
    · by_cases h : ∀ p, M.blk p ≠ some k
      · simp only [c, Option.elim_some, dif_pos h]
        exact hc₀ _
      · simp only [c, Option.elim_some, dif_neg h]
        exact one_ne_zero
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) := mcPts_smul hW.2.1.2.1 c hc hz
  have hbp : basePart M.blk (fstPt k₀ z') = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show c (some k) * z ⟨some k, m⟩ = c₀ ⟨k, hk⟩ * z ⟨some k, m⟩
    simp only [c, Option.elim_some, dif_pos hk]
  have hbp2 : basePart M.blk (sndPt k₀ z') = zc := by
    rw [← hbp]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (e ▸ hblk)
    show z' (v₁ k₀ ⟨k, m⟩) = z' (v₀ k₀ ⟨k, m⟩)
    rw [v₁_ne hne]
    rfl
  obtain ⟨h, t, H1, H2⟩ := (GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hblk hca hcb hA F z' hF
    (hbp ▸ hblm) (hbp ▸ hblgood) (hbp ▸ hblnorm)).1 hz'
  have hh := H1.2.1
  refine ⟨F, kb, V, bl, r, h, ⟨hb, hba, hblk, hca, hcb, hA, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hp
    obtain ⟨A, hA0, hA'⟩ := H1.2.2 p k hp
    have hk : c (some k) = 1 := by
      simp only [c, Option.elim_some]
      exact dif_neg fun e => e p hp
    have hw : ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : fstPt k₀ z' ⟨k, m⟩ = fstPt k₀ z ⟨k, m⟩ := by
        show c (some k) * z ⟨some k, m⟩ = z ⟨some k, m⟩
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0
  · obtain ⟨A, hA0, hA'⟩ := H2.2.2 (τ, a) k₀ hblk
    have hbd := (H2.2.1 τ).1
    rw [Function.update_self] at hbd
    have hw : ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = A * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
        minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := fun m => by
      have e : sndPt k₀ z' ⟨k₀, m⟩ = sndPt k₀ z ⟨k₀, m⟩ := by
        show z' (v₁ k₀ ⟨k₀, m⟩) = z (v₁ k₀ ⟨k₀, m⟩)
        rw [v₁_self]
        exact one_mul _
      rw [← e, hA' m, hbp2, show (τ, a).1 = τ from rfl, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by
        rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    have := twMinor_of_flag M hF hzb hG (p := (τ, a)) hblk hbd hw (h τ)⁻¹ (stepCols N j a)
    refine fun e0 => hA0 ?_
    rw [show (τ, a).2 = a from rfl] at this
    rw [this, Matrix.nonsing_inv_mul_cancel_left _ _ (hh τ).2.isUnit, minorIJ_shear t (cb_notMem hca hcb), mul_one] at e0
    exact e0

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover
