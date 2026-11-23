import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovLift

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isValueAt_orbit {x : (Σ k, ι k) → Ω} {s : Ω} {t t' : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt x s t v) (ho : SameOrbit t' t) : IsValueAt x s t' v := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨c, hc, rfl⟩ := ho
  have hp : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, hy, heq, ?_, ?_⟩
  · rw [eval_smul_homog h d hh c t]; exact mul_ne_zero hp hz0
  · rw [eval_smul_homog h d hh c t, eval_smul_homog g d hg c t, mul_div_mul_left _ _ hp]

theorem analyticAt_eval {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) (t : σ → ℂ) :
    AnalyticAt ℂ (fun t : σ → ℂ => eval t P) t := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => exact (hp.add hq).congr (Filter.Eventually.of_forall fun t => by simp)
  | mul_X p i hp =>
    have hi : AnalyticAt ℂ (fun t : σ → ℂ => t i) t :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt t
    exact (hp.mul hi).congr (Filter.Eventually.of_forall fun t => by simp)

theorem notMem_of_eval_ne_zero {t : (Σ k, ι k) → ℂ} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (h0 : eval t (map (Int.castRingHom ℂ) h) ≠ 0) : h ∉ mCoordIdeal t := by
  intro hm
  have h' : mConeMap t h = 0 := hm
  rw [mConeMap_of_isMultiHomog t hh] at h'
  rcases mul_eq_zero.1 h' with h1 | h1
  · refine h0 ?_
    have h2 := MvPolynomial.C_eq_zero.1 h1
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at h2
    simpa using h2
  · exact absurd h1 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero _))

theorem exists_value_family {A : Type} [Finite A] {x : (Σ k, ι k) → Ω} {b : (Σ k, ι k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal x)) (e : A → Ω) (he : ∀ a, RegAt x (mCoordIdeal b) (e a)) :
    ∃ (W : Set ((Σ k, ι k) → ℂ)) (r : A → ((Σ k, ι k) → ℂ) → ℂ), IsOpen W ∧ b ∈ W ∧
      (∀ t t', SameOrbit t' t → t ∈ W → t' ∈ W) ∧ (∀ a, AnalyticOnNhd ℂ (r a) W) ∧
      ∀ a, ∀ t ∈ W, IsValueAt x (e a) t (r a t) ∧ RegAt x (mCoordIdeal t) (e a) := by
  choose d g h hg hh hn heq using he
  have hW : ∀ a, ∀ t ∈ {t : (Σ k, ι k) → ℂ | ∀ a, eval t (map (Int.castRingHom ℂ) (h a)) ≠ 0},
      eval t (map (Int.castRingHom ℂ) (h a)) ≠ 0 := fun a t ht => ht a
  refine ⟨{t | ∀ a, eval t (map (Int.castRingHom ℂ) (h a)) ≠ 0},
    fun a t => eval t (map (Int.castRingHom ℂ) (g a)) / eval t (map (Int.castRingHom ℂ) (h a)), ?_,
    fun a => ValRing.eval_ne_zero_of_notMem (hh a) (hn a), ?_, ?_, ?_⟩
  · rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun a => ?_
    have hc : Continuous fun t : (Σ k, ι k) → ℂ => eval t (map (Int.castRingHom ℂ) (h a)) :=
      continuous_iff_continuousAt.2 fun t => (analyticAt_eval _ t).continuousAt
    exact isOpen_ne_fun hc continuous_const
  · rintro t t' ⟨c, hc, rfl⟩ ht a
    rw [eval_smul_homog (h a) (d a) (hh a) c t]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)) (ht a)
  · intro a t ht
    exact (analyticAt_eval _ t).div (analyticAt_eval _ t) (ht a)
  · intro a t ht
    exact ⟨⟨d a, g a, h a, hg a, hh a, ValRing.aeval_ne_zero_of_notMem hb (hh a) (hn a), heq a, ht a, rfl⟩,
      d a, g a, h a, hg a, hh a, notMem_of_eval_ne_zero (hh a) (ht a), heq a⟩

theorem ne_zero_of_X_notMem {t : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal t) :
    t q ≠ 0 := fun h0 => h (by
  show mConeMap t (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem X_notMem_of_ne_zero {t : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h0 : t q ≠ 0) :
    (X q : MRing ι) ∉ mCoordIdeal t := fun hm => by
  have h' : mConeMap t (X q) = 0 := hm
  rw [mConeMap, aeval_X] at h'
  exact h0 (C_eq_zero.1 ((mul_eq_zero.1 h').resolve_right (X_ne_zero _)))

theorem isValueAt_sum {A : Type} {x : (Σ k, ι k) → Ω} {t : (Σ k, ι k) → ℂ} (S : Finset A) (f : A → Ω) (v : A → ℂ)
    (h : ∀ i, IsValueAt x (f i) t (v i)) : IsValueAt x (∑ i ∈ S, f i) t (∑ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x t
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ValRing.isValueAt_add (h a) ih

end Values

section Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {L L' : Type} [Fintype L] [Fintype L'] {a : L → Type} {a' : L' → Type} [∀ k, Fintype (a k)]
    [∀ k, Fintype (a' k)] {κ : L → L'} {v : (Σ k, a k) → (Σ k, a' k)} (hv : IsBlockMap κ v)
    {t t' : (Σ k, a' k) → ℂ} (h : SameOrbit t t') : SameOrbit (t ∘ v) (t' ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c ∘ κ, fun k => hc _, ?_⟩
  funext p
  simp [Function.comp, hv.2.2.1 p]

theorem exists_normalised (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {z : (Σ k, ι k) → ℂ}
    (hc : ∀ k, basePart M.blk z ⟨k, F.c k⟩ ≠ 0) :
    ∃ z₁, SameOrbit z₁ z ∧ ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := by
  let c : K → ℂ := fun k => if h : ∀ q, M.blk q ≠ some k then
    (basePart M.blk z ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩)⁻¹ else 1
  refine ⟨fun p => c p.1 * z p, ⟨c, fun k => ?_, rfl⟩, fun k => ?_⟩
  · by_cases h : ∀ q, M.blk q ≠ some k
    · simp only [c, dif_pos h]
      exact inv_ne_zero (hc ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  · obtain ⟨k, h⟩ := k
    show c k * basePart M.blk z ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩ = 1
    simp only [c, dif_pos h]
    exact inv_mul_cancel₀ (hc ⟨k, h⟩)

theorem good_open (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal b)) :
    ∃ W : Set ((Σ k, baseIdx ι M.blk k) → ℂ), IsOpen W ∧ b ∈ W ∧ (∀ t t', SameOrbit t' t → t ∈ W → t' ∈ W) ∧
      ∀ t ∈ W, M.GoodAt F (mCoordIdeal t) := by
  obtain ⟨W₁, r₁, o₁, m₁, s₁, -, v₁⟩ := exists_value_family hb
    (fun q : (Σ k, ι k) × Finset (Fin N) => F.u q.1 q.2) fun q => (hF.2.1 q.1 q.2).1
  obtain ⟨W₂, r₂, o₂, m₂, s₂, -, v₂⟩ := exists_value_family hb
    (fun q : (Σ k, ι k) × Finset (Fin N) => F.u' q.2 q.1) fun q => (hF.2.1 q.1 q.2).2
  obtain ⟨W₃, r₃, o₃, m₃, s₃, -, v₃⟩ := exists_value_family hb
    (fun p : {p : Ψ × Fin N // M.blk p = none} => F.υ p.1) fun p => (hF.2.2 p.1 p.2).2.1
  obtain ⟨W₄, r₄, o₄, m₄, s₄, -, v₄⟩ := exists_value_family hb
    (fun p : {p : Ψ × Fin N // M.blk p = none} => (F.υ p.1)⁻¹) fun p => (hF.2.2 p.1 p.2).2.2
  refine ⟨W₁ ∩ W₂ ∩ (W₃ ∩ W₄) ∩ {t | ∀ k, t ⟨k, F.c k⟩ ≠ 0}, ?_, ⟨⟨⟨m₁, m₂⟩, m₃, m₄⟩,
    fun k => ne_zero_of_X_notMem (hF.1 k)⟩, ?_, ?_⟩
  · refine ((o₁.inter o₂).inter (o₃.inter o₄)).inter ?_
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  · rintro t t' ho ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₅⟩
    refine ⟨⟨⟨s₁ _ _ ho h₁, s₂ _ _ ho h₂⟩, s₃ _ _ ho h₃, s₄ _ _ ho h₄⟩, fun k => ?_⟩
    obtain ⟨c, hc, rfl⟩ := ho
    exact mul_ne_zero (hc k) (h₅ k)
  · rintro t ⟨⟨⟨h₁, h₂⟩, h₃, h₄⟩, h₅⟩
    exact ⟨fun k => X_notMem_of_ne_zero (h₅ k), fun q I => ⟨(v₁ (q, I) t h₁).2, (v₂ (q, I) t h₂).2⟩,
      fun p hp => ⟨(hF.2.2 p hp).1, (v₃ ⟨p, hp⟩ t h₃).2, (v₄ ⟨p, hp⟩ t h₄).2⟩⟩

theorem val_inv (M : FlagModel y Ψ N j) (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M)
    {t : (Σ k, baseIdx ι' M'.blk k) → ℂ} (ht : t ∈ mcPts (mCoordIdeal M'.x)) (F' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F : FrameData ι Ψ N M.Ω M.blk) (hF' : M'.IsFrame F') (hF : M.IsFrame F) (hg' : M'.GoodAt F' (mCoordIdeal t))
    (hg : M.GoodAt F (mCoordIdeal (t ∘ Cv.v))) (τ : Ψ) :
    (Matrix.of fun a b => valAt M'.x (((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) a b) t) * Cv.trans F' F t τ = 1 := by
  have hd' : IsUnit (F'.T τ).det := ((hF'.1 τ).2).isUnit
  have hd : IsUnit ((F.T τ).map Cv.φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero Cv.φ).2 (hF.1 τ).2).isUnit
  have hAB : ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) * (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd']
  have hA : ∀ a b, ∃ v, IsValueAt M'.x (((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) a b) t v := fun a b =>
    ValRing.exists_isValueAt ht (Cv.agree t ht F' F hF' hF hg' hg τ a b).2
  have hB : ∀ a b, ∃ v, IsValueAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a b) t v := fun a b =>
    ValRing.exists_isValueAt ht (Cv.agree t ht F' F hF' hF hg' hg τ a b).1
  choose vA hvA using hA
  choose vB hvB using hB
  ext a b
  have hv := isValueAt_sum (x := M'.x) (t := t) Finset.univ
    (fun c => ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) a c * (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) c b)
    (fun c => vA a c * vB c b) fun c => isValueAt_mul (hvA a c) (hvB c b)
  rw [← Matrix.mul_apply, hAB, Matrix.one_apply] at hv
  have e : ((Matrix.of fun a b => valAt M'.x (((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) a b) t) * Cv.trans F' F t τ) a b =
      ∑ c, vA a c * vB c b := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by
      simp only [Matrix.of_apply, FlagCover.trans]
      rw [valAt_eq ht (hvA a c), valAt_eq ht (hvB c b)]
  rw [e, Matrix.one_apply]
  split_ifs with hab
  · rw [if_pos hab] at hv
    exact isValueAt_one ht hv
  · rw [if_neg hab] at hv
    exact isValueAt_zero ht hv

theorem left_inv_val (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (hF : M.IsFrame F)
    {b : (Σ k, baseIdx ι M.blk k) → ℂ} (hb : b ∈ mcPts (mCoordIdeal M.x)) (hg : M.GoodAt F (mCoordIdeal b))
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (I I' : Finset (Fin N)) (hI : IsStepRows N j p.2 I)
    (hI' : IsStepRows N j p.2 I') :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := by
  have h1 : ∀ m : ι k, ∃ v, IsValueAt M.x (F.u' I ⟨k, m⟩) b v := fun m =>
    ValRing.exists_isValueAt hb (hg.2.1 ⟨k, m⟩ I).2
  have h2 : ∀ m : ι k, ∃ v, IsValueAt M.x (F.u ⟨k, m⟩ I') b v := fun m =>
    ValRing.exists_isValueAt hb (hg.2.1 ⟨k, m⟩ I').1
  choose v hv using h1
  choose w hw using h2
  have hs := isValueAt_sum (x := M.x) (t := b) Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I')
    (fun m => v m * w m) fun m => isValueAt_mul (hv m) (hw m)
  rw [hF.2.2.1 p k hp I I' hI hI'] at hs
  have e : ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = ∑ m, v m * w m :=
    Finset.sum_congr rfl fun m _ => by rw [valAt_eq hb (hv m), valAt_eq hb (hw m)]
  rw [e]
  split_ifs with hII
  · rw [if_pos hII] at hs
    exact isValueAt_one hb hs
  · rw [if_neg hII] at hs
    exact isValueAt_zero hb hs

theorem minor_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
    (A : E → Matrix (Fin n) (Fin n) ℂ) (x : E) (I J : Finset (Fin n))
    (h : ∀ a b, AnalyticAt ℂ (fun w => A w a b) x) : AnalyticAt ℂ (fun w => minorIJ (A w) I J) x := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    refine Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.fun_mul
      (Finset.analyticAt_fun_prod _ fun a _ => ?_)
    exact h _ _
  · simp only [dif_neg e]
    exact analyticAt_const

theorem flag_transfer (N j : ℕ) (i : Fin N) (hj : j ≤ N) {κ κ' : Type} [Fintype κ] [Fintype κ']
    (u : κ → Finset (Fin N) → ℂ) (u' : Finset (Fin N) → κ → ℂ) (uu : κ' → Finset (Fin N) → ℂ)
    (A T h : Matrix (Fin N) (Fin N) ℂ) (a a' : ℂ) (z₀ : κ → ℂ) (z₁ : κ' → ℂ)
    (hu : ∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0)
    (hA : A * T = 1) (hTh : IsBlockDiag j (T * h)) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (h0 : ∀ m, z₀ m = a * ∑ I, u m I * minorIJ (T * h) I (stepCols N j i))
    (h1 : ∀ m, z₁ m = a' * ∑ I, uu m I * minorIJ h I (stepCols N j i)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z₁ m = c * ∑ I, uu m I * ∑ I', if IsStepRows N j i I' then
      minorIJ A I I' * ∑ m', u' I' m' * z₀ m' else 0 := by
  obtain ⟨hCB, hvan', -, -⟩ := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj
  have hvan : ∀ I, ¬ IsStepRows N j i I → minorIJ (T * h) I (stepCols N j i) = 0 := fun I hI => by
    rcases hvan' (T * h) I hTh hI with e | e
    · exact e
    · refine dif_neg fun hc => hI ⟨hc, ?_⟩
      rw [e, Finset.card_empty, Finset.card_eq_zero] at hc
      rw [hc]
      exact Finset.empty_subset _
  have step : ∀ I', IsStepRows N j i I' → ∑ m', u' I' m' * z₀ m' = a * minorIJ (T * h) I' (stepCols N j i) := by
    intro I' hI'
    calc ∑ m', u' I' m' * z₀ m'
        = a * ∑ I, (∑ m', u' I' m' * u m' I) * minorIJ (T * h) I (stepCols N j i) := by
          simp only [h0, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
      _ = a * minorIJ (T * h) I' (stepCols N j i) := by
          congr 1
          rw [Finset.sum_eq_single I']
          · rw [hu I' I' hI' hI', if_pos rfl, one_mul]
          · intro I _ hne
            by_cases hI : IsStepRows N j i I
            · rw [hu I' I hI' hI, if_neg hne.symm, zero_mul]
            · rw [hvan I hI, mul_zero]
          · simp
  have hmin : ∀ I, minorIJ h I (stepCols N j i) = a⁻¹ * ∑ I', if IsStepRows N j i I' then
      minorIJ A I I' * ∑ m', u' I' m' * z₀ m' else 0 := by
    intro I
    have e : h = A * (T * h) := by rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
    conv_lhs => rw [e]
    rw [hCB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    by_cases hI' : IsStepRows N j i I'
    · rw [if_pos hI', step I' hI']
      field_simp
    · rw [if_neg hI', hvan I' hI', mul_zero, mul_zero]
  refine ⟨a' * a⁻¹, mul_ne_zero ha' (inv_ne_zero ha), fun m => ?_⟩
  rw [h1 m, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hmin I]
  ring

end Geo

theorem lift_inverse : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w₀ ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w₀ → ∀ (V : Set ((Σ k, baseIdx ι M.blk k) → ℂ)) (V' : Set ((Σ k, baseIdx ι' M'.blk k) → ℂ)) (s : ((Σ k, baseIdx ι M.blk k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ), IsOpen V → basePart M.blk w₀ ∈ V → IsOpen V' → basePart M'.blk z ∈ V' → AnalyticOnNhd ℂ s V → (∀ b'' ∈ V' ∩ mcPts (mCoordIdeal M'.x), ∀ w' ∈ V, SameOrbit w' (b'' ∘ Cv.v) → SameOrbit (s w') b'') → ∃ (U : Set ((Σ k, ι k) → ℂ)) (U' : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ), IsOpen U ∧ w₀ ∈ U ∧ IsOpen U' ∧ z ∈ U' ∧ AnalyticOnNhd ℂ f U ∧ ∀ z'' ∈ U' ∩ mcPts (mCoordIdeal y'), ∀ w ∈ U ∩ mcPts (mCoordIdeal y), CovMap.IsImg Cv z'' w → SameOrbit (f w) z'' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d hP hP' z hz w₀ hw₀ hImg V V' s hV hw₀V hV' hzV' hs hsO
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨Q1, Q2, Q3⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  have hb := Q1 z hz
  have hwb₀ := P1 w₀ hw₀
  have hbase := GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP' z hz w₀ hImg
  obtain ⟨F', hF', hG'⟩ := Q2 _ hb
  obtain ⟨F, hF, hG⟩ := P2 _ hwb₀
  obtain ⟨W₁, hW₁o, hW₁m, hW₁s, hW₁g⟩ := good_open M F hwb₀ hG
  obtain ⟨W₂, hW₂o, hW₂m, hW₂s, hW₂g⟩ := good_open M' F' hb hG'
  have hbv : basePart M'.blk z ∘ Cv.v ∈ W₁ := hW₁s _ _ (Cj.sameOrbit_symm hbase) hW₁m
  obtain ⟨W₃, rT, hW₃o, hW₃m, hW₃s, hrTa, hrTv⟩ := exists_value_family hb
    (fun q : Ψ × Fin N × Fin N => ((F'.T q.1)⁻¹ * (F.T q.1).map Cv.φ) q.2.1 q.2.2)
    fun q => (Cv.agree _ hb F' F hF' hF hG' (hW₁g _ hbv) q.1 q.2.1 q.2.2).2
  obtain ⟨W₄, rU, hW₄o, hW₄m, hW₄s, hrUa, hrUv⟩ := exists_value_family hb
    (fun q : (Σ k, ι' k) × Finset (Fin N) => F'.u q.1 q.2) fun q => (hG'.2.1 q.1 q.2).1
  obtain ⟨W₅, rV, hW₅o, hW₅m, hW₅s, hrVa, hrVv⟩ := exists_value_family hwb₀
    (fun q : Finset (Fin N) × (Σ k, ι k) => F.u' q.1 q.2) fun q => (hG.2.1 q.2 q.1).2
  have hs₀ : SameOrbit (s (basePart M.blk w₀)) (basePart M'.blk z) := hsO _ ⟨hzV', hb⟩ _ hw₀V hbase
  have hbpc : Continuous (basePart M.blk : ((Σ k, ι k) → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) :=
    continuous_pi fun q => continuous_apply _
  have hbpc' : Continuous (basePart M'.blk : ((Σ k, ι' k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ) :=
    continuous_pi fun q => continuous_apply _
  have hvc : Continuous fun t : (Σ k, baseIdx ι' M'.blk k) → ℂ => t ∘ Cv.v :=
    continuous_pi fun q => continuous_apply _
  have hbpa : ∀ w, AnalyticAt ℂ (basePart M.blk : ((Σ k, ι k) → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) w := fun w =>
    analyticAt_pi_iff.2 fun q => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨q.1.1, q.2⟩).analyticAt w
  let S : ((Σ k, ι k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ := fun w => s (basePart M.blk w)
  let U : Set ((Σ k, ι k) → ℂ) := basePart M.blk ⁻¹' ((V ∩ s ⁻¹' (W₃ ∩ W₄)) ∩ W₅)
  let U' : Set ((Σ k, ι' k) → ℂ) :=
    basePart M'.blk ⁻¹' ((V' ∩ W₂) ∩ (fun t => t ∘ Cv.v) ⁻¹' W₁)
  have hUo : IsOpen U := ((hs.continuousOn.isOpen_inter_preimage hV (hW₃o.inter hW₄o)).inter hW₅o).preimage hbpc
  have hU'o : IsOpen U' := ((hV'.inter hW₂o).inter (hW₁o.preimage hvc)).preimage hbpc'
  have hSa : ∀ w ∈ U, AnalyticAt ℂ S w := fun w hw => (hs _ hw.1.1).comp (hbpa w)
  let Tm : Ψ → ((Σ k, baseIdx ι' M'.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ :=
    fun τ t => Matrix.of fun a b => rT (τ, a, b) t
  let G : ∀ (p : Ψ × Fin N) (k' : K') (k : K), ((Σ k, ι k) → ℂ) → ι' k' → ℂ := fun p k' k w m' =>
    ∑ I, rU (⟨k', m'⟩, I) (S w) * ∑ I', if IsStepRows N j p.2 I' then
      minorIJ (Tm p.1 (S w)) I I' * ∑ m : ι k, rV (I', ⟨k, m⟩) (basePart M.blk w) * w ⟨k, m⟩ else 0
  have core : ∀ z'' ∈ U' ∩ mcPts (mCoordIdeal y'), ∀ w ∈ U ∩ mcPts (mCoordIdeal y), CovMap.IsImg Cv z'' w →
      SameOrbit (S w) (basePart M'.blk z'') ∧ ∀ p k' k, M'.blk p = some k' → M.blk p = some k →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ m', G p k' k w m' = c * z'' ⟨k', m'⟩ := by
    rintro z'' ⟨hzU, hzp⟩ w ⟨hwU, hwp⟩ hI
    have hb'' := Q1 z'' hzp
    have hg'' := hW₂g _ hzU.1.2
    obtain ⟨z₁, hz₁o, hz₁n⟩ := exists_normalised M' F' (z := z'') fun k => ne_zero_of_X_notMem (hg''.1 k)
    have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mem_mcPts_of_sameOrbit hP'.2.1.2.1 hz₁o hzp
    have ho₁ := basePart_orbit M'.blk hz₁o
    have ht := Q1 z₁ hz₁
    have htW₂ := hW₂s _ _ ho₁ hzU.1.2
    have htv := hW₁s _ _ (comp_orbit Cv.block ho₁) hzU.2
    have hgt := hW₂g _ htW₂
    have hgv := hW₁g _ htv
    obtain ⟨h, hh⟩ := (Q3 F' hF' z₁ ht hgt hz₁n).1 hz₁
    obtain ⟨z₀, hz₀w, hz₀b, hz₀f⟩ := hI z₁ hz₁o F' F hF' hF hgt hgv h hh
    have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) := mem_mcPts_of_sameOrbit hP.2.1.2.1 hz₀w hwp
    have hwb : SameOrbit (basePart M.blk w) (basePart M'.blk z'' ∘ Cv.v) :=
      Cj.sameOrbit_trans (basePart_orbit M.blk (Cj.sameOrbit_symm hz₀w))
        (Cj.sameOrbit_trans hz₀b (comp_orbit Cv.block ho₁))
    have hsw : SameOrbit (S w) (basePart M'.blk z'') := hsO _ ⟨hzU.1.1, hb''⟩ _ hwU.1.1 hwb
    refine ⟨hsw, fun p k' k hp' hp => ?_⟩
    have hb₀ := P1 z₀ hz₀
    have hb₀W := hW₁s _ _ hz₀b htv
    have hg₀ := hW₁g _ hb₀W
    obtain ⟨a', ha', e1⟩ := hh.2.2 p k' hp'
    obtain ⟨a, ha, e0⟩ := hz₀f.2.2 p k hp
    obtain ⟨c, hc, hcm⟩ := flag_transfer N j p.2 M.j_le
      (fun m I => valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z₀))
      (fun I m => valAt M.x (F.u' I ⟨k, m⟩) (basePart M.blk z₀))
      (fun m I => valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk z₁))
      (Matrix.of fun a b => valAt M'.x (((F'.T p.1)⁻¹ * (F.T p.1).map Cv.φ) a b) (basePart M'.blk z₁))
      (Cv.trans F' F (basePart M'.blk z₁) p.1) (h p.1) a a' (fun m => z₀ ⟨k, m⟩) (fun m => z₁ ⟨k', m⟩)
      (fun I I' hI hI' => left_inv_val M F hF hb₀ hg₀ p k hp I I' hI hI')
      (val_inv M M' Cv ht F' F hF' hF hgt hgv p.1) (hz₀f.2.1 p.1).1 ha ha' e0 e1
    have ht' : SameOrbit (basePart M'.blk z₁) (S w) := Cj.sameOrbit_trans ho₁ (Cj.sameOrbit_symm hsw)
    have hU : ∀ q, valAt M'.x (F'.u q.1 q.2) (basePart M'.blk z₁) = rU q (S w) := fun q =>
      valAt_eq ht (isValueAt_orbit (hrUv q _ hwU.1.2.2).1 ht')
    have hT : (Matrix.of fun a b => valAt M'.x (((F'.T p.1)⁻¹ * (F.T p.1).map Cv.φ) a b) (basePart M'.blk z₁)) =
        Tm p.1 (S w) := by
      ext a b
      exact valAt_eq ht (isValueAt_orbit (hrTv (p.1, a, b) _ hwU.1.2.1).1 ht')
    have hVv : ∀ I m, valAt M.x (F.u' I ⟨k, m⟩) (basePart M.blk z₀) = rV (I, ⟨k, m⟩) (basePart M.blk w) := fun I m =>
      valAt_eq hb₀ (isValueAt_orbit (hrVv (I, ⟨k, m⟩) _ hwU.2).1 (basePart_orbit M.blk hz₀w))
    obtain ⟨c₀, hc₀, e₀⟩ := hz₀w
    obtain ⟨c₁, hc₁, e₁⟩ := hz₁o
    have key : ∀ m', z₁ ⟨k', m'⟩ = c * c₀ k * G p k' k w m' := by
      intro m'
      rw [hcm m', mul_assoc]
      congr 1
      simp only [G]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      have h1 := hU (⟨k', m'⟩, I)
      simp only at h1
      rw [h1, mul_left_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I' _ => ?_
      split_ifs
      · rw [hT, mul_left_comm]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hVv, congrFun e₀ ⟨k, m⟩]
        ring
      · simp
    have hcc : c * c₀ k ≠ 0 := mul_ne_zero hc (hc₀ k)
    refine ⟨(c * c₀ k)⁻¹ * c₁ k', mul_ne_zero (inv_ne_zero hcc) (hc₁ k'), fun m' => ?_⟩
    have h1 := key m'
    rw [congrFun e₁ ⟨k', m'⟩] at h1
    rw [mul_assoc]
    exact (inv_mul_eq_iff_eq_mul₀ hcc).2 h1 |>.symm ▸ rfl
  have hw₀U : w₀ ∈ U := ⟨⟨hw₀V, hW₃s _ _ hs₀ hW₃m, hW₄s _ _ hs₀ hW₄m⟩, hW₅m⟩
  have hzU' : z ∈ U' := ⟨⟨hzV', hW₂m⟩, hbv⟩
  have hblk : ∀ k', ∃ fk : ((Σ k, ι k) → ℂ) → ι' k' → ℂ, (∀ m, ∀ w ∈ U, AnalyticAt ℂ (fun w => fk w m) w) ∧
      ∀ z'' ∈ U' ∩ mcPts (mCoordIdeal y'), ∀ w ∈ U ∩ mcPts (mCoordIdeal y), CovMap.IsImg Cv z'' w →
        ∃ c : ℂ, c ≠ 0 ∧ ∀ m, fk w m = c * z'' ⟨k', m⟩ := by
    intro k'
    by_cases h : ∃ p, M'.blk p = some k'
    · obtain ⟨p, hp'⟩ := h
      have hk : ∃ k, M.blk p = some k := by
        have h1 : M'.blk p ≠ none := by rw [hp']; simp
        have h2 : IsProperStep N j p.2 := by_contra fun e => h1 ((M'.blk_none p).2 e)
        exact Option.ne_none_iff_exists'.1 fun e => ((M.blk_none p).1 e) h2
      obtain ⟨k, hp⟩ := hk
      refine ⟨G p k' k, fun m w hw => ?_, fun z'' hz'' w hw hI => (core z'' hz'' w hw hI).2 p k' k hp' hp⟩
      have aU : ∀ q, AnalyticAt ℂ (fun w => rU q (S w)) w := fun q => (hrUa q (S w) hw.1.2.2).comp (hSa w hw)
      have aT : ∀ q, AnalyticAt ℂ (fun w => rT q (S w)) w := fun q => (hrTa q (S w) hw.1.2.1).comp (hSa w hw)
      have aV : ∀ q, AnalyticAt ℂ (fun w => rV q (basePart M.blk w)) w := fun q => (hrVa q _ hw.2).comp (hbpa w)
      have aw : ∀ q : Σ k, ι k, AnalyticAt ℂ (fun w : (Σ k, ι k) → ℂ => w q) w := fun q =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt w
      refine Finset.analyticAt_fun_sum _ fun I _ => (aU _).fun_mul (Finset.analyticAt_fun_sum _ fun I' _ => ?_)
      by_cases hst : IsStepRows N j p.2 I'
      · simp only [if_pos hst]
        exact (minor_analytic _ _ _ _ fun a b => aT _).fun_mul
          (Finset.analyticAt_fun_sum _ fun m _ => (aV _).fun_mul (aw _))
      · simp only [if_neg hst]
        exact analyticAt_const
    · have h' : ∀ p, M'.blk p ≠ some k' := fun p e => h ⟨p, e⟩
      refine ⟨fun w m => S w ⟨⟨k', h'⟩, m⟩, fun m w hw => analyticAt_pi_iff.1 (hSa w hw) ⟨⟨k', h'⟩, m⟩,
        fun z'' hz'' w hw hI => ?_⟩
      obtain ⟨c, hc, e⟩ := (core z'' hz'' w hw hI).1
      exact ⟨c ⟨k', h'⟩, hc _, fun m => congrFun e ⟨⟨k', h'⟩, m⟩⟩
  choose fk hfa hfc using hblk
  refine ⟨U, U', fun w q => fk q.1 w q.2, hUo, hw₀U, hU'o, hzU', fun w hw => ?_, ?_⟩
  · exact analyticAt_pi_iff.2 fun q => hfa q.1 q.2 w hw
  · intro z'' hz'' w hw hI
    choose c hc hm using fun k' => hfc k' z'' hz'' w hw hI
    exact ⟨c, hc, funext fun q => hm q.1 q.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovLift
