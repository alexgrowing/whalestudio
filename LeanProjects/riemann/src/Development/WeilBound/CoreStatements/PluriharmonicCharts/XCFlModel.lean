import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_fl_model

section Point

theorem an0 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : (Fin 0 → ℂ) → E) (U : Set (Fin 0 → ℂ)) :
    AnalyticOnNhd ℂ f U := by
  intro x _
  have e : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
  rw [e]
  exact analyticAt_const

theorem ball0 (w : Fin 0 → ℂ) : w ∈ Metric.ball (0 : Fin 0 → ℂ) 1 := by
  rw [Subsingleton.elim w 0]
  exact Metric.mem_ball_self one_pos

def ptA : FinHolAtlas 0 (Fin 0 → ℂ) where
  n := 1
  chart _ := OpenPartialHomeomorph.refl _
  cover _ := ⟨0, trivial⟩
  holo _ _ := an0 _ _

theorem snc0 (L : LocPot (Fin 0 → ℂ)) (s : (Fin 0 → ℂ) → (Fin 0 → ℂ) → ℂ) (hs : ∀ x y, s x y ≠ 0) :
    IsSNC ptA L s (Fin.elim0 : Fin 0 → ℕ) Fin.elim0 := fun x =>
  ⟨OpenPartialHomeomorph.refl _, fun _ => ⟨an0 _ _, an0 _ _⟩, trivial,
    fun y _ => by rw [Subsingleton.elim y x]; exact L.mem_U x, Fin.elim0, fun k => k.elim0, fun k => k.elim0,
    s x, fun _ => an0 _ _, fun y _ => hs x y, fun y _ => by simp⟩

variable {K : Type} [Fintype K] [IsEmpty K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

instance : IsEmpty (Σ k, ι k) := ⟨fun q => isEmptyElim q.1⟩

theorem mem_pts (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : z ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => isEmptyElim k, fun f hf => ?_⟩
  have hf' : f = C (f.coeff 0) := MvPolynomial.eq_C_of_isEmpty f
  rw [mCoordIdeal, RingHom.mem_ker] at hf
  rw [hf'] at hf ⊢
  simp at hf ⊢
  exact hf

theorem not_mem_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  simpa using h.2 1 trivial

theorem homog (f : MRing ι) (d : K → ℕ) : IsMultiHomog f d := fun _ _ k => isEmptyElim k

theorem orbit (z z' : (Σ k, ι k) → ℂ) : SameOrbit z z' := ⟨fun _ => 1, fun _ => one_ne_zero, funext fun p => isEmptyElim p⟩

theorem regAt_int (x : (Σ k, ι k) → Ω) {Q : Ideal (MRing ι)} (hQ : Q.IsPrime) (n : ℤ) : RegAt x Q (n : Ω) :=
  ⟨fun _ => 0, C n, 1, homog _ _, homog _ _, fun h => hQ.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩

theorem valAt_int (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) : valAt x (n : Ω) z = n :=
  valAt_eq (mem_pts x z) ⟨fun _ => 0, C n, 1, homog _ _, homog _ _, by simp, by simp, by simp, by simp⟩

def ptRes (x : (Σ k, ι k) → Ω) : AnLogRes (mCoordIdeal x) ⊤ 0 where
  homog := ⟨{1}, fun f _ => ⟨fun _ => 0, homog _ _⟩, by simp⟩
  nondeg h := (RingHom.ker_isPrime (mConeMap x)).ne_top (top_le_iff.1 h)
  X := Fin 0 → ℂ
  A := ptA
  U _ := Set.univ
  isOpen_U _ := isOpen_univ
  mem_U _ := trivial
  lift _ _ := 0
  holo _ _ _ := an0 _ _
  mem _ _ _ := mem_pts _ _
  compat _ _ _ _ := orbit _ _
  surj _ _ _ := ⟨0, orbit _ _⟩
  inj _ _ _ _ := Subsingleton.elim _ _
  immersion _ _ _ _ _ _ := Subsingleton.elim _ _
  snc f _ _ _ h := ⟨0, _, _, snc0 _ _ fun _ _ e => not_mem_top _ (h _ (mem_pts _ _) e)⟩
  null j := by simp [not_mem_top]

end Point

section Minors

variable {R : Type} [CommRing R] {N : ℕ}

theorem minorIJ_eq (h : Matrix (Fin N) (Fin N) R) {I J : Finset (Fin N)} {s : ℕ} (hI : I.card = s) (hJ : J.card = s) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  exact dif_pos hI

theorem minorIJ_one (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl]
  have : (1 : Matrix (Fin N) (Fin N) R).submatrix ⇑(I.orderEmbOfFin rfl) ⇑(I.orderEmbOfFin rfl) = 1 :=
    Matrix.submatrix_one_embedding (I.orderEmbOfFin rfl).toEmbedding
  rw [this, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [detFac, minorIJ_one]

private theorem det_submatrix_orderEmbOfFin_congr {a b : ℕ} (hab : a = b) (M : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (p1 : J.card = a) (p2 : I.card = a) (p3 : J.card = b) (p4 : I.card = b) :
    (M.submatrix (J.orderEmbOfFin p1) (I.orderEmbOfFin p2)).det =
      (M.submatrix (J.orderEmbOfFin p3) (I.orderEmbOfFin p4)).det := by
  subst hab
  rfl

theorem minorIJ_conj (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) :
    minorIJ hᴴ J I = star (minorIJ h I J) := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · rw [dif_pos e.symm, dif_pos e, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]
    exact det_submatrix_orderEmbOfFin_congr e _ _ _ _ _ _ _
  · rw [dif_neg (fun e' => e e'.symm), dif_neg e, star_zero]

def im {s : ℕ} (A : PlueckerData.Incr s N) : Finset (Fin N) := Finset.univ.image A.1

theorem card_im {s : ℕ} (A : PlueckerData.Incr s N) : (im A).card = s := by
  simp [im, Finset.card_image_of_injective _ A.2.injective]

theorem emb_im {s : ℕ} (A : PlueckerData.Incr s N) : ⇑((im A).orderEmbOfFin (card_im A)) = A.1 := (Finset.orderEmbOfFin_unique (card_im A) (fun x => by simp [im]) A.2).symm

theorem im_inj {s : ℕ} : Function.Injective (im : PlueckerData.Incr s N → _) := by
  intro A B h
  apply Subtype.ext
  rw [← emb_im A]
  exact (Finset.orderEmbOfFin_unique (card_im A) (fun x => by rw [h]; simp [im]) B.2).symm

theorem exists_im {s : ℕ} (I : Finset (Fin N)) (h : I.card = s) : ∃ A : PlueckerData.Incr s N, im A = I := by
  refine ⟨⟨I.orderEmbOfFin h, (I.orderEmbOfFin h).strictMono⟩, ?_⟩
  ext a
  simp only [im, Finset.mem_image, Finset.mem_univ, true_and]
  rw [← Set.mem_range, Finset.range_orderEmbOfFin]
  rfl

theorem cols_eq (i : Fin N) (hi : (i : ℕ) + 1 ≤ N) :
    stepCols N N i = im ⟨Fin.castLE hi, Fin.strictMono_castLE _⟩ := by
  ext a
  simp only [stepCols, im, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi, Finset.mem_image]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨⟨a, by omega⟩, Fin.ext (by simp)⟩
  · rintro ⟨b, rfl⟩
    simp
    omega

theorem card_cols (i : Fin N) : (stepCols N N i).card = i + 1 := by
  rw [cols_eq i (by omega), card_im]

theorem minor_im (h : Matrix (Fin N) (Fin N) R) (i : Fin N) (hi : (i : ℕ) + 1 ≤ N)
    (A : PlueckerData.Incr (i + 1) N) :
    minorIJ h (im A) (stepCols N N i) = (h.submatrix A.1 (Fin.castLE hi)).det := by
  rw [minorIJ_eq h (card_im A) (card_cols i), emb_im]
  congr 2
  exact (Finset.orderEmbOfFin_unique (card_cols i) (fun x => by rw [cols_eq i hi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ x)) (Fin.strictMono_castLE hi)).symm

theorem gram (h : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) [Fintype (PlueckerData.Incr (i + 1) N)] :
    (minorIJ (hᴴ * 1 * h) (stepCols N N i) (stepCols N N i)).re =
      ∑ A : PlueckerData.Incr (i + 1) N, ‖minorIJ h (im A) (stepCols N N i)‖ ^ 2 := by
  have hS := card_cols (N := N) i
  rw [mul_one, MinorCalc.minorIJ_mul]
  simp only [minorIJ_conj]
  rw [Complex.re_sum]
  have hterm : ∀ I' : Finset (Fin N),
      (star (minorIJ h I' (stepCols N N i)) * minorIJ h I' (stepCols N N i)).re =
        ‖minorIJ h I' (stepCols N N i)‖ ^ 2 := by
    intro I'
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [hterm]
  rw [← Finset.sum_image (f := fun I => ‖minorIJ h I (stepCols N N i)‖ ^ 2)
    (fun A _ B _ e => im_inj e)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro I' _ hI'
  have hc : I'.card ≠ (stepCols N N i).card := by
    intro e
    rw [hS] at e
    obtain ⟨A, hA⟩ := exists_im (s := (i : ℕ) + 1) I' e
    exact hI' (Finset.mem_image.2 ⟨A, Finset.mem_univ _, hA⟩)
  simp [minorIJ, hc]

theorem blockDiag (h : Matrix (Fin N) (Fin N) R) : IsBlockDiag N h := by
  intro a b hab
  simp at hab

end Minors

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def blk : Ψ × Fin N → Option (FlBlock Ψ N) := fun p =>
  if h : (p.2 : ℕ) + 1 < N then some (p.1, ⟨p.2, by omega⟩) else none

variable {Ψ N}

def stp (k : FlBlock Ψ N) : Ψ × Fin N := (k.1, ⟨k.2, by have := k.2.2; omega⟩)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem blk_some {p : Ψ × Fin N} {k : FlBlock Ψ N} : blk Ψ N p = some k ↔ p = stp k := by
  rcases p with ⟨a, i⟩
  rcases k with ⟨b, j⟩
  have hj := j.2
  unfold blk stp
  split_ifs with h
  · simp [Prod.ext_iff, Fin.ext_iff]
  · simp only [reduceCtorEq, false_iff, Prod.mk.injEq, not_and]
    intro _ e
    apply h
    rw [e]
    simp
    omega

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem blk_none {p : Ψ × Fin N} : blk Ψ N p = none ↔ ¬ IsProperStep N N p.2 := by
  have := p.2.2
  unfold blk IsProperStep
  split_ifs with h
  · simp; omega
  · simp; omega

instance : IsEmpty (NonPluckerBlocks (blk Ψ N)) := ⟨fun k => k.2 (stp k.1) (blk_some.2 rfl)⟩

def coef (q : Σ k, FlIdx Ψ N k) (I : Finset (Fin N)) : ℚ := if I = im q.2 then 1 else 0

variable (Ψ N)

def frame : FrameData (FlIdx Ψ N) Ψ N ℚ (blk Ψ N) where
  c k := isEmptyElim k
  T _ := 1
  u := coef
  u' I q := coef q I
  υ _ := 1

theorem good (x : (Σ k, baseIdx (FlIdx Ψ N) (blk Ψ N) k) → ℚ) (Q : Ideal (MRing (baseIdx (FlIdx Ψ N) (blk Ψ N))))
    (hQ : Q.IsPrime) :
    (∀ k, (X ⟨k, (frame Ψ N).c k⟩ : MRing (baseIdx (FlIdx Ψ N) (blk Ψ N))) ∉ Q) ∧
      (∀ q I, RegAt x Q ((frame Ψ N).u q I) ∧ RegAt x Q ((frame Ψ N).u' I q)) ∧
        ∀ p, blk Ψ N p = none → (frame Ψ N).υ p ≠ 0 ∧ RegAt x Q ((frame Ψ N).υ p) ∧ RegAt x Q ((frame Ψ N).υ p)⁻¹ := by
  have r1 : RegAt x Q (1 : ℚ) := by simpa using regAt_int x hQ 1
  have r0 : RegAt x Q (0 : ℚ) := by simpa using regAt_int x hQ 0
  refine ⟨fun k => isEmptyElim k, fun q I => ?_, fun p _ => ⟨one_ne_zero, ?_, ?_⟩⟩
  · by_cases e : I = im q.2
    · simp only [frame, coef, if_pos e]
      exact ⟨r1, r1⟩
    · simp only [frame, coef, if_neg e]
      exact ⟨r0, r0⟩
  · simpa [frame] using r1
  · simpa [frame] using r1

theorem left_inv (p : Ψ × Fin N) (k : FlBlock Ψ N) (hp : blk Ψ N p = some k) (I I' : Finset (Fin N))
    (hI : IsStepRows N N p.2 I) :
    ∑ m : FlIdx Ψ N k, coef ⟨k, m⟩ I * coef ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
  obtain rfl := blk_some.1 hp
  have hc : I.card = (k.2 : ℕ) + 1 := by
    rw [hI.1, card_cols]
    rfl
  obtain ⟨m0, hm0⟩ := exists_im (N := N) I hc
  rw [Finset.sum_eq_single m0]
  · subst hm0
    by_cases e : im m0 = I'
    · simp [coef, e]
    · have e' : ¬ I' = im m0 := fun h => e h.symm
      simp [coef, e, e']
  · intro m _ hm
    have : ¬ I = im m := fun h => hm (im_inj (h.symm.trans hm0.symm))
    simp [coef, this]
  · simp

def model : FlagModel (yFl Ψ N) Ψ N N where
  j_le := le_rfl
  Ω := ℚ
  blk := blk Ψ N
  blk_none _ := blk_none
  blk_inj _ _ _ h h' := (blk_some.1 h).trans (blk_some.1 h').symm
  x _ := 0
  x_ne k := isEmptyElim k
  y_base q := isEmptyElim q
  g τ := Matrix.of fun a b => algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (X (τ, b, a))
  g_block _ := blockDiag _
  g_indep := by
    refine IsGenericFlag.of_indep (fun _ => blockDiag _) ?_
    refine AlgebraicIndependent.map' (x := fun q : inertBlockIndex Ψ N N =>
      (X (q.1.1, q.1.2.2, q.1.2.1) : MvPolynomial (Ψ × Fin N × Fin N) ℚ))
      (f := (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)).toRatAlgHom) ?_
      (IsFractionRing.injective _ _)
    refine (algebraicIndependent_X _ ℚ).comp (fun q : inertBlockIndex Ψ N N => (q.1.1, q.1.2.2, q.1.2.1)) ?_
    rintro ⟨⟨a, b, c⟩, _⟩ ⟨⟨a', b', c'⟩, _⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  coef := coef
  y_step p k hp m := by
    obtain rfl := blk_some.1 hp
    rw [Finset.sum_eq_single (im m) (fun I _ hI => by simp [coef, hI]) (by simp)]
    simp only [coef, if_true, map_one, one_mul]
    refine Eq.trans ?_ (minor_im _ (stp k).2 (step_le k.2) m).symm
    rw [yFl, RingHom.map_det, ← det_transpose]
    rfl
  b _ _ := 0
  lam _ := 1
  frames Q hQ _ _ := ⟨frame Ψ N, ⟨fun _ => ⟨blockDiag _, by simp [frame]⟩, fun p k _ m h _ => by
    simp [frame, detFac_one], fun p k hp I I' hI _ => left_inv Ψ N p k hp I I' hI,
    fun p _ => by simp [frame, detFac_one]⟩, good Ψ N _ Q hQ⟩

instance : IsEmpty (NonPluckerBlocks (model Ψ N).blk) := inferInstanceAs (IsEmpty (NonPluckerBlocks (blk Ψ N)))

theorem isFrame : (model Ψ N).IsFrame (frame Ψ N) :=
  ⟨fun _ => ⟨blockDiag _, show (1 : Matrix (Fin N) (Fin N) ℚ).det ≠ 0 by simp⟩,
    fun p k _ m (h : Matrix (Fin N) (Fin N) ℚ) _ =>
      show detFac N p.2 (1 : Matrix (Fin N) (Fin N) ℚ) *
        ∑ I, coef ⟨k, m⟩ I * minorIJ (1 * h) I (stepCols N N p.2) =
        (∏ _k' : NonPluckerBlocks (blk Ψ N), (0 : ℚ) ^ (0 : ℤ)) * ∑ I, coef ⟨k, m⟩ I * minorIJ h I (stepCols N N p.2) by
      simp [detFac_one],
    fun p k hp I I' hI _ => left_inv Ψ N p k hp I I' hI,
    fun p _ => show detFac N p.2 (1 : Matrix (Fin N) (Fin N) ℚ) * 1 =
      (∏ _k' : NonPluckerBlocks (blk Ψ N), (0 : ℚ) ^ (0 : ℤ)) * 1 by simp [detFac_one]⟩

theorem dy_eq (p : Ψ × Fin N) : (model Ψ N).dy p = fun q => if q.1 = p.1 ∧ (q.2 : ℕ) = p.2 then 1 else 0 := by
  funext q
  unfold FlagModel.dy
  rw [dif_neg (fun h => h (stp q) (blk_some.2 rfl))]
  have e : (model Ψ N).blk p = some q ↔ (q.1 = p.1 ∧ (q.2 : ℕ) = p.2) := by
    show blk Ψ N p = some q ↔ _
    rw [blk_some]
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    simp only [stp, Prod.mk.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h.symm⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, h.symm⟩
  by_cases hc : q.1 = p.1 ∧ (q.2 : ℕ) = p.2
  · rw [if_pos (e.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (e.1 h)), if_neg hc]

theorem periodGram : IsPeriodGram N (1 : Matrix (Fin N) (Fin N) ℂ) 1 := by
  have hE : ∀ a : {a : Fin N // (a : ℕ) < N - N}, False := fun a => by
    have := a.2
    omega
  refine ⟨⟨by simp, ?_⟩, fun h _ k => ?_⟩
  · refine ⟨?_, fun x hx => absurd (Finsupp.ext fun a => (hE a).elim) hx⟩
    ext a
    exact (hE a).elim
  · have hs : (diagonal fun i : Fin N => ((sigForm N N i : ℝ) : ℂ)) = 1 := by
      ext a b
      simp [sigForm, Matrix.diagonal_apply, Matrix.one_apply]
    simp only [gramHead, gramOf, hs, one_mul, mul_one, Matrix.conjTranspose_one]

theorem induced (zb) (p : Ψ × Fin N) : (model Ψ N).IsInducedAt (frame Ψ N) zb p 1 (yLineFl Ψ N p) := by
  intro z _ _ _ h _ _
  have v1 : valAt (model Ψ N).x (1 : ℚ) (basePart (model Ψ N).blk z) = 1 := by
    have h1 := valAt_int (model Ψ N).x (basePart (model Ψ N).blk z) 1
    push_cast at h1
    exact h1
  have v0 : valAt (model Ψ N).x (0 : ℚ) (basePart (model Ψ N).blk z) = 0 := by
    have h1 := valAt_int (model Ψ N).x (basePart (model Ψ N).blk z) 0
    push_cast at h1
    exact h1
  constructor
  · intro k hp hz
    obtain rfl := blk_some.1 hp
    have hpr : IsProperStep N N (stp k).2 := by
      have := k.2.2
      simp only [IsProperStep, stp]
      constructor <;> omega
    have hz' : ∀ m : FlIdx Ψ N k, z ⟨k, m⟩ = minorIJ h (im m) (stepCols N N (stp k).2) := by
      intro m
      rw [hz m, Finset.sum_eq_single (im m)]
      · simp [frame, coef, v1]
      · intro I _ hI
        simp [frame, coef, hI, v0]
      · simp
    have hA : (yLineFl Ψ N (stp k)).h z = (∑ m : FlIdx Ψ N k, ‖z ⟨k, m⟩‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      show refNorm _ z = _
      unfold refNorm
      rw [Finset.prod_eq_single k]
      · simp [stp]
      · intro q _ hq
        have : ¬ (q.1 = (stp k).1 ∧ (q.2 : ℕ) = (stp k).2) := by
          rintro ⟨e1, e2⟩
          exact hq (Prod.ext e1 (Fin.ext e2))
        simp [this]
      · simp
    have hg := gram h (stp k).2
    have hX : (∑ m : FlIdx Ψ N k, ‖z ⟨k, m⟩‖ ^ 2) =
        (minorIJ (hᴴ * 1 * h) (stepCols N N (stp k).2) (stepCols N N (stp k).2)).re := by
      simp only [hz']
      exact hg.symm
    have hnn : 0 ≤ (minorIJ (hᴴ * 1 * h) (stepCols N N (stp k).2) (stepCols N N (stp k).2)).re := by
      rw [← hX]
      positivity
    rw [hA, hX]
    simp only [blockPot, detFac_one, if_pos hpr, Complex.one_re, Real.log_one, mul_zero, zero_add]
    rcases hnn.lt_or_eq with hpos | h0
    · rw [Real.log_rpow hpos]
    · rw [← h0]
      simp
  · intro hp
    have hnp : ¬ IsProperStep N N p.2 := blk_none.1 hp
    have hp2 : ¬ ((p.2 : ℕ) + 1 < N) := by
      intro h'
      exact hnp ⟨by omega, by omega⟩
    have hv : valAt (model Ψ N).x ((frame Ψ N).υ p) (basePart (model Ψ N).blk z) = 1 := v1
    have hA : (yLineFl Ψ N p).h z = 1 := by
      show refNorm _ z = 1
      unfold refNorm
      apply Finset.prod_eq_one
      intro q _
      have : ¬ (q.1 = p.1 ∧ (q.2 : ℕ) = p.2) := by
        rintro ⟨-, e⟩
        have := q.2.2
        have := p.2.2
        omega
      simp [this]
    rw [hA, hv]
    simp [blockPot, detFac_one, hnp]

def metric : BaseMetric (model Ψ N) 0 where
  Rb := ptRes (model Ψ N).x
  L := LocPot.ofFun 0
  s _ _ := 1
  nb := 0
  m := Fin.elim0
  W := Fin.elim0
  potL := isPotential_ofFun _ _ fun _ => contDiffOn_const
  sec := ⟨fun _ _ => an0 _ _, fun _ _ _ _ => rfl⟩
  snc := snc0 _ _ fun _ _ => one_ne_zero
  norm_le x := by simp [logNormSec, LocPot.ofFun]
  Bat := ptA
  adapted := ⟨⟨fun _ _ => an0 _ _, fun _ _ => an0 _ _⟩, fun _ => Set.subset_univ _,
    fun x => ⟨(0 : Fin 1), trivial, ball0 _⟩,
    0, fun _ => ⟨∅, Fin.elim0, by simp, by simp [bdry], fun _ _ _ => by
      simp [rW, rLoc, logNormSec, LocPot.ofFun]⟩⟩
  q := 1
  O _ := Set.univ
  O_open _ := isOpen_univ
  O_cover _ := ⟨0, trivial⟩
  F _ := frame Ψ N
  isFrame _ := isFrame Ψ N
  good _ _ _ := good Ψ N _ _ (RingHom.ker_isPrime _)
  G _ _ _ := 1
  G_pos _ _ _ _ := ⟨blockDiag _, Matrix.PosDef.one⟩
  G_smooth _ _ _ _ := ⟨fun _ => contDiffOn_const, fun _ => contDiffOn_const⟩
  Cst := 0
  size _ _ _ _ := by simp [Matrix.PosSemidef.zero]
  grad _ _ _ _ _ _ _ _ := by simp
  period _ _ _ := ⟨Set.univ, fun _ _ => 1, trivial, isOpen_univ, fun _ _ _ _ => an0 _ _, fun _ _ _ => periodGram N⟩
  immersion := ⟨0, (0 : Fin 0 → ℂ), ⟨trivial, fun h => one_ne_zero (α := ℂ) h⟩, Set.univ, fun _ _ => 1, trivial,
    ⟨isOpen_univ, fun _ _ _ _ => an0 _ _, fun _ _ _ => periodGram N⟩, fun _ _ _ _ => Subsingleton.elim _ _⟩
  hom := yLineFl Ψ N
  hom_deg p := (dy_eq Ψ N p).symm
  induced _ _ _ p := induced Ψ N _ p

end PositivityTheory.Xgp.c_fl_model

end

theorem PositivityTheory.Xgp.t_c_fl_model : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∃ (M : FlagModel (yFl Ψ N) Ψ N N) (BM : BaseMetric M 0), (∀ p, BM.hom p = yLineFl Ψ N p) ∧ (∀ p, fsHerm (FlIdx Ψ N) (M.dy p) = yLineFl Ψ N p) ∧ bdry BM.s = ∅ := by
  intro Ψ _ _ _ N _
  refine ⟨PositivityTheory.Xgp.c_fl_model.model Ψ N, PositivityTheory.Xgp.c_fl_model.metric Ψ N, fun _ => rfl, fun p => ?_, ?_⟩
  · rw [PositivityTheory.Xgp.c_fl_model.dy_eq]
    rfl
  · exact Set.eq_empty_of_forall_notMem fun _ h => one_ne_zero (α := ℂ) h
