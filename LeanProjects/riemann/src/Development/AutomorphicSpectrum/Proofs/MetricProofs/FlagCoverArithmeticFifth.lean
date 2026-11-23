import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThirdStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.FibreCount

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b b' : (Σ k, ι' k) → ℂ} (h : SameOrbit b b') :
    SameOrbit (b ∘ v) (b' ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext p
  simp only [Function.comp]
  rw [hv.2.2.1 p]

theorem mCoordIdeal_le_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  intro f hf
  let φ : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ := aeval fun k => C (c k) * X k
  have e : mConeMap (fun p : Σ k, ι k => c p.1 * z' p) = (φ.restrictScalars ℤ).comp (mConeMap z') := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, φ, mul_left_comm, mul_assoc]
  have h0 : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [e, AlgHom.comp_apply, h0, map_zero]

theorem mCoordIdeal_eq_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le_of_orbit (Cj.sameOrbit_symm h)) (mCoordIdeal_le_of_orbit h)

theorem chart_ne {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun h0 => h (by
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem exists_normal (c : ∀ k, ι k) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) :
    ∃ z₁, SameOrbit z₁ z ∧ ∀ k, z₁ ⟨k, c k⟩ = 1 :=
  ⟨fun p => (z ⟨p.1, c p.1⟩)⁻¹ * z p, ⟨fun k => (z ⟨k, c k⟩)⁻¹, fun k => inv_ne_zero (hc k), rfl⟩,
    fun k => inv_mul_cancel₀ (hc k)⟩

theorem exists_normal_base {σ : Type} (blk : σ → Option K) (c : ∀ k : NonPluckerBlocks blk, baseIdx ι blk k)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, basePart blk z ⟨k, c k⟩ ≠ 0) :
    ∃ z₁, SameOrbit z₁ z ∧ ∀ k, basePart blk z₁ ⟨k, c k⟩ = 1 := by
  let t : K → ℂ := fun k => if hk : ∀ p, blk p ≠ some k then (z ⟨k, c ⟨k, hk⟩⟩)⁻¹ else 1
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases hk : ∀ p, blk p ≠ some k
    · simp only [t, dif_pos hk]
      exact inv_ne_zero (hc ⟨k, hk⟩)
    · simp only [t, dif_neg hk]
      exact one_ne_zero
  refine ⟨fun p => t p.1 * z p, ⟨t, ht, rfl⟩, fun k => ?_⟩
  obtain ⟨k, hk⟩ := k
  show t k * z ⟨k, c ⟨k, hk⟩⟩ = 1
  simp only [t, dif_pos hk]
  exact inv_mul_cancel₀ (hc ⟨k, hk⟩)

theorem eq_of_orbit_normal {c : ∀ k, ι k} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hz : ∀ k, z ⟨k, c k⟩ = 1) (hz' : ∀ k, z' ⟨k, c k⟩ = 1) : z = z' := by
  obtain ⟨t, ht, rfl⟩ := h
  have h1 : ∀ k, t k = 1 := fun k => by
    have := hz k
    simp only [hz' k, mul_one] at this
    exact this
  funext p
  simp [h1]

theorem orbit_eq_iff {z z' : (Σ k, ι k) → ℂ} :
    {z'' | SameOrbit z'' z} = {z'' | SameOrbit z'' z'} ↔ SameOrbit z z' := by
  constructor
  · intro h
    have : z ∈ {z'' | SameOrbit z'' z} := Cj.sameOrbit_refl z
    rw [h] at this
    exact this
  · intro h
    ext z''
    exact ⟨fun a => Cj.sameOrbit_trans a h, fun a => Cj.sameOrbit_trans a (Cj.sameOrbit_symm h)⟩

theorem sameOrbit_of_blocks {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (hb : basePart blk z = basePart blk z')
    (h : ∀ p k, blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩) : SameOrbit z z' := by
  have h' : ∀ k, ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := fun k => by
    by_cases hk : ∀ p, blk p ≠ some k
    · refine ⟨1, one_ne_zero, fun m => ?_⟩
      rw [one_mul]
      exact congrFun hb ⟨⟨k, hk⟩, m⟩
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      exact h p k hp
  choose a ha hm using h'
  exact ⟨a, ha, funext fun q => hm q.1 q.2⟩

variable {Ω : Type} [Field Ω]

theorem isValueAt_of_regAt {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (h : RegAt x (mCoordIdeal z) s) : IsValueAt x s z (valAt x s z) := by
  obtain ⟨d, g, q, hg, hq, hQ, e⟩ := h
  have h1 : eval z (map (Int.castRingHom ℂ) q) ≠ 0 := fun h0 => hQ
    (mem_mCoordIdeal_of_aeval_eq_zero z hq (by rw [aeval_def, algebraMap_int_eq, ← eval_map]; exact h0))
  have h2 : aeval x q ≠ 0 := fun h0 => h1 (hz.2 q (mem_mCoordIdeal_of_aeval_eq_zero x hq h0))
  have hv : IsValueAt x s z (eval z (map (Int.castRingHom ℂ) g) / eval z (map (Int.castRingHom ℂ) q)) :=
    ⟨d, g, q, hg, hq, h2, e, h1, rfl⟩
  rw [valAt_eq hz hv]
  exact hv

theorem isValueAt_sum' {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {α : Type} (s : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i, IsValueAt x (f i) z (v i)) : IsValueAt x (∑ i ∈ s, f i) z (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_intCast x z 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a) ih

end Orbits

section Flags

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

theorem stepCols_nonempty {i : Fin N} (h : IsProperStep N j i) : (stepCols N j i).Nonempty := by
  have hN : 0 < N := i.pos
  have h1 := h.1
  by_cases hi : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, hi, if_true, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · refine ⟨⟨0, hN⟩, ?_⟩
    simp only [stepCols, hi, if_false, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem minor_off_step (hj : j ≤ N) {i : Fin N} (hp : IsProperStep N j i) {h : Matrix (Fin N) (Fin N) ℂ}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hI : ¬ IsStepRows N j i I) : minorIJ h I (stepCols N j i) = 0 :=
  ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.1 h I hh hI).resolve_right (stepCols_nonempty hp).ne_empty

theorem minors_of_mul (hj : j ≤ N) (i : Fin N) {T h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} (hT : T.det ≠ 0)
    {C : Finset (Fin N)} {c : ℂ} (h : ∀ I, minorIJ (T * h₁) I C = c * minorIJ (T * h₂) I C) (I : Finset (Fin N)) :
    minorIJ h₁ I C = c * minorIJ h₂ I C := by
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).1
  have hu : IsUnit T.det := hT.isUnit
  calc minorIJ h₁ I C = minorIJ (T⁻¹ * (T * h₁)) I C := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
    _ = ∑ I', minorIJ T⁻¹ I I' * minorIJ (T * h₁) I' C := cb _ _ _ _
    _ = c * ∑ I', minorIJ T⁻¹ I I' * minorIJ (T * h₂) I' C := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I' _ => by rw [h I']; ring
    _ = c * minorIJ (T⁻¹ * (T * h₂)) I C := by rw [← cb]
    _ = c * minorIJ h₂ I C := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem plucker_inj (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F)
    {b : (Σ k, baseIdx ι M.blk k) → ℂ} (hb : b ∈ mcPts (mCoordIdeal M.x)) (hg : M.GoodAt F (mCoordIdeal b))
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (P : Finset (Fin N) → ℂ)
    (hP : ∀ I, ¬ IsStepRows N j p.2 I → P I = 0)
    (h0 : ∀ m : ι k, ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * P I = 0) (I : Finset (Fin N)) : P I = 0 := by
  by_cases hI : IsStepRows N j p.2 I
  swap
  · exact hP I hI
  have key : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := fun I' hI' => by
    have hv := isValueAt_sum' (x := M.x) (z := b) Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I')
      (fun m => valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b)
      (fun m => isValueAt_mul (isValueAt_of_regAt hb (hg.2.1 _ _).2) (isValueAt_of_regAt hb (hg.2.1 _ _).1))
    rw [hF.2.2.1 p k hp I I' hI hI'] at hv
    by_cases e : I = I'
    · rw [if_pos e] at hv ⊢
      exact isValueAt_one hb hv
    · rw [if_neg e] at hv ⊢
      exact isValueAt_zero hb hv
  calc P I = ∑ I', (if I = I' then 1 else 0) * P I' := by simp
    _ = ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b) * P I' :=
        Finset.sum_congr rfl fun I' _ => by
          by_cases hI' : IsStepRows N j p.2 I'
          · rw [key I' hI']
          · rw [hP I' hI', mul_zero, mul_zero]
    _ = ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') b * P I' := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    _ = 0 := Finset.sum_eq_zero fun m _ => by rw [h0 m, mul_zero]

theorem trans_unit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    {b : (Σ k, baseIdx ι' M'.blk k) → ℂ} (hb : b ∈ mcPts (mCoordIdeal M'.x))
    {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk} (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal b)) (hg : M.GoodAt F (mCoordIdeal (b ∘ Cv.v))) (τ : Ψ) :
    IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  set A := ((F.T τ).map Cv.φ)⁻¹ * F'.T τ with hA
  set B := (F'.T τ)⁻¹ * (F.T τ).map Cv.φ with hB
  have hd : IsUnit ((F.T τ).map Cv.φ).det := by
    have e : ((F.T τ).map Cv.φ).det = Cv.φ (F.T τ).det := (RingHom.map_det Cv.φ (F.T τ)).symm
    rw [e]
    exact ((map_ne_zero Cv.φ).2 (hF.1 τ).2).isUnit
  have hd' : IsUnit (F'.T τ).det := (hF'.1 τ).2.isUnit
  have hAB : A * B = 1 := by
    rw [hA, hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd', Matrix.nonsing_inv_mul _ hd]
  have hreg := Cv.agree b hb F' F hF' hF hg' hg τ
  have hvA : ∀ a c, IsValueAt M'.x (A a c) b (valAt M'.x (A a c) b) := fun a c => isValueAt_of_regAt hb (hreg a c).1
  have hvB : ∀ a c, IsValueAt M'.x (B a c) b (valAt M'.x (B a c) b) := fun a c => isValueAt_of_regAt hb (hreg a c).2
  constructor
  · intro a c h
    have hblk : IsBlockDiag j A := (((hF.1 τ).1.map Cv.φ).inv hd).mul (hF'.1 τ).1
    have h1 := hvA a c
    rw [hblk a c h] at h1
    show valAt M'.x (A a c) b = 0
    rw [hblk a c h]
    exact isValueAt_zero hb h1
  · have hinv : Cv.trans F' F b τ * Matrix.of (fun a c => valAt M'.x (B a c) b) = 1 := by
      ext a c
      have hv := isValueAt_sum' (x := M'.x) (z := b) Finset.univ (fun e => A a e * B e c)
        (fun e => valAt M'.x (A a e) b * valAt M'.x (B e c) b) (fun e => isValueAt_mul (hvA a e) (hvB e c))
      rw [← Matrix.mul_apply, hAB] at hv
      rw [Matrix.mul_apply]
      by_cases e : a = c
      · subst e
        rw [Matrix.one_apply_eq] at hv ⊢
        exact isValueAt_one hb hv
      · rw [Matrix.one_apply_ne e] at hv ⊢
        exact isValueAt_zero hb hv
    intro h0
    have h1 := congrArg Matrix.det hinv
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1

theorem exists_point (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {b : (Σ k, baseIdx ι M.blk k) → ℂ} (hn : ∀ k, b ⟨k, F.c k⟩ = 1) {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) : ∃ z, basePart M.blk z = b ∧ M.IsFlagOf F z h := by
  let z : (Σ k, ι k) → ℂ := fun q => if hk : ∀ p, M.blk p ≠ some q.1 then b ⟨⟨q.1, hk⟩, q.2⟩ else
    ∑ I, valAt M.x (F.u q I) b * minorIJ (h (not_forall.1 hk).choose.1) I (stepCols N j (not_forall.1 hk).choose.2)
  have hb : basePart M.blk z = b := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    exact dif_pos hk
  refine ⟨z, hb, fun k => by rw [hb]; exact hn k, hh, fun p k hp => ⟨1, one_ne_zero, fun m => ?_⟩⟩
  have hk : ¬ ∀ p, M.blk p ≠ some k := fun e => e p hp
  have e : (not_forall.1 hk).choose = p := M.blk_inj _ _ k (not_not.1 (not_forall.1 hk).choose_spec) hp
  refine (dif_neg hk).trans ?_
  rw [hb, one_mul, e]

end Flags

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem step_prop {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk}
    (hF : M.IsFrame F) {β : (Σ k, baseIdx ι M.blk k) → ℂ} (hβ : β ∈ mcPts (mCoordIdeal M.x))
    (hgβ : M.GoodAt F (mCoordIdeal β)) {p : Ψ × Fin N} {k : K} (hk : M.blk p = some k)
    (hpr : IsProperStep N j p.2) {T h₁ h₂ : Matrix (Fin N) (Fin N) ℂ} (hT : IsBlockDiag j T ∧ T.det ≠ 0)
    (b₁ : IsBlockDiag j h₁) (b₂ : IsBlockDiag j h₂) {c e₁ e₂ : ℂ} (he₁ : e₁ ≠ 0)
    (hm : ∀ m : ι k, e₁ * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) β * minorIJ (T * h₁) I (stepCols N j p.2) =
      c * (e₂ * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) β * minorIJ (T * h₂) I (stepCols N j p.2))) (I : Finset (Fin N)) :
    minorIJ h₁ I (stepCols N j p.2) = (c * e₂ / e₁) * minorIJ h₂ I (stepCols N j p.2) := by
  refine minors_of_mul M.j_le p.2 hT.2 (fun I => ?_) I
  have := plucker_inj M hF hβ hgβ hk
    (fun I => e₁ * minorIJ (T * h₁) I (stepCols N j p.2) - c * e₂ * minorIJ (T * h₂) I (stepCols N j p.2))
    (fun I hI => by
      rw [minor_off_step M.j_le hpr (hT.1.mul b₁) hI, minor_off_step M.j_le hpr (hT.1.mul b₂) hI]
      ring)
    (fun m => by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have g1 : ∀ (a : ℂ) (A : Matrix (Fin N) (Fin N) ℂ),
          ∑ I, valAt M.x (F.u ⟨k, m⟩ I) β * (a * minorIJ A I (stepCols N j p.2)) =
            a * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) β * minorIJ A I (stepCols N j p.2) := fun a A => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [g1, g1, hm m]
      ring) I
  beta_reduce at this
  field_simp
  linear_combination this

theorem img_inj {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {d : ℕ}
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) {z₁ z₂ : (Σ k, ι' k) → ℂ}
    (h₁ : z₁ ∈ mcPts (mCoordIdeal y')) (h₂ : z₂ ∈ mcPts (mCoordIdeal y'))
    (i₁ : CovMap.IsImg Cv z₁ w) (i₂ : CovMap.IsImg Cv z₂ w)
    (hb : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z₂)) : SameOrbit z₁ z₂ := by
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z₁ h₁)
  obtain ⟨a₁, o₁, n₁⟩ := exists_normal_base M'.blk F'.c z₁ fun k => chart_ne (hg'.1 k)
  obtain ⟨a₂, o₂, n₂⟩ := exists_normal_base M'.blk F'.c z₂ fun k =>
    chart_ne (by rw [← mCoordIdeal_eq_of_orbit hb]; exact hg'.1 k)
  have ob₁ := basePart_orbit M'.blk o₁
  have ob₂ := basePart_orbit M'.blk o₂
  have eb : basePart M'.blk a₁ = basePart M'.blk a₂ := eq_of_orbit_normal (c := F'.c)
    (Cj.sameOrbit_trans ob₁ (Cj.sameOrbit_trans hb (Cj.sameOrbit_symm ob₂))) n₁ n₂
  have hbm : basePart M'.blk a₁ ∈ mcPts (mCoordIdeal M'.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) ob₁ (P'.1 z₁ h₁)
  have hgb : M'.GoodAt F' (mCoordIdeal (basePart M'.blk a₁)) := by rw [mCoordIdeal_eq_of_orbit ob₁]; exact hg'
  have ha₁ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₁ h₁
  have ha₂ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₂ h₂
  have hbw : SameOrbit (basePart M'.blk a₁ ∘ Cv.v) (basePart M.blk w) := Cj.sameOrbit_trans
    (comp_orbit Cv.block ob₁) (Cj.sameOrbit_symm (GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z₁ h₁ w i₁))
  have hbv := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) hbw (P.1 w hw)
  obtain ⟨F, hF, hg⟩ := P.2.1 _ hbv
  obtain ⟨g₁, fl₁⟩ := (P'.2.2 F' hF' a₁ hbm hgb n₁).1 ha₁
  obtain ⟨g₂, fl₂⟩ := (P'.2.2 F' hF' a₂ (by rw [← eb]; exact hbm) (by rw [← eb]; exact hgb) n₂).1 ha₂
  obtain ⟨z₀, s₁, t₁, f₁⟩ := i₁ a₁ o₁ F' F hF' hF hgb hg g₁ fl₁
  obtain ⟨z₀', s₂, t₂, f₂⟩ := i₂ a₂ o₂ F' F hF' hF (by rw [← eb]; exact hgb) (by rw [← eb]; exact hg) g₂ fl₂
  rw [← eb] at t₂ f₂
  have eβ : basePart M.blk z₀ = basePart M.blk z₀' :=
    eq_of_orbit_normal (c := F.c) (Cj.sameOrbit_trans t₁ (Cj.sameOrbit_symm t₂)) f₁.1 f₂.1
  have hβ : basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) t₁ hbv
  have hgβ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [mCoordIdeal_eq_of_orbit t₁]; exact hg
  obtain ⟨c, hc, ez⟩ := Cj.sameOrbit_trans s₁ (Cj.sameOrbit_symm s₂)
  have hT := trans_unit Cv hbm hF' hF hgb hg
  have hfin : SameOrbit a₁ a₂ := sameOrbit_of_blocks M'.blk eb fun p k' hp' => by
    have hpr : IsProperStep N j p.2 := by
      by_contra hn
      rw [(M'.blk_none p).2 hn] at hp'
      exact absurd hp' (by simp)
    obtain ⟨k, hk⟩ : ∃ k, M.blk p = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none p).1 e hpr
    obtain ⟨e₁, he₁, v₁⟩ := f₁.2.2 p k hk
    obtain ⟨e₂, he₂, v₂⟩ := f₂.2.2 p k hk
    have key := step_prop (M' := M') (c := c k) (e₁ := e₁) (e₂ := e₂) hF hβ hgβ hk hpr (hT p.1) (fl₁.2.1 p.1).1
      (fl₂.2.1 p.1).1 he₁ (fun m => by
        have x3 : z₀ ⟨k, m⟩ = c k * z₀' ⟨k, m⟩ := congrFun ez ⟨k, m⟩
        have x1 := v₁ m
        have x2 := v₂ m
        rw [← eβ] at x2
        rw [x1, x2] at x3
        exact x3)
    obtain ⟨a, ha, w₁⟩ := fl₁.2.2 p k' hp'
    obtain ⟨a', ha', w₂⟩ := fl₂.2.2 p k' hp'
    refine ⟨a * (c k * e₂ / e₁) / a', div_ne_zero (mul_ne_zero ha (div_ne_zero (mul_ne_zero (hc k) he₂) he₁)) ha',
      fun m => ?_⟩
    rw [w₁ m, w₂ m, ← eb]
    simp only [key]
    have g1 : ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) *
        ((c k * e₂ / e₁) * minorIJ (g₂ p.1) I (stepCols N j p.2)) =
        (c k * e₂ / e₁) * ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) * minorIJ (g₂ p.1) I (stepCols N j p.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [g1]
    field_simp
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm o₁) (Cj.sameOrbit_trans hfin o₂)

theorem img_surj {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) {d : ℕ}
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) {b' : (Σ k, baseIdx ι' M'.blk k) → ℂ}
    (hb' : b' ∈ mcPts (mCoordIdeal M'.x)) (ho : SameOrbit (fun p => b' (Cv.v p)) (basePart M.blk w)) :
    ∃ z, z ∈ mcPts (mCoordIdeal y') ∧ SameOrbit (basePart M'.blk z) b' ∧ CovMap.IsImg Cv z w := by
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hg'0⟩ := P'.2.1 b' hb'
  obtain ⟨b, ob, nb⟩ := exists_normal F'.c b' fun k => chart_ne (hg'0.1 k)
  have hbm := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) ob hb'
  have hg' : M'.GoodAt F' (mCoordIdeal b) := by rw [mCoordIdeal_eq_of_orbit ob]; exact hg'0
  have ov : SameOrbit (b ∘ Cv.v) (basePart M.blk w) := Cj.sameOrbit_trans (comp_orbit Cv.block ob) ho
  have hbv := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) ov (P.1 w hw)
  obtain ⟨F, hF, hg⟩ := P.2.1 _ hbv
  have hgw : M.GoodAt F (mCoordIdeal (basePart M.blk w)) := by rw [← mCoordIdeal_eq_of_orbit ov]; exact hg
  obtain ⟨w₁, ow, nw⟩ := exists_normal_base M.blk F.c w fun k => chart_ne (hgw.1 k)
  have hw₁ := mem_mcPts_of_sameOrbit hy.2.1.2.1 ow hw
  have obw := basePart_orbit M.blk ow
  have hgw₁ : M.GoodAt F (mCoordIdeal (basePart M.blk w₁)) := by rw [mCoordIdeal_eq_of_orbit obw]; exact hgw
  obtain ⟨g, fl⟩ := (P.2.2 F hF w₁ (P.1 w₁ hw₁) hgw₁ nw).1 hw₁
  have hT := trans_unit Cv hbm hF' hF hg' hg
  have hTg : (fun τ => Cv.trans F' F b τ * ((Cv.trans F' F b τ)⁻¹ * g τ)) = g := funext fun τ =>
    Matrix.mul_nonsing_inv_cancel_left _ _ (hT τ).2.isUnit
  have hh : ∀ τ, IsBlockDiag j ((Cv.trans F' F b τ)⁻¹ * g τ) ∧ ((Cv.trans F' F b τ)⁻¹ * g τ).det ≠ 0 := fun τ =>
    ⟨((hT τ).1.inv (hT τ).2.isUnit).mul (fl.2.1 τ).1, by
      have hi : IsUnit (Cv.trans F' F b τ)⁻¹.det := by
        rw [Matrix.det_nonsing_inv]
        exact ((hT τ).2.isUnit).ringInverse
      rw [Matrix.det_mul]
      exact mul_ne_zero hi.ne_zero (fl.2.1 τ).2⟩
  obtain ⟨z, ez, flz⟩ := exists_point M' nb hh
  have hz : z ∈ mcPts (mCoordIdeal y') := (P'.2.2 F' hF' z (by rw [ez]; exact hbm) (by rw [ez]; exact hg')
    (fun k => by rw [ez]; exact nb k)).2 ⟨_, flz⟩
  obtain ⟨V, f, -, hzV, -, hf⟩ := GlobalTheory.T.flag_cover_arithmetic_first K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z hz
  obtain ⟨-, hi⟩ := hf z ⟨hzV, hz⟩
  obtain ⟨z₀, s, t, f₀⟩ := hi z (Cj.sameOrbit_refl z) F' F hF' hF (by rw [ez]; exact hg') (by rw [ez]; exact hg) _ flz
  rw [ez] at t f₀
  rw [hTg] at f₀
  have eβ : basePart M.blk z₀ = basePart M.blk w₁ :=
    eq_of_orbit_normal (c := F.c) (Cj.sameOrbit_trans t (Cj.sameOrbit_trans ov (Cj.sameOrbit_symm obw))) f₀.1 nw
  have o₀ : SameOrbit z₀ w₁ := sameOrbit_of_blocks M.blk eβ fun p k hp => by
    obtain ⟨a, ha, va⟩ := f₀.2.2 p k hp
    obtain ⟨a', ha', va'⟩ := fl.2.2 p k hp
    refine ⟨a / a', div_ne_zero ha ha', fun m => ?_⟩
    rw [va m, va' m, eβ]
    field_simp
  refine ⟨z, hz, by rw [ez]; exact ob, hi.orbit (Cj.sameOrbit_refl z) ?_⟩
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm ow) (Cj.sameOrbit_trans (Cj.sameOrbit_symm o₀) s)

end Main

theorem fibre_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ w ∈ mcPts (mCoordIdeal y), {O | ∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ CovMap.IsImg Cv z w}.ncard = (GroundTheory.Heights₂.Heights.Inter.ptsOverPt (mCoordIdeal M'.x) Cv.v (basePart M.blk w)).ncard := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d hy hy' w hw
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  have hS : ∀ O : Set ((Σ k, ι' k) → ℂ), (∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ CovMap.IsImg Cv z w) →
      ∃ z, z ∈ mcPts (mCoordIdeal y') ∧ O = {z'' | SameOrbit z'' z} ∧ CovMap.IsImg Cv z w :=
    fun O ⟨z, a, b, c⟩ => ⟨z, a, b, c⟩
  choose! g hg using hS
  refine Set.ncard_congr (fun O _ => {b | SameOrbit b (basePart M'.blk (g O))}) ?_ ?_ ?_
  · intro O hO
    obtain ⟨hz, -, hi⟩ := hg O hO
    exact ⟨_, P'.1 _ hz, rfl, Cj.sameOrbit_symm (GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ hz w hi)⟩
  · intro O O' hO hO' e
    obtain ⟨hz, e₁, hi⟩ := hg O hO
    obtain ⟨hz', e₂, hi'⟩ := hg O' hO'
    exact e₁.trans ((orbit_eq_iff.2 (img_inj Cv hy hy' hw hz hz' hi hi' (orbit_eq_iff.1 e))).trans e₂.symm)
  · rintro O' ⟨b', hb', rfl, ho⟩
    obtain ⟨z, hz, ob, hi⟩ := img_surj Cv hy hy' hw hb' ho
    have hO : ∃ z₀ ∈ mcPts (mCoordIdeal y'), {z'' | SameOrbit z'' z} = {z'' | SameOrbit z'' z₀} ∧ CovMap.IsImg Cv z₀ w :=
      ⟨z, hz, rfl, hi⟩
    refine ⟨_, hO, ?_⟩
    obtain ⟨-, e, -⟩ := hg _ hO
    exact orbit_eq_iff.2 (Cj.sameOrbit_trans (basePart_orbit _ (Cj.sameOrbit_symm (orbit_eq_iff.1 e))) ob)

end GlobalTheory.CompanionTheory.Ar.PB.FibreCount
