import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods

open GroundTheory.Heights₂.Heights.Regular

theorem star_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    star w ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simpa using hw.1 i
  · simpa using hw.2 k hk

theorem expCover_star {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : expCover a (star w) = star (expCover a w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · exact Complex.exp_conj _
  · rfl

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w; simp [logCover]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
    · simp [hk]

theorem star_mem_ball {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro i
  simpa using hz i

theorem differentiableOn_conj {n g : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hst : ∀ w ∈ S, star w ∈ S)
    {f : (Fin n → ℂ) → Fin g → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun w => star (f (star w))) S := by
  intro w hw
  have h1 : DifferentiableAt ℂ f (star w) := hf.differentiableAt (hS.mem_nhds (hst w hw))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

theorem dot_map_conj {g : ℕ} (x y : Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ) :
    x ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ y = star (star x ⬝ᵥ M *ᵥ star y) := by
  simp [dotProduct, Matrix.mulVec, star_sum]

theorem isHermitian_map_conj {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) :
    (M.map (starRingEnd ℂ)).IsHermitian := by
  ext i j
  have := hM.apply i j
  simp [Matrix.conjTranspose_apply, ← this]

theorem star_single {n : ℕ} (c : Fin n) :
    star (Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) = -Pi.single c (2 * Real.pi * Complex.I) := by
  funext k
  by_cases hk : k = c
  · subst hk
    simp
  · simp [hk]

theorem sub_single_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w - Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

def conj {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (hT : ∀ i, Function.Bijective (L.T i)) : Flat.LogPeriods n a g Λ where
  a_le := L.a_le
  free := L.free
  fin := L.fin
  rank := L.rank
  E := -L.E
  alt x := by simp [L.alt x]
  unimod := by
    constructor
    · intro x y hxy
      exact L.unimod.1 (neg_injective hxy)
    · intro f
      obtain ⟨x, hx⟩ := L.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  P w := AddMonoidHom.mk' (fun x => star (L.P (star w) x)) (fun x y => by simp)
  hol x := differentiableOn_conj (isOpen_logCover L.a_le) (fun w hw => star_mem_logCover L.a_le hw) (L.hol x)
  H z := (L.H (star z)).map (starRingEnd ℂ)
  herm w hw := by
    rw [← expCover_star]
    exact isHermitian_map_conj (L.herm _ (star_mem_logCover L.a_le hw))
  pos w hw z hz := by
    rw [← expCover_star, dot_map_conj]
    have h := L.pos _ (star_mem_logCover L.a_le hw) (star z) (by simpa using hz)
    simpa using h
  im w hw x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, dot_map_conj]
    have h := L.im _ (star_mem_logCover L.a_le hw) x y
    simp [h]
  T i := ((LinearEquiv.ofBijective (L.T i) (hT i)).symm : Λ ≃ₗ[ℤ] Λ).toLinearMap
  mono i w hw x := by
    set e : Fin _ → ℂ := Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I) with he
    have hw₁ : star w - e ∈ logCover L.a_le :=
      sub_single_mem_logCover L.a_le (star_mem_logCover L.a_le hw) i
    have hm := L.mono i _ hw₁ ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x)
    have hTT : L.T i ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x) = x :=
      (LinearEquiv.ofBijective (L.T i) (hT i)).apply_symm_apply x
    rw [hTT, ← he, sub_add_cancel] at hm
    have hs : star (w + e) = star w - e := by
      rw [star_add, he, star_single, sub_eq_add_neg]
    simp only [AddMonoidHom.mk'_apply, LinearEquiv.coe_coe]
    rw [hs, hm]
  W := L.W
  coiso x hx := L.coiso x fun y hy => by simpa using hx y hy
  s x z := star (L.s x (star z))
  s_hol x := differentiableOn_conj Metric.isOpen_ball (fun _ hz => star_mem_ball hz) (L.s_hol x)
  s_eq x w hw := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, L.s_eq x _ (star_mem_logCover L.a_le hw)]
  span := by
    rw [eq_top_iff]
    intro v _
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun x => L.s x 0),
        star y ∈ Submodule.span ℂ (Set.range fun x => star (L.s x (star (0 : Fin _ → ℂ)))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy
    have := key (star v) (by rw [L.span]; trivial)
    simpa using this

theorem exists_conj_periodGram : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) →
    ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1,
      HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u =
        (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  intro n a g r Λ _ L U hT
  refine ⟨conj L hT, fun u _ => ?_⟩
  ext i j
  simp only [HodgeMetric.periodGram, Matrix.of_apply, Matrix.map_apply]
  change _ * (_ ⬝ᵥ ((L.H (star u)).map (starRingEnd ℂ)) *ᵥ _) = _
  rw [dot_map_conj, map_mul, Complex.conj_ofReal]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods
