import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveOrbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  rcases Finset.mem_singleton.mp hm with rfl
  simp

theorem mem_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  show mConeMap y f = 0
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_map_eq_aeval (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_comp (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    eval (fun p => σ (y p)) (map (Int.castRingHom ℂ) f) = σ (aeval y f) := by
  have : (eval (fun p => σ (y p))).comp (map (Int.castRingHom ℂ)) = σ.comp (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp)
  exact congrArg (fun φ => φ f) this

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem mem_mcPts (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    (fun p => σ (y p)) ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => ⟨c k, (map_ne_zero σ).mpr (hc k)⟩, fun f hf => by rw [eval_comp, aeval_eq_zero_of_mem y hf, map_zero]⟩

theorem eval_smul (w : (Σ k, ι k) → ℂ) (l : K → ℂ) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    eval (fun p => l p.1 * w p) (map (Int.castRingHom ℂ) f) = (∏ k, l k ^ d k) * eval w (map (Int.castRingHom ℂ) f) := by
  have hc : (MvPolynomial.eval l).comp (mConeMap w).toRingHom = (aeval (fun p => l p.1 * w p)).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap, mul_comm])
  have h1 := congrArg (MvPolynomial.eval l) (ConeTrdeg.mConeMap_of_isMultiHomog w hf)
  have h2 := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [eval_map_eq_aeval, eval_map_eq_aeval, ← h2, h1, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem exists_sameOrbit {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (hB : Birational y)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : ∃ σ : Ω →+* ℂ, SameOrbit z (fun p => σ (y p)) := by
  classical
  set P := mCoordIdeal y
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → aeval y v ≠ 0 → φ v ≠ 0 := fun v a hv hv0 =>
    eval_ne_zero_of_dimOne arithVarZero hP
      (A := HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun k => (a k : ℤ)))
      ⟨a, fun _ => rfl, hv, fun hm => hv0 (aeval_eq_zero_of_mem y hm)⟩ hz
  choose d g h hg hh hh0 hgh using hB
  let σf : Ω → ℂ := fun s => φ (g s) / φ (h s)
  have hhz : ∀ s, φ (h s) ≠ 0 := fun s => hne _ _ (hh s) (hh0 s)

  have rep : ∀ (s : Ω) (e : K → ℕ) (G H : MRing ι), IsMultiHomog G e → IsMultiHomog H e → aeval y H ≠ 0 →
      aeval y G = s * aeval y H → σf s * φ H = φ G := by
    intro s e G H hG hH hH0 hGs
    have hmem : G * h s - H * g s ∈ P :=
      mem_of_aeval_eq_zero y (isMultiHomog_sub (isMultiHomog_mul hG (hh s)) (isMultiHomog_mul hH (hg s)))
        (by rw [map_sub, map_mul, map_mul, hGs, hgh s]; ring)
    have h1 : φ G * φ (h s) = φ H * φ (g s) := by
      have : φ (G * h s - H * g s) = 0 := hz.2 _ hmem
      rw [map_sub, map_mul, map_mul] at this
      exact sub_eq_zero.mp this
    simp only [σf]
    field_simp [hhz s]
    linear_combination h1.symm
  have hsub : ∀ s t, aeval y (h s * h t) ≠ 0 := fun s t => by rw [map_mul]; exact mul_ne_zero (hh0 s) (hh0 t)
  let σ : Ω →+* ℂ :=
    { toFun := σf
      map_one' := by
        have := rep 1 0 1 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_mul' := fun s t => by
        have := rep (s * t) (d s + d t) (g s * g t) (h s * h t) (isMultiHomog_mul (hg s) (hg t)) (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this)
      map_zero' := by
        have := rep 0 0 0 1 (fun m hm => by simp at hm) isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_add' := fun s t => by
        have := rep (s + t) (d s + d t) (g s * h t + h s * g t) (h s * h t) (isMultiHomog_add (isMultiHomog_mul (hg s) (hh t)) (isMultiHomog_mul (hh s) (hg t)))
          (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_add, map_mul, map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_add, map_mul, map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this) }
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hzj : ∀ k, z ⟨k, j k⟩ ≠ 0 := fun k => by
    simpa [φ] using hne _ _ (regularityEmbedding_holds.isMultiHomog_X_single k (j k)) (by simpa using hj k)
  refine ⟨σ, fun k => z ⟨k, j k⟩ / σ (y ⟨k, j k⟩), fun k => div_ne_zero (hzj k) ((map_ne_zero σ).mpr (hj k)), ?_⟩
  funext p
  have hr := rep (y p / y ⟨p.1, j p.1⟩) _ _ _ (regularityEmbedding_holds.isMultiHomog_X_single p.1 p.2)
    (regularityEmbedding_holds.isMultiHomog_X_single p.1 (j p.1)) (by simpa using hj p.1) (by simp [div_mul_cancel₀ _ (hj p.1)])
  have hσ : σf (y p / y ⟨p.1, j p.1⟩) = σ (y p) / σ (y ⟨p.1, j p.1⟩) := map_div₀ σ _ _
  rw [hσ] at hr
  simp only [φ, RingHom.comp_apply, map_X, eval_X] at hr
  have hr' : σ (y p) / σ (y ⟨p.1, j p.1⟩) * z ⟨p.1, j p.1⟩ = z p := hr
  show z p = z ⟨p.1, j p.1⟩ / σ (y ⟨p.1, j p.1⟩) * σ (y p)
  rw [← hr']
  ring

end CurveOrbit

end

end GroundTheory.Heights₂.Heights.Targets
