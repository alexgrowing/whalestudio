import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpMulThetaCharAutomorphy
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix Topology

namespace GlobalTheory.ThetaSquareIntegrable

theorem eq_zero_of_entire_mul {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : ∃ z, θ z ≠ 0)
    {z : Fin g → ℂ} (hD : ContinuousAt D z) (h : ∀ᶠ x in 𝓝 z, θ x * D x = 0) : D z = 0 := by
  obtain ⟨z₀, hz₀⟩ := h0
  let L : ℂ → (Fin g → ℂ) := fun t => z + t • (z₀ - z)
  have hL : Differentiable ℂ L := by fun_prop
  have hL0 : L 0 = z := by simp [L]
  have hf : Differentiable ℂ (θ ∘ L) := hθ.comp hL
  have han : AnalyticOnNhd ℂ (θ ∘ L) Set.univ := fun t _ => hf.analyticAt t
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), (θ ∘ L) t ≠ 0 := by
    rcases (han 0 trivial).eventually_eq_zero_or_eventually_ne_zero with e | e
    · exfalso
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) e
        (Set.mem_univ 1)
      apply hz₀
      simpa [L] using this
    · exact e
  have ht : Filter.Tendsto L (𝓝 0) (𝓝 z) := hL0 ▸ hL.continuous.tendsto 0
  have ht' : Filter.Tendsto L (𝓝[≠] 0) (𝓝 z) := ht.mono_left nhdsWithin_le_nhds
  have e1 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), D (L t) = 0 := by
    filter_upwards [hne, ht'.eventually h] with t h1 h2
    exact (mul_eq_zero.1 h2).resolve_left h1
  have e2 : Filter.Tendsto (fun t => D (L t)) (𝓝[≠] 0) (𝓝 (D z)) := hD.tendsto.comp ht'
  exact tendsto_nhds_unique e2 (tendsto_const_nhds.congr' (e1.mono fun t ht => ht.symm))

theorem mulVec_period {g : ℕ} {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (per : ∀ k, h *ᵥ (P (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h *ᵥ (P (bas (Pi.single (.inr k) 1))) = τ *ᵥ (Pi.single k 1)) (u : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas u) = (fun i => (u (.inl i) : ℂ)) + τ *ᵥ (fun i => (u (.inr i) : ℂ)) := by
  let A : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ) :=
    (Matrix.mulVecLin h).toAddMonoidHom.comp (P.comp bas.toLinearMap.toAddMonoidHom)
  let B : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk'
    (fun u => (fun i => (u (.inl i) : ℂ)) + τ *ᵥ (fun i => (u (.inr i) : ℂ))) (by
      intro a b
      have : (fun i => ((a + b) (.inr i) : ℂ)) = (fun i => (a (.inr i) : ℂ)) + (fun i => (b (.inr i) : ℂ)) := by
        funext i; simp
      rw [this, Matrix.mulVec_add]
      funext i; simp; ring)
  have : A.toIntLinearMap = B.toIntLinearMap := by
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    rcases j with k | k
    · have := (per k).1
      have e : (fun i => ((Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ) (.inr i) : ℂ)) = 0 := by
        funext i; simp
      change h *ᵥ (P (bas (Pi.single (.inl k) 1))) = (fun i => ((Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ) (.inl i) : ℂ)) + τ *ᵥ (fun i => ((Pi.single (Sum.inl k) 1 : Fin g ⊕ Fin g → ℤ) (.inr i) : ℂ))
      rw [this, e]
      funext i; by_cases hi : i = k <;> simp [Pi.single_apply, hi]
    · have := (per k).2
      have e : (fun i => ((Pi.single (Sum.inr k) 1 : Fin g ⊕ Fin g → ℤ) (.inr i) : ℂ)) = Pi.single k 1 := by
        funext i; by_cases hi : i = k <;> simp [Pi.single_apply, hi]
      change h *ᵥ (P (bas (Pi.single (.inr k) 1))) = (fun i => ((Pi.single (Sum.inr k) 1 : Fin g ⊕ Fin g → ℤ) (.inl i) : ℂ)) + τ *ᵥ (fun i => ((Pi.single (Sum.inr k) 1 : Fin g ⊕ Fin g → ℤ) (.inr i) : ℂ))
      rw [this, e]
      funext i; simp
  exact LinearMap.congr_fun this u

theorem im_form {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (m n m' n' : Fin g → ℤ) :
    (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ⬝ᵥ
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ
        star ((fun i => (m' i : ℂ)) + τ *ᵥ (fun i => (n' i : ℂ)))).im =
      -∑ i, ((m i : ℝ) * n' i - n i * m' i) := by
  set Y := τ.map Complex.im with hY
  set X := τ.map Complex.re with hX
  have hXs : X.IsSymm := hs.map _
  have hYs : Y.IsSymm := hs.map _
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have gen : ∀ u v : Fin g → ℂ, (u ⬝ᵥ (Y⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star v).im =
      (fun i => (u i).im) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).re) - (fun i => (u i).re) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (v i).im) := by
    intro u v
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.im_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp
    ring
  have him : ∀ m n : Fin g → ℤ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).im) =
      Y *ᵥ (fun i => (n i : ℝ)) := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hY]
  have hre : ∀ m n : Fin g → ℤ, (fun i => (((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) i).re) =
      (fun i => (m i : ℝ)) + X *ᵥ (fun i => (n i : ℝ)) := by
    intro m n; funext i; simp [Matrix.mulVec, dotProduct, hX]
  have sd : ∀ {M : Matrix (Fin g) (Fin g) ℝ}, M.IsSymm → ∀ u v : Fin g → ℝ, u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
    intro M hM u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq, dotProduct_comm]
  rw [gen, him, him, hre, hre, sd hYs.inv (Y *ᵥ _), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec, Matrix.one_mulVec, add_dotProduct, add_dotProduct,
    dotProduct_comm (X *ᵥ _), dotProduct_comm (X *ᵥ _), sd hXs]
  simp only [dotProduct, Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun i _ => mul_comm (n i : ℝ) (m' i : ℝ)]
  ring

theorem posDef_form {g : ℕ} {τ h : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef) (hh : IsUnit h.det) :
    (hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ)).IsHermitian ∧
    ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (hermForm (hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ)) z z).re := by
  set Y := τ.map Complex.im with hY
  have hi : (Y⁻¹).PosDef := hp.inv
  refine ⟨?_, fun z hz => ?_⟩
  · have h1 : ((Y⁻¹).map (fun x : ℝ => (x : ℂ))).IsHermitian := by
      ext i j
      have := hi.isHermitian.apply i j
      simp only [star_trivial] at this
      simp [this]
    have h2 : h.map (starRingEnd ℂ) = (hᵀ)ᴴ := by ext i j; simp
    rw [h2]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ h1
  · rw [GlobalTheory.ThetaAH.hermForm_pullback]
    have hw : h *ᵥ z ≠ 0 := fun e => hz (Matrix.eq_zero_of_mulVec_eq_zero hh.ne_zero e)
    generalize h *ᵥ z = u at hw
    have gen : (u ⬝ᵥ (Y⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ star u).re =
        (fun i => (u i).re) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (u i).re) + (fun i => (u i).im) ⬝ᵥ Y⁻¹ *ᵥ (fun i => (u i).im) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp
    rw [gen]
    have p0 : ∀ v : Fin g → ℝ, 0 ≤ v ⬝ᵥ Y⁻¹ *ᵥ v := fun v => by simpa using hi.posSemidef.dotProduct_mulVec_nonneg v
    have p1 : ∀ v : Fin g → ℝ, v ≠ 0 → 0 < v ⬝ᵥ Y⁻¹ *ᵥ v := fun v hv => by simpa using hi.dotProduct_mulVec_pos hv
    by_cases hr : (fun i => (u i).re) = 0
    · have : (fun i => (u i).im) ≠ 0 := fun e => hw (funext fun i => Complex.ext (congrFun hr i) (congrFun e i))
      exact add_pos_of_nonneg_of_pos (p0 _) (p1 _ this)
    · exact add_pos_of_pos_of_nonneg (p1 _ hr) (p0 _)

theorem theta_l2_of_analytic_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (y : FrPt Xo c (CAt σ)), Ha.T < w.im → y.x = Fu.u Ha.i (Ha.Pw w) → AnGen Fu Ha.i (Ha.Pw w) y (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) Θ.κ → IsThetaL2NormSquared Fu Ha.i (Ha.Pw w) y (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ g * ((Θ.τ w).map Complex.im).det))⁻¹) := by
  intro E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha th Θ w y hw hy hG
  obtain ⟨fr, ⟨f1, f2, f3, f4, s, f5⟩, hgen⟩ := hG
  obtain ⟨hs, hp⟩ := Θ.pos w hw
  have hper := Ha.period w hw
  have hm := mulVec_period (Ha.Pw w) Θ.bas Θ.h (Θ.τ w) (Θ.per w)
  have hh : IsUnit Θ.h.det := by
    have : Θ.h * (Matrix.of fun i k => Ha.Pw w (Θ.bas (Pi.single (.inl k) 1)) i) = 1 := by
      ext i k
      have := congrFun (Θ.per w k).1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply] using this
    exact Matrix.isUnit_det_of_right_inverse this
  have hΛ : ∀ lam, lam ∈ (Ha.Pw w).range ↔ ∃ m n : Fin g → ℤ,
      Θ.h *ᵥ lam = (fun i => (m i : ℂ)) + Θ.τ w *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := Θ.bas.surjective v
      exact ⟨_, _, hm u⟩
    · rintro ⟨m, n, e⟩
      refine ⟨Θ.bas (Sum.elim m n), ?_⟩
      have := hm (Sum.elim m n)
      simp only [Sum.elim_inl, Sum.elim_inr] at this
      rw [← e, ← sub_eq_zero, ← Matrix.mulVec_sub] at this
      exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hh.ne_zero this)
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g (Θ.τ w) Θ.h Θ.c₁ Θ.c₂
    _ hs hp hh Θ.half₁ Θ.half₂ hΛ
  obtain ⟨Hm, hHm⟩ : ∃ Hm, Hm = Θ.hᵀ * (((Θ.τ w).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
    Θ.h.map (starRingEnd ℂ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, q = fun z => Real.pi / 2 * ((Θ.h *ᵥ z) ⬝ᵥ
    ((((Θ.τ w).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (Θ.h *ᵥ z))) := ⟨_, rfl⟩
  have hq0 : q 0 = 0 := by simp [hq]
  have hqd : Differentiable ℂ q := by
    rw [hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨an1, an2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g (Θ.τ w) Θ.h Hm Θ.c₁ Θ.c₂ q hs hp Θ.half₁ Θ.half₂
    hHm (fun z => by rw [hq])
  obtain ⟨θd, z₀, θne⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g Θ.c₁ Θ.c₂ Θ.half₁ Θ.half₂).1 _ hs hp
  obtain ⟨θ, hθ⟩ : ∃ θ : (Fin g → ℂ) → ℂ, θ = fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h *ᵥ z) := ⟨_, rfl⟩
  have hθd : Differentiable ℂ θ := by
    rw [hθ]
    refine θd.comp (f := fun z => Θ.h *ᵥ z) ?_
    exact (Matrix.mulVecLin Θ.h).toContinuousLinearMap.differentiable
  have hθ0 : ∃ z, θ z ≠ 0 := ⟨Θ.h⁻¹ *ᵥ z₀, by
    rw [hθ]
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec] using θne⟩
  have hθz : ∀ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h *ᵥ z) = θ z := fun z => by rw [hθ]
  simp only [hθz] at an2 hint f5 hgen
  have hχ : ∀ lam : Fin g → ℂ, ∃ x : ℂ, ‖x‖ = 1 ∧ (lam ∈ (Ha.Pw w).range → ∀ z,
      Complex.exp (q (z + lam)) * θ (z + lam) = x * Complex.exp (Real.pi * hermForm Hm z lam +
        Real.pi / 2 * hermForm Hm lam lam) * (Complex.exp (q z) * θ z)) := by
    intro lam
    by_cases hl : lam ∈ (Ha.Pw w).range
    · obtain ⟨m, n, e⟩ := (hΛ lam).1 hl
      obtain ⟨x, h1, h2⟩ := an2 lam m n e
      exact ⟨x, h1, fun _ => h2⟩
    · exact ⟨1, norm_one, fun h => (hl h).elim⟩
  choose χl hχ1 hχ2 using hχ
  have hopen : ∀ U, IsOpen {z | ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) z).left ⁻¹ᵁ U} := by
    intro U
    have := ((Fu.hol Ha.i 0 Set.univ (fun _ => Ha.Pw w) isOpen_univ
      ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 U 0).1
    have h2 := this.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    simpa using h2
  have hex : ∀ v z, Fu.ex Ha.i (Ha.Pw w) (z + Ha.Pw w v) = Fu.ex Ha.i (Ha.Pw w) z := by
    intro v z
    open scoped MonObj in rw [Fu.ex_add _ _ hper, (Fu.ex_ker _ _ hper _).2 ⟨v, rfl⟩, mul_one]
  have hpf : ∀ v j z, ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      θ z * fr j z = θ (z + Ha.Pw w v) * fr j (z + Ha.Pw w v) := by
    intro v j z hz
    have hc : (Fu.ex Ha.i (Ha.Pw w) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ Fu.u Ha.i (Ha.Pw w) := by
      simpa using Over.w (Fu.ex Ha.i (Ha.Pw w) z)
    rw [← f5 j z (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hz,
      ← f5 j (z + Ha.Pw w v) (pullback.lift _ _ hc) (by rw [hex]; exact pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _) (by rw [hex]; exact hz)]
  have hpd := posDef_form hp hh
  rw [← hHm] at hpd
  refine ⟨Hm, χl, fun j z => fr j z * Complex.exp (-q z), fun z => Θ.κ * Complex.exp (q z) * θ z, Fd,
    hpd.1, hpd.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hFd, ?_⟩
  · intro u v
    obtain ⟨u, rfl⟩ := Θ.bas.surjective u
    obtain ⟨v, rfl⟩ := Θ.bas.surjective v
    rw [hHm, GlobalTheory.ThetaAH.hermForm_pullback, hm, hm, im_form hs hp, Θ.sympl, omegaStd]
    push_cast
    rfl
  · exact fun j => (f1 j).mul (hqd.neg.cexp.differentiableOn)
  · exact fun j z hz => mul_ne_zero (f2 j z hz) (Complex.exp_ne_zero _)
  · intro j j' z hz
    beta_reduce
    rw [f3 j j' z hz, mul_assoc]
  · intro j hj
    beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, hy]
    exact f4 j hj
  · intro v j z
    refine ⟨hχ1 _, fun hz => ?_⟩
    beta_reduce
    rw [← sub_eq_zero]
    have hn := (hopen _).mem_nhds hz
    refine eq_zero_of_entire_mul (D := fun z => fr j z * Complex.exp (-q z) - χl (Ha.Pw w v) *
      Complex.exp (Real.pi * hermForm Hm z (Ha.Pw w v) + Real.pi / 2 * hermForm Hm (Ha.Pw w v) (Ha.Pw w v)) *
      (fr j (z + Ha.Pw w v) * Complex.exp (-q (z + Ha.Pw w v)))) hθd hθ0 ?_ ?_
    · have c1 : ContinuousAt (fr j) z := (f1 j).continuousOn.continuousAt hn
      have c2 : ContinuousAt (fun z => fr j (z + Ha.Pw w v)) z := by
        refine ContinuousAt.comp (f := fun z => z + Ha.Pw w v) ?_ (by fun_prop)
        refine (f1 j).continuousOn.continuousAt ((hopen _).mem_nhds ?_)
        change ⊤ ≤ (Fu.ex Ha.i (Ha.Pw w) (z + Ha.Pw w v)).left ⁻¹ᵁ _
        rw [hex]; exact hz
      have c3 := hqd.continuous
      have c4 : Continuous fun z => hermForm Hm z (Ha.Pw w v) := by
        simp only [hermForm, dotProduct]; fun_prop
      refine (c1.mul (by fun_prop)).sub ((continuousAt_const.mul ?_).mul (c2.mul (by fun_prop)))
      exact ((continuous_const.mul c4).add continuous_const).cexp.continuousAt
    · filter_upwards [hn] with x hx
      have e1 := hpf v j x hx
      have e2 := hχ2 _ ⟨v, rfl⟩ x
      have n1 := Complex.exp_ne_zero (q x)
      have n2 := Complex.exp_ne_zero (q (x + Ha.Pw w v))
      rw [Complex.exp_neg, Complex.exp_neg]
      have k1 := mul_inv_cancel₀ n1
      have k2 := mul_inv_cancel₀ n2
      generalize (Complex.exp (q x))⁻¹ = a₁ at *
      generalize (Complex.exp (q (x + Ha.Pw w v)))⁻¹ = a₂ at *
      generalize χl (Ha.Pw w v) * Complex.exp _ = A at *
      linear_combination a₁ * e1 + a₁ * a₂ * fr j (x + Ha.Pw w v) * e2 -
        a₁ * θ (x + Ha.Pw w v) * fr j (x + Ha.Pw w v) * k2 + a₂ * A * θ x * fr j (x + Ha.Pw w v) * k1
  · intro j z pt h1 h2 h3
    beta_reduce
    rw [hgen j z pt h1 h2 h3, Complex.exp_neg]
    have n1 := Complex.exp_ne_zero (q z)
    field_simp
  · rw [← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    funext z
    rw [← an1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.ThetaSquareIntegrable
