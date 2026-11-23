import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ConeImage

theorem exists_compact_cover {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (h : Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤) :
    ∃ K : Set (Fin g → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, ∃ n n' : Fin g → ℤ,
      z = w + τ *ᵥ ofIntVec n + ofIntVec n' := by
  let L : (Fin g → ℝ) × (Fin g → ℝ) → (Fin g → ℂ) :=
    fun x => τ *ᵥ ofRealVec x.1 + ofRealVec x.2
  have hc : Continuous L := by
    have h1 : Continuous (ofRealVec : (Fin g → ℝ) → (Fin g → ℂ)) := by
      unfold ofRealVec; fun_prop
    exact (continuous_const.matrix_mulVec (h1.comp continuous_fst)).add (h1.comp continuous_snd)
  have hadd : ∀ a b : Fin g → ℝ, ofRealVec (a + b) = ofRealVec a + ofRealVec b := by
    intro a b; ext i; simp [ofRealVec]
  have hsm : ∀ (r : ℝ) (a : Fin g → ℝ), ofRealVec (r • a) = (r : ℂ) • ofRealVec a := by
    intro r a; ext i; simp [ofRealVec]
  have hint : ∀ n : Fin g → ℤ, ofIntVec n = ofRealVec (fun i => (n i : ℝ)) := by
    intro n; ext i; simp [ofRealVec, ofIntVec]
  have hs : ∀ z, ∃ x, z = L x := by
    intro z
    have hz : z ∈ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, n', rfl⟩ := hx
      exact ⟨(fun i => (n i : ℝ), fun i => (n' i : ℝ)), by simp only [L, hint]⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp [L, this]
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [L, Prod.fst_add, Prod.snd_add, hadd, Matrix.mulVec_add]; abel
    | smul r x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨r • a, ?_⟩
      simp only [L, Prod.smul_fst, Prod.smul_snd, hsm, Matrix.mulVec_smul]
      ext i; simp [mul_add]
  refine ⟨L '' (Set.Icc 0 1), isCompact_Icc.image hc, fun z => ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := hs z
  refine ⟨L (fun i => Int.fract (a i), fun i => Int.fract (b i)), ⟨_, ?_, rfl⟩,
    fun i => ⌊a i⌋, fun i => ⌊b i⌋, ?_⟩
  · exact ⟨⟨fun i => Int.fract_nonneg _, fun i => Int.fract_nonneg _⟩,
      ⟨fun i => (Int.fract_lt_one _).le, fun i => (Int.fract_lt_one _).le⟩⟩
  · have ha : a = (fun i => Int.fract (a i)) + fun i => ((⌊a i⌋ : ℤ) : ℝ) := by ext i; simp
    have hb : b = (fun i => Int.fract (b i)) + fun i => ((⌊b i⌋ : ℤ) : ℝ) := by ext i; simp
    simp only [L, hint]
    conv_lhs => rw [ha, hb]
    simp only [hadd, Matrix.mulVec_add]; abel

theorem isClosed_cone {E ι : Type*} [TopologicalSpace E] {f : E → ι → ℂ} (hf : Continuous f)
    (h0 : ∀ z, f z ≠ 0) {K : Set E} (hK : IsCompact K) :
    IsClosed {p : ι → ℂ | ∃ t : ℂ, ∃ z ∈ K, p = t • f z} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h1 : IsClosed {x : (ι → ℂ) × K | ∀ c c', x.1 c * f x.2 c' = x.1 c' * f x.2 c} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_eq ?_ ?_ <;> fun_prop
  convert isClosedMap_fst_of_compactSpace _ h1 using 1
  ext p
  constructor
  · rintro ⟨t, z, hz, rfl⟩
    refine ⟨(t • f z, ⟨z, hz⟩), fun c c' => ?_, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rintro ⟨⟨p, z, hz⟩, h, rfl⟩
    obtain ⟨c, hc⟩ := Function.ne_iff.mp (h0 z)
    have hc' : f z c ≠ 0 := hc
    refine ⟨p c / f z c, z, hz, ?_⟩
    ext c'
    have := h c c'
    simp only at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -this

theorem exists_continuous_slope {σ : Type*} (p : Polynomial (MvPolynomial σ ℂ)) :
    ∃ k : (σ → ℂ) × ℂ × ℂ → ℂ, Continuous k ∧ ∀ u s s',
      p.eval₂ (MvPolynomial.eval u) s' - p.eval₂ (MvPolynomial.eval u) s
        = (s' - s) * k (u, s, s') ∧
      k (u, s, s) = p.derivative.eval₂ (MvPolynomial.eval u) s := by
  induction p using Polynomial.induction_on with
  | C a => exact ⟨0, continuous_zero, fun u s s' => by simp⟩
  | add p q hp hq =>
    obtain ⟨k, hk, h⟩ := hp
    obtain ⟨l, hl, h'⟩ := hq
    refine ⟨k + l, hk.add hl, fun u s s' => ⟨?_, ?_⟩⟩
    · simp only [Polynomial.eval₂_add, Pi.add_apply]
      linear_combination (h u s s').1 + (h' u s s').1
    · simp [Polynomial.eval₂_add, (h u s s').2, (h' u s s').2]
  | monomial n a hp =>
    obtain ⟨k, hk, h⟩ := hp
    refine ⟨fun x => k x * x.2.2 + MvPolynomial.eval x.1 a * x.2.1 ^ n, ?_, fun u s s' => ⟨?_, ?_⟩⟩
    · have := MvPolynomial.continuous_eval a
      fun_prop
    · have := (h u s s').1
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at this ⊢
      linear_combination s' * this
    · dsimp only
      rw [(h u s s).2, pow_succ, ← mul_assoc, Polynomial.derivative_mul]
      simp [Polynomial.eval₂_add, Polynomial.eval₂_mul]

theorem map_eval₂ {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (r : MvPolynomial σ ℂ) :
    φ (j r) = MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i))) r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [← MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem map_eval₂' {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (a : A) (r : Polynomial (MvPolynomial σ ℂ)) :
    φ (r.eval₂ j.toRingHom a) =
      r.eval₂ (MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i)))) (φ a) := by
  have := Polynomial.hom_eval₂ r j.toRingHom (φ : A →+* ℂ) a
  rw [show φ (r.eval₂ j.toRingHom a) = _ from this]
  congr 1
  exact RingHom.ext fun x => map_eval₂ j φ x

theorem derivation_eq_zero {σ A : Type*} [CommRing A] [Algebra ℂ A]
    (j : MvPolynomial σ ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial σ ℂ))
    (q : MvPolynomial σ ℂ) (hp : p.eval₂ j.toRingHom a = 0)
    (hb : ∀ b : A, ∃ r : Polynomial (MvPolynomial σ ℂ), j q * b = r.eval₂ j.toRingHom a)
    (φ : A →ₐ[ℂ] ℂ) (hq : φ (j q) ≠ 0) (hp' : φ (p.derivative.eval₂ j.toRingHom a) ≠ 0)
    (D : A → ℂ) (hadd : ∀ x y, D (x + y) = D x + D y)
    (hmul : ∀ x y, D (x * y) = D x * φ y + φ x * D y)
    (hC : ∀ c : ℂ, D (algebraMap ℂ A c) = 0) (hX : ∀ i, D (j (MvPolynomial.X i)) = 0) (b : A) :
    D b = 0 := by
  have h1 : ∀ r, D (j r) = 0 := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, hC]
    | add p q hp hq => simp [hadd, hp, hq]
    | mul_X p i hp => simp [hmul, hp, hX]
  have h2 : ∀ r : Polynomial (MvPolynomial σ ℂ),
      D (r.eval₂ j.toRingHom a) = φ (r.derivative.eval₂ j.toRingHom a) * D a := by
    intro r
    induction r using Polynomial.induction_on with
    | C c => simp [h1]
    | add p q hp hq =>
      rw [Polynomial.eval₂_add, hadd, hp, hq, Polynomial.derivative_add, Polynomial.eval₂_add,
        map_add]; ring
    | monomial n c hp =>
      rw [pow_succ, ← mul_assoc, Polynomial.derivative_mul, Polynomial.eval₂_mul, hmul, hp]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.derivative_X, Polynomial.eval₂_one, map_add, map_mul, map_one]
      ring
  have h0 : D 0 = 0 := by simpa using hC 0
  have ha : D a = 0 := by
    have := h2 p
    rw [hp, h0] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hp'
  obtain ⟨r, hr⟩ := hb b
  have := h2 r
  rw [← hr, hmul, h1, ha] at this
  simpa [hq] using this

theorem exists_nhds_subset_range {d : ℕ} {A W : Type*} [CommRing A] [Algebra ℂ A]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (hd : d ≤ Module.finrank ℂ W)
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hp : p.eval₂ j.toRingHom a = 0)
    (hpq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (hb : ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (Φ : W → A →ₐ[ℂ] ℂ) (hΦ : ∀ b, Differentiable ℂ fun w => Φ w b) (w₀ : W)
    (hq : Φ w₀ (j q) ≠ 0) (himm : ∀ ξ, (∀ b, fderiv ℂ (fun w => Φ w b) w₀ ξ = 0) → ξ = 0) :
    ∃ U ∈ 𝓝 (⇑(Φ w₀) : A → ℂ), ∀ φ : A →ₐ[ℂ] ℂ, ⇑φ ∈ U → ∃ w, φ = Φ w := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hp' : Φ w₀ (p.derivative.eval₂ j.toRingHom a) ≠ 0 := by
    intro h
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hpq
    have := congrArg (fun r => Φ w₀ (Polynomial.eval₂ j.toRingHom a r)) hαβ
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hp, map_add, map_mul, h,
      Polynomial.eval₂_C, mul_zero, map_zero, add_zero] at this
    exact hq this.symm
  let u : W → Fin d → ℂ := fun w i => Φ w (j (MvPolynomial.X i))
  have hu : Differentiable ℂ u := differentiable_pi.mpr fun i => hΦ _
  have hus : HasStrictFDerivAt u (fderiv ℂ u w₀) w₀ :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiable hu Set.univ w₀ trivial).hasStrictFDerivAt
  have hinj : Function.Injective (fderiv ℂ u w₀) := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    refine himm ξ fun b => derivation_eq_zero j a p q hp hb (Φ w₀) hq hp'
      (fun b => fderiv ℂ (fun w => Φ w b) w₀ ξ) ?_ ?_ ?_ ?_ b
    · intro x y
      simp only [map_add]
      rw [fderiv_fun_add (hΦ x w₀) (hΦ y w₀)]; rfl
    · intro x y
      simp only [map_mul]
      rw [fderiv_fun_mul (hΦ x w₀) (hΦ y w₀)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · intro c
      simp
    · intro i
      have := congrFun hξ i
      rw [fderiv_pi (fun i => hΦ _ w₀)] at this
      exact this
  have hsurj : (fderiv ℂ u w₀).range = ⊤ := by
    have h1 := LinearMap.finrank_range_of_inj (f := (fderiv ℂ u w₀ : W →ₗ[ℂ] (Fin d → ℂ))) hinj
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [Module.finrank_fin_fun]
    exact hd.trans h1.ge
  have hmap := hus.map_nhds_eq_of_surj hsurj
  obtain ⟨k, hk, hk'⟩ := exists_continuous_slope p
  have hk0 : k (u w₀, Φ w₀ a, Φ w₀ a) ≠ 0 := by
    rw [(hk' _ _ (Φ w₀ a)).2, ← map_eval₂']; exact hp'
  have hev : ∀ᶠ x in 𝓝 (u w₀, Φ w₀ a, Φ w₀ a), k x ≠ 0 := hk.continuousAt.eventually_ne hk0
  obtain ⟨U₁, hU₁, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨V₁, hV₁, V₂, hV₂, hVV⟩ := mem_nhds_prod_iff.mp hV
  have hW : (fun w => Φ w a) ⁻¹' V₂ ∈ 𝓝 w₀ := (hΦ a).continuous.continuousAt hV₂
  have hU₂ : u '' ((fun w => Φ w a) ⁻¹' V₂) ∈ 𝓝 (u w₀) := hmap ▸ image_mem_map hW
  have c1 : Continuous fun (x : A → ℂ) (i : Fin d) => x (j (MvPolynomial.X i)) := by fun_prop
  have c2 : Continuous fun (x : A → ℂ) => x a := by fun_prop
  have c3 : Continuous fun (x : A → ℂ) => x (j q) := by fun_prop
  refine ⟨_, inter_mem (inter_mem (c1.continuousAt (inter_mem hU₁ hU₂)) (c2.continuousAt hV₁))
    (c3.continuousAt.eventually_ne hq), ?_⟩
  rintro φ ⟨⟨⟨h1, w, hw, h2⟩, h3⟩, h4⟩
  refine ⟨w, ?_⟩
  have h2' : (fun i => φ (j (MvPolynomial.X i))) = u w := h2.symm
  have hk1 : k (u w, φ a, Φ w a) ≠ 0 :=
    hUV (Set.mk_mem_prod (h2' ▸ h1) (hVV (Set.mk_mem_prod h3 hw)))
  have e1 := map_eval₂' j φ a p
  have e2 := map_eval₂' j (Φ w) a p
  rw [hp, map_zero] at e1 e2
  rw [h2'] at e1
  have ha : Φ w a = φ a := by
    have := (hk' (u w) (φ a) (Φ w a)).1
    rw [← e1, ← e2, sub_zero] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this.symm).resolve_right hk1)
  ext b
  obtain ⟨r, hr⟩ := hb b
  have f1 := map_eval₂' j φ a r
  have f2 := map_eval₂' j (Φ w) a r
  rw [← hr, map_mul] at f1 f2
  have hqq : Φ w (j q) = φ (j q) := by rw [map_eval₂, map_eval₂ j φ, h2']
  rw [h2'] at f1
  rw [ha, hqq] at f2
  exact mul_left_cancel₀ (h4 : φ (j q) ≠ 0) (f1.trans f2.symm)

theorem differentiable_eval {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {f : W → ι → ℂ} (hf : ∀ c, Differentiable ℂ fun w => f w c) (F : MvPolynomial ι ℂ) :
    Differentiable ℂ fun w => MvPolynomial.eval (f w) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hf i)

theorem cone_eq_zeroLocus {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : ι → E → ℂ} (hf : ∀ c, Differentiable ℂ (f c))
    (h0 : ∀ z, ∃ c, f c z ≠ 0)
    (htan : ∀ (z ξ : E) (γ : ℂ), (∀ c, fderiv ℂ (f c) z ξ = γ * f c z) → ξ = 0)
    (hcl : IsClosed {p : ι → ℂ | ∃ (t : ℂ) (z : E), p = fun c => t * f c z})
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), MvPolynomial.eval (fun c => t * f c z) F = 0)
    [IsDomain (MvPolynomial ι ℂ ⧸ I)] {d : ℕ} (hd : d ≤ Module.finrank ℂ E + 1)
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial ι ℂ ⧸ I) (hj : Function.Injective j)
    (a : MvPolynomial ι ℂ ⧸ I) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hq : q ≠ 0) (hp : p.eval₂ j.toRingHom a = 0)
    (hpq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (hb : ∀ b, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a)
    (hconn : ∀ b : MvPolynomial ι ℂ ⧸ I, b ≠ 0 → IsConnected {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
      ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b ≠ 0})
    (hdense : ∀ b : MvPolynomial ι ℂ ⧸ I, b ≠ 0 → {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
      ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆
      closure {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
        ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b ≠ 0})
    (y : ι → ℂ) (hy : ∀ F ∈ I, MvPolynomial.eval y F = 0) :
    ∃ (t : ℂ) (z : E), y = fun c => t * f c z := by
  let pt : ∀ y : ι → ℂ, (∀ F ∈ I, MvPolynomial.eval y F = 0) → (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    fun y hy => Ideal.Quotient.liftₐ I (MvPolynomial.aeval y) fun F hF => hy F hF
  have hpt : ∀ y hy F, pt y hy (Ideal.Quotient.mk I F) = MvPolynomial.eval y F := by
    intro y hy F
    rfl
  let Φ : ℂ × E → (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ :=
    fun w => pt (fun c => w.1 * f c w.2) fun F hF => (hI F).mp hF _ _
  have hΦ : ∀ w F, Φ w (Ideal.Quotient.mk I F) = MvPolynomial.eval (fun c => w.1 * f c w.2) F :=
    fun w F => hpt _ _ F
  have hΦX : ∀ w c, Φ w (Ideal.Quotient.mk I (MvPolynomial.X c)) = w.1 * f c w.2 := by
    intro w c; rw [hΦ, MvPolynomial.eval_X]
  have hΦd : ∀ b, Differentiable ℂ fun w => Φ w b := by
    intro b
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [hΦ]
    exact differentiable_eval (fun c => differentiable_fst.mul ((hf c).comp differentiable_snd)) F
  have hne : ∀ b, b ≠ 0 → ∃ w, Φ w b ≠ 0 := by
    intro b hb
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra! h
    exact hb (Ideal.Quotient.eq_zero_iff_mem.mpr ((hI F).mpr fun t z => hΦ (t, z) F ▸ h (t, z)))
  obtain ⟨c₀, hc₀⟩ := h0 0
  have hX : Ideal.Quotient.mk I (MvPolynomial.X c₀) ≠ 0 := by
    intro h
    have := hΦX (1, 0) c₀
    rw [h, map_zero, one_mul] at this
    exact hc₀ this.symm
  have hb0 : j q * Ideal.Quotient.mk I (MvPolynomial.X c₀) ≠ 0 :=
    mul_ne_zero (fun h => hq (hj (h.trans (map_zero j).symm))) hX
  set b₀ := j q * Ideal.Quotient.mk I (MvPolynomial.X c₀) with hb₀
  set D := {x : (MvPolynomial ι ℂ ⧸ I) → ℂ |
    ∃ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ = x ∧ x b₀ ≠ 0} with hD
  let Y : Set ((MvPolynomial ι ℂ ⧸ I) → ℂ) :=
    (fun x c => x (Ideal.Quotient.mk I (MvPolynomial.X c))) ⁻¹'
      {p : ι → ℂ | ∃ (t : ℂ) (z : E), p = fun c => t * f c z}
  have hY : IsClosed Y := hcl.preimage (by fun_prop)
  have hYΦ : ∀ w, ⇑(Φ w) ∈ Y := fun w => ⟨w.1, w.2, funext fun c => hΦX w c⟩
  have hYΦ' : ∀ φ : (MvPolynomial ι ℂ ⧸ I) →ₐ[ℂ] ℂ, ⇑φ ∈ Y → ∃ w, φ = Φ w := by
    rintro φ ⟨t, z, h⟩
    refine ⟨(t, z), Ideal.Quotient.algHom_ext ℂ (MvPolynomial.algHom_ext fun c => ?_)⟩
    exact (congrFun h c).trans (hΦX (t, z) c).symm
  have hDY : D ⊆ Y := by
    haveI : PreconnectedSpace D := Subtype.preconnectedSpace (hconn b₀ hb0).isPreconnected
    have hclopen : IsClopen (Subtype.val ⁻¹' Y : Set D) := by
      refine ⟨hY.preimage continuous_subtype_val, isOpen_iff_mem_nhds.mpr ?_⟩
      rintro ⟨_, φ, rfl, hφ⟩ hφY
      obtain ⟨w₀, rfl⟩ := hYΦ' φ hφY
      have hφ' := hφ
      rw [hb₀, map_mul, hΦX] at hφ'
      have ht : w₀.1 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hφ')
      obtain ⟨U, hU, hU'⟩ := exists_nhds_subset_range (W := ℂ × E)
        (by rw [Module.finrank_prod, Module.finrank_self, add_comm]; exact hd)
        j a p q hp hpq hb Φ hΦd w₀ (left_ne_zero_of_mul hφ') (by
          intro ξ hξ
          have key : ∀ c, ξ.1 * f c w₀.2 + w₀.1 * fderiv ℂ (f c) w₀.2 ξ.2 = 0 := by
            intro c
            have h1 := hξ (Ideal.Quotient.mk I (MvPolynomial.X c))
            simp only [hΦX] at h1
            have h2 := (hasFDerivAt_fst (𝕜 := ℂ) (p := w₀)).mul
              (((hf c) w₀.2).hasFDerivAt.comp w₀ hasFDerivAt_snd)
            have h3 : fderiv ℂ (fun w : ℂ × E => w.1 * f c w.2) w₀ = _ := h2.fderiv
            rw [h3] at h1
            simp at h1
            linear_combination h1
          have h2 : ξ.2 = 0 := htan w₀.2 ξ.2 (-ξ.1 / w₀.1) fun c => by
            field_simp
            linear_combination key c
          obtain ⟨c, hc⟩ := h0 w₀.2
          have h1 := key c
          rw [h2, map_zero, mul_zero, add_zero] at h1
          exact Prod.ext ((mul_eq_zero.mp h1).resolve_right hc) h2)
      refine mem_of_superset (continuous_subtype_val.continuousAt hU) ?_
      rintro ⟨_, ψ, rfl, hψ⟩ hψU
      obtain ⟨w, rfl⟩ := hU' ψ hψU
      exact hYΦ w
    obtain ⟨w, hw⟩ := hne b₀ hb0
    have := hclopen.eq_univ ⟨⟨Φ w, Φ w, rfl, hw⟩, hYΦ w⟩
    intro x hx
    exact this.ge (Set.mem_univ (⟨x, hx⟩ : D))
  have := closure_minimal hDY hY (hdense b₀ hb0 ⟨pt y hy, rfl, by simp⟩)
  obtain ⟨t, z, h⟩ := this
  refine ⟨t, z, ?_⟩
  rw [← h]
  ext c
  simp only [hpt, MvPolynomial.eval_X]

end GlobalTheory.ConeImage

namespace GlobalTheory

theorem thetaCone_eq_zeroLocus : (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ z, ∃ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) ∧ f z ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) → fderiv ℂ f z ξ = γ * f z) → ξ = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 2 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → I.IsPrime ∧ ringKrullDim (MvPolynomial (Fin g → Fin N) ℂ ⧸ I) ≤ (g + 1 : ℕ)) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (I : Ideal (MvPolynomial (Fin g → Fin N) ℂ)), (∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : Fin g → ℂ), MvPolynomial.eval (fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) F = 0) → ∀ p : (Fin g → Fin N) → ℂ, (∀ F ∈ I, MvPolynomial.eval p F = 0) → ∃ (t : ℂ) (z : Fin g → ℂ), p = fun c => t * theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 g τ hτ N hN I hI y hy
  obtain ⟨hprime, hdim⟩ := h6 g τ hτ N (by omega) I hI
  obtain ⟨d, j, a, p, q, hd, hj, -, -, -, hp, hq, hpq, hb⟩ :=
    h7 (MvPolynomial (Fin g → Fin N) ℂ ⧸ I)
  obtain ⟨h1, -⟩ := h1 g τ hτ N (by omega)
  replace h2 := h2 g τ hτ N (by omega)
  replace h3 := h3 g τ hτ N (by omega)
  replace h4 := h4 g τ hτ N hN
  set f : (Fin g → Fin N) → (Fin g → ℂ) → ℂ :=
    fun c z => theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) with hf
  have hdiff : ∀ c, Differentiable ℂ (f c) := fun c => (h1 c).1
  have h0 : ∀ z, ∃ c, f c z ≠ 0 := by
    intro z
    by_contra! h
    obtain ⟨F, hF, hFz⟩ := h3 z
    refine hFz ?_
    have := h2 F hF
    clear hF hFz
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have htan : ∀ (z ξ : Fin g → ℂ) (γ : ℂ), (∀ c, fderiv ℂ (f c) z ξ = γ * f c z) → ξ = 0 := by
    intro z ξ γ h
    refine h4 z ξ γ fun F hF => ?_
    have := h2 F hF
    clear hF
    suffices Differentiable ℂ F ∧ fderiv ℂ F z ξ = γ * F z from this.2
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact ⟨hdiff c, h c⟩
    | zero => exact ⟨differentiable_const 0, by simp⟩
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      rw [fderiv_add (hx.1 z) (hy.1 z), ContinuousLinearMap.add_apply, hx.2, hy.2, Pi.add_apply,
        mul_add]
    | smul r x _ hx =>
      refine ⟨hx.1.const_smul r, ?_⟩
      rw [fderiv_const_smul (hx.1 z), ContinuousLinearMap.smul_apply, hx.2, Pi.smul_apply,
        smul_eq_mul, smul_eq_mul]
      ring
  have hcl : IsClosed {p : (Fin g → Fin N) → ℂ |
      ∃ (t : ℂ) (z : Fin g → ℂ), p = fun c => t * f c z} := by
    obtain ⟨K, hK, hK'⟩ := ConeImage.exists_compact_cover τ (h5 g τ hτ).2.1
    convert ConeImage.isClosed_cone (f := fun z c => f c z)
      (continuous_pi fun c => (hdiff c).continuous)
      (fun z hz => by obtain ⟨c, hc⟩ := h0 z; exact hc (congrFun hz c)) hK using 1
    ext p
    constructor
    · rintro ⟨t, z, rfl⟩
      obtain ⟨w, hw, n, n', rfl⟩ := hK' z
      refine ⟨t * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ w)), w, hw, ?_⟩
      ext c
      have : f c (w + τ *ᵥ ofIntVec n + ofIntVec n') = _ * f c w := (h1 c).2 n n' w
      rw [this, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · rintro ⟨t, z, -, rfl⟩
      exact ⟨t, z, rfl⟩
  refine ConeImage.cone_eq_zeroLocus hdiff h0 htan hcl I hI (d := d) ?_ j hj a p q hq
    ((hp p).mpr dvd_rfl) hpq hb (h8 _) (h9 _) y hy
  rw [hd] at hdim
  rw [Module.finrank_fin_fun]
  exact_mod_cast hdim

end GlobalTheory
