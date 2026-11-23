import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ImmBlock

theorem aeval_mul_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommRing R] {alg : Algebra ℤ R}
    {F : MvPolynomial σ ℤ} {n : ℕ}
    (hF : F.IsHomogeneous n) (a : σ → R) (t : R) :
    MvPolynomial.aeval (fun i => a i * t) F = MvPolynomial.aeval a F * t ^ n := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    have h2 : Finsupp.degree d = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h2, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, _root_.mul_assoc]

theorem aeval_ringHom {σ A B : Type*} [CommRing A] [CommRing B] {algA : Algebra ℤ A} {algB : Algebra ℤ B}
    (φ : A →+* B) (a : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun i => φ (a i)) P = φ (MvPolynomial.aeval a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem differentiable_aeval {σ κ : Type*} [Fintype κ] (g : σ → κ) (P : MvPolynomial σ ℤ) :
    Differentiable ℂ (fun u : κ → ℂ => MvPolynomial.aeval (fun i => u (g i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (differentiable_apply _)

theorem form_mem {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (k₀ k : K) (n : ℕ) (F G : MvPolynomial (J k₀) ℤ) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous n) (c d : J k)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) G * y ⟨k, d⟩) :
    MvPolynomial.rename (Sigma.mk k₀) F * MvPolynomial.X ⟨k, c⟩ -
      MvPolynomial.rename (Sigma.mk k₀) G * MvPolynomial.X ⟨k, d⟩ ∈ mCoordIdeal y := by
  have hh := congrArg (MvPolynomial.C : Ω → MvPolynomial K Ω) h
  simp only [map_mul] at hh
  rw [mCoordIdeal, RingHom.mem_ker]
  simp only [mConeMap, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def]
  rw [aeval_mul_of_isHomogeneous hF (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_mul_of_isHomogeneous hG (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) F,
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) G]
  linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * hh

theorem differentiableAt_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ} {v : E}
    (ha : DifferentiableAt ℂ a v) (hb : DifferentiableAt ℂ b v) (h : b v ≠ 0) :
    DifferentiableAt ℂ (fun w => a w / b w) v := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv h)

theorem ker_bot_of_factor {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {f : E → F₁} {a : E → F₂} {Ψ : F₁ → F₂} {v₀ : E}
    (hf : DifferentiableAt ℂ f v₀) (hΨ : DifferentiableAt ℂ Ψ (f v₀)) (h : a =ᶠ[nhds v₀] Ψ ∘ f)
    (hk : (fderiv ℂ a v₀).ker = ⊥) : (fderiv ℂ f v₀).ker = ⊥ := by
  rw [h.fderiv_eq, fderiv_comp v₀ hΨ hf] at hk
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ f v₀ u = 0 := hu
  have : u ∈ ((fderiv ℂ Ψ (f v₀)).comp (fderiv ℂ f v₀)).ker := by
    change (fderiv ℂ Ψ (f v₀)) (fderiv ℂ f v₀ u) = 0
    rw [hu', map_zero]
  rwa [hk] at this

theorem immersion_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  intro X Ω _ _ ξ K _ J _ y k₀ hTie hEmb e M _ A U lam hE κ _ ix x p hp j hj
  classical
  have hev : ∀ (z : (Σ k, J k) → ℂ) (f : MRing J),
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := fun z f => by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  set G : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun v => lam x ((A.chart j).symm v) with hGdef
  set v₀ : Fin e → ℂ := A.chart j x with hv₀
  have hG0 : G v₀ = lam x x := by
    simp only [hGdef, hv₀]
    rw [(A.chart j).left_inv hj]
  have hS : v₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    change (A.chart j).symm (A.chart j x) ∈ U x
    rw [(A.chart j).left_inv hj]
    exact hE.mem_U x
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U x) :=
    (A.chart j).isOpen_inter_preimage_symm (hE.isOpen x)
  have hAn : ∀ q, DifferentiableAt ℂ (fun v => G v q) v₀ := fun q =>
    (hE.holo x q j v₀ hS).differentiableAt
  have hCo : ∀ q, ContinuousAt (fun v => G v q) v₀ := fun q => (hAn q).continuousAt
  have hw : lam x x ∈ mcPts (mCoordIdeal y) := hE.mem x x (hE.mem_U x)
  have hwpts : lam x x ∈ Small.ptsOver ℂ (mCoordIdeal y) :=
    ⟨hw.1, fun f hf => by rw [← hev]; exact hw.2 f hf⟩
  choose r hr using hw.1
  set p' : (k : K) → J k := Function.update r k₀ (ix p) with hp'def
  have hp'0 : p' k₀ = ix p := by simp [hp'def]
  have hp' : ∀ k, lam x x ⟨k, p' k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hp'0]
      exact hp
    · rw [hp'def, Function.update_of_ne h]
      exact hr k
  have hblk := fun k => GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hTie hEmb ℂ (lam x x) hwpts (ix p) k (p' k) hp (hp' k)
  choose n F hFh hFr hFn using hblk

  set f : (Fin e → ℂ) → κ → ℂ := fun v i => G v ⟨k₀, ix i⟩ / G v ⟨k₀, ix p⟩ with hfdef
  have ht0 : G v₀ ⟨k₀, ix p⟩ ≠ 0 := by rw [hG0]; exact hp
  have hfd : DifferentiableAt ℂ f v₀ :=
    by
    refine differentiableAt_pi.2 fun i => ?_
    have h := differentiableAt_quot (hAn ⟨k₀, ix i⟩) (hAn ⟨k₀, ix p⟩) ht0
    exact h

  set ev : MvPolynomial (J k₀) ℤ → (κ → ℂ) → ℂ :=
    fun P u => MvPolynomial.aeval (fun i' : J k₀ => u (ix.symm i')) P with hevdef
  have hevd : ∀ P, Differentiable ℂ (ev P) := fun P => differentiable_aeval (fun i' => ix.symm i') P
  have hscale : ∀ v k (d : J k), ev (F k d) (f v) =
      MvPolynomial.aeval (fun i' : J k₀ => G v ⟨k₀, i'⟩) (F k d) * ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k := by
    intro v k d
    rw [← aeval_mul_of_isHomogeneous (hFh k d)]
    simp only [hevdef, hfdef, Equiv.apply_symm_apply, div_eq_mul_inv]
  have hden0 : ∀ k, ev (F k (p' k)) (f v₀) ≠ 0 := by
    intro k
    rw [hscale, hG0]
    exact mul_ne_zero (hFn k) (pow_ne_zero _ (inv_ne_zero hp))
  set Ψ : (κ → ℂ) → (Σ k, J k) → ℂ := fun u q => ev (F q.1 q.2) u / ev (F q.1 (p' q.1)) u with hΨdef
  have hΨd : DifferentiableAt ℂ Ψ (f v₀) :=
    by
    refine differentiableAt_pi.2 fun q => ?_
    have h := differentiableAt_quot (hevd (F q.1 q.2) (f v₀)) (hevd (F q.1 (p' q.1)) (f v₀)) (hden0 q.1)
    exact h

  have e1 : ∀ᶠ v in nhds v₀, G v ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hSo.mem_nhds hS] with v hv
    exact hE.mem x _ hv.2
  have e2 : ∀ᶠ v in nhds v₀, ∀ k, G v ⟨k, p' k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (hCo ⟨k, p' k⟩).eventually_ne (by rw [hG0]; exact hp' k)
  have e3 : ∀ᶠ v in nhds v₀, ∀ k, ev (F k (p' k)) (f v) ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (((hevd _).continuous.continuousAt).comp hfd.continuousAt).eventually_ne (hden0 k)
  have e4 : ∀ᶠ v in nhds v₀, G v ⟨k₀, ix p⟩ ≠ 0 := (hCo _).eventually_ne ht0
  have hfac : (fun v => affCoord p' (G v)) =ᶠ[nhds v₀] Ψ ∘ f := by
    filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
    funext q
    obtain ⟨k, d⟩ := q
    have hmem := form_mem y k₀ k (n k) (F k d) (F k (p' k)) (hFh k d) (hFh k (p' k)) (p' k) d (hFr k d)
    have h0 := h1.2 _ hmem
    rw [hev] at h0
    simp only [map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def] at h0
    have hrel : ev (F k d) (f v) * G v ⟨k, p' k⟩ = ev (F k (p' k)) (f v) * G v ⟨k, d⟩ := by
      rw [hscale, hscale]
      linear_combination ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k * h0
    change G v ⟨k, d⟩ / G v ⟨k, p' k⟩ = ev (F k d) (f v) / ev (F k (p' k)) (f v)
    rw [div_eq_div_iff (h2 k) (h3 k)]
    linear_combination -hrel
  have hk : (fderiv ℂ (fun v => affCoord p' (G v)) v₀).ker = ⊥ :=
    hE.immersion x p' hp' j hj
  exact ⟨hfd, ker_bot_of_factor hfd hΨd hfac hk⟩

end GlobalTheory.CompanionTheory.Ar.ImmBlock
