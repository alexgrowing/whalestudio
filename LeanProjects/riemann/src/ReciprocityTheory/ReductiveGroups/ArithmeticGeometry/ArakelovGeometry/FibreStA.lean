import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def deh {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) : MvPolynomial ι ℤ →+* S :=
  eval₂Hom (Int.castRingHom S) fun i => v i / v i₀

def homog {ι : Type*} [DecidableEq ι] (i₀ : ι) (N : ℕ) (G : MvPolynomial ι ℤ) :
    MvPolynomial ι ℤ :=
  ∑ m ∈ G.support, monomial (m + Finsupp.single i₀ (N - m.degree)) (G.coeff m)

theorem homog_isHomogeneous {ι : Type*} [DecidableEq ι] (i₀ : ι) {N : ℕ} (G : MvPolynomial ι ℤ)
    (hN : G.totalDegree ≤ N) : (homog i₀ N G).IsHomogeneous N := by
  apply IsHomogeneous.sum
  intro m hm
  apply isHomogeneous_monomial
  have : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  have h := Finsupp.degree_single (R := ℕ) i₀ (N - m.degree)
  simp only [map_add, h]
  omega

theorem eval₂_homog {ι S : Type*} [Fintype ι] [DecidableEq ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {N : ℕ} (G : MvPolynomial ι ℤ) (hN : G.totalDegree ≤ N) :
    eval₂ (Int.castRingHom S) v (homog i₀ N G) = v i₀ ^ N * deh v i₀ G := by
  rw [homog, eval₂_sum, deh, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m.degree ≤ N := le_trans (le_totalDegree hm) hN
  rw [eval₂_monomial, Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
    Finsupp.prod_single_index (by simp)]
  have h1 : (m.prod fun i k => v i ^ k) = ∏ i, v i ^ m i :=
    Finsupp.prod_fintype _ _ (by simp)
  have h2 : ∏ i, (v i / v i₀) ^ m i = (∏ i, v i ^ m i) / v i₀ ^ m.degree := by
    rw [Finset.prod_congr rfl fun i _ => div_pow (v i) (v i₀) (m i), Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [h1, h2]
  have h3 : v i₀ ^ N = v i₀ ^ (N - m.degree) * v i₀ ^ m.degree := by
    rw [← pow_add]; congr 1; omega
  rw [h3]
  field_simp

theorem aeval_smul_of_isHomogeneous {ι S : Type*} [Fintype ι] [CommRing S]
    {f : MvPolynomial ι ℤ} {d : ℕ} (hf : f.IsHomogeneous d) (c : S) (v : ι → S) :
    aeval (fun i => c * v i) f = c ^ d * aeval v f := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hf (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem aeval_eq_pow_mul_deh {ι S : Type*} [Fintype ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {n : ℕ} {f : MvPolynomial ι ℤ} (hf : f.IsHomogeneous n) :
    aeval v f = v i₀ ^ n * deh v i₀ f := by
  have h : v = fun i => v i₀ * (v i / v i₀) := by
    funext i; rw [mul_div_cancel₀ _ hv]
  conv_lhs => rw [h]
  rw [aeval_smul_of_isHomogeneous hf]
  rfl

theorem deh_X {ι S : Type*} [Field S] (v : ι → S) (i₀ i : ι) : deh v i₀ (X i) = v i / v i₀ := by
  simp [deh]

theorem deh_rename {ι J S : Type*} [Field S] (v : ι → S) (e : J → ι) (j₀ : J)
    (m : MvPolynomial J ℤ) : deh v (e j₀) (rename e m) = deh (v ∘ e) j₀ m := by
  simp only [deh, coe_eval₂Hom, eval₂_rename]
  rfl

theorem deh_comp_rename {ι J S : Type*} [Field S] (v : ι → S) (e : J → ι) (j₀ : J) :
    (deh v (e j₀)).comp (rename e).toRingHom = deh (v ∘ e) j₀ := by
  ext m
  · simp [deh]
  · exact deh_rename v e j₀ (X m)

theorem deh_eq_zero_of_deh_eq_zero {ι : Type*} [Fintype ι] {Ω : Type*} [Field Ω]
    (x : ι → Ω) (z : ι → ℂ) (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (hP : ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0)
    {G : MvPolynomial ι ℤ} (hG : deh x i₀ G = 0) : deh z i₀ G = 0 := by
  classical
  have hH := homog_isHomogeneous i₀ G le_rfl
  have h1 : aeval x (homog i₀ G.totalDegree G) = 0 := by
    rw [aeval_def, algebraMap_int_eq, eval₂_homog x i₀ hx G le_rfl, hG, mul_zero]
  have h2 := hP _ (mem_coordIdeal_of_isHomogeneous ℤ x hH h1)
  rw [eval_map, eval₂_homog z i₀ hz G le_rfl] at h2
  exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz)

theorem mem_pts_of_deh {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] (x : ι → Ω) (z : ι → ℂ)
    (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (h : ∀ G : MvPolynomial ι ℤ, deh x i₀ G = 0 → deh z i₀ G = 0) :
    z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨fun h0 => hz (by rw [h0]; rfl), fun f hf => ?_⟩
  rw [coordIdeal, RingHom.mem_ker] at hf
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  have hd := homogeneousComponent_isHomogeneous d f
  have hx0 : aeval x (homogeneousComponent d f) = 0 := by
    rw [← coeff_coneMap, hf, Polynomial.coeff_zero]
  rw [aeval_eq_pow_mul_deh x i₀ hx hd] at hx0
  have hz0 := h _ ((mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hx))
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_eq_pow_mul_deh z i₀ hz hd, hz0, mul_zero]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem deh_apply {ι S : Type*} [Field S] (v : ι → S) (i₀ : ι) (F : MvPolynomial ι ℤ) :
    deh v i₀ F = eval₂ (Int.castRingHom S) (fun i => v i / v i₀) F := rfl

theorem eval₂_eq_zero_of_monic {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : R →+* T) (hker : ∀ m, φ m = 0 → ψ m = 0) {P : Polynomial R}
    (hP : P.Monic) {θ : S} {ρ : T}
    (hmin : ∀ H : Polynomial R, H.natDegree < P.natDegree → H.eval₂ φ θ = 0 →
      ∀ j, φ (H.coeff j) = 0)
    (hθ : P.eval₂ φ θ = 0) (hρ : P.eval₂ ψ ρ = 0) (hP1 : P ≠ 1) {H : Polynomial R}
    (hH : H.eval₂ φ θ = 0) : H.eval₂ ψ ρ = 0 := by
  have hdec := Polynomial.modByMonic_add_div H P
  have h1 : (H %ₘ P).eval₂ φ θ = 0 := by
    have := congrArg (Polynomial.eval₂ φ θ) hdec
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hθ, zero_mul, add_zero, hH] at this
    exact this
  have h2 := hmin _ (Polynomial.natDegree_modByMonic_lt H hP hP1) h1
  have h3 : (H %ₘ P).eval₂ ψ ρ = 0 := by
    rw [← Polynomial.eval_map]
    have : (H %ₘ P).map ψ = 0 := by
      ext j; rw [Polynomial.coeff_map, hker _ (h2 j), Polynomial.coeff_zero]
    rw [this, Polynomial.eval_zero]
  rw [← hdec, Polynomial.eval₂_add, Polynomial.eval₂_mul, hρ, zero_mul, add_zero, h3]

variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ}

structure Gen (x : ι → Ω) (e : Fin (D + 1) → ι) where
  Θ : MvPolynomial ι ℤ
  P : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  monic : P.Monic
  root : P.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0
  min : ∀ H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ), H.natDegree < P.natDegree →
    H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ) = 0 → ∀ j, deh (x ∘ e) 0 (H.coeff j) = 0
  dd : MvPolynomial (Fin (D + 1)) ℤ
  dd_ne : deh (x ∘ e) 0 dd ≠ 0
  Q : ι → Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hQ : ∀ i, deh (x ∘ e) 0 dd * deh x (e 0) (X i) = (Q i).eval₂ (deh (x ∘ e) 0) (deh x (e 0) Θ)
  cc : MvPolynomial (Fin (D + 1)) ℤ
  cc_ne : deh (x ∘ e) 0 cc ≠ 0
  U : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  V : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)
  hUV : (U * P + V * Polynomial.derivative P - Polynomial.C cc).map (deh (x ∘ e) 0) = 0

variable {x : ι → Ω} {e : Fin (D + 1) → ι}

def Gen.HG [DecidableEq ι] (G : Gen x e) (F : MvPolynomial ι ℤ) :
    Polynomial (MvPolynomial (Fin (D + 1)) ℤ) :=
  MvPolynomial.eval₂ (Int.castRingHom _) (fun o : Option ι => o.elim (Polynomial.C G.dd) G.Q)
    (homog none F.totalDegree (rename some F))

def Gen.evQ (G : Gen x e) {S : Type*} [Field S] (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) :
    ι → S :=
  fun i => (G.Q i).eval₂ ψ t / ψ G.dd

theorem Gen.HG_eval [DecidableEq ι] (G : Gen x e) {S : Type*} [Field S]
    (ψ : MvPolynomial (Fin (D + 1)) ℤ →+* S) (t : S) (hd : ψ G.dd ≠ 0) (F : MvPolynomial ι ℤ) :
    (G.HG F).eval₂ ψ t =
      ψ G.dd ^ F.totalDegree * MvPolynomial.eval₂ (Int.castRingHom S) (G.evQ ψ t) F := by
  have h1 : (G.HG F).eval₂ ψ t = MvPolynomial.eval₂ (Int.castRingHom S)
      (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t)
      (homog none F.totalDegree (rename some F)) := by
    rw [Gen.HG, ← Polynomial.coe_eval₂RingHom, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  have hv : (fun o : Option ι => (o.elim (Polynomial.C G.dd) G.Q).eval₂ ψ t) none ≠ 0 := by
    simpa using hd
  rw [h1, eval₂_homog _ none hv _ (totalDegree_rename_le _ _)]
  simp only [Option.elim, Polynomial.eval₂_C]
  congr 1
  rw [deh_apply, eval₂_rename]
  congr 1
  funext i
  simp [Gen.evQ, Polynomial.eval₂_C]

theorem Gen.dehomogenized_generator_eval (G : Gen x e) :
    G.evQ (deh (x ∘ e) 0) (deh x (e 0) G.Θ) = fun i => x i / x (e 0) := by
  funext i
  rw [Gen.evQ, ← G.hQ i, mul_div_cancel_left₀ _ G.dd_ne, deh_X]

theorem Gen.P_ne_one (G : Gen x e) : G.P ≠ 1 := by
  intro h1
  have := G.root
  rw [h1, Polynomial.eval₂_one] at this
  exact one_ne_zero this

theorem Gen.transfer [DecidableEq ι] (G : Gen x e) (w : Fin (D + 1) → ℂ)
    (hker : ∀ m, deh (x ∘ e) 0 m = 0 → deh w 0 m = 0) (hdw : deh w 0 G.dd ≠ 0)
    {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) {F : MvPolynomial ι ℤ}
    {H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)}
    (h : deh x (e 0) F = H.eval₂ (deh (x ∘ e) 0) (deh x (e 0) G.Θ)) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) (G.evQ (deh w 0) ρ) F = H.eval₂ (deh w 0) ρ := by
  have key := eval₂_eq_zero_of_monic (deh (x ∘ e) 0) (deh w 0) hker G.monic G.min G.root hρ
    G.P_ne_one (H := G.HG F - Polynomial.C (G.dd ^ F.totalDegree) * H) (by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ G.dd_ne,
        G.dehomogenized_generator_eval, ← deh_apply, h, map_pow, sub_self])
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, G.HG_eval _ _ hdw, map_pow,
    ← mul_sub, mul_eq_zero] at key
  exact sub_eq_zero.mp (key.resolve_left (pow_ne_zero _ hdw))

def Gen.zOf (G : Gen x e) (w : Fin (D + 1) → ℂ) (ρ : ℂ) : ι → ℂ :=
  fun i => w 0 * G.evQ (deh w 0) ρ i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem coneMap_eq_zero_of_mem_pts {J : Type} [Fintype J] {P : Ideal (MvPolynomial J ℤ)}
    (hP : IsHomogIdeal ℤ P) {z : J → ℂ} (hz : z ∈ pts P) {f : MvPolynomial J ℤ} (hf : f ∈ P) :
    coneMap ℤ z f = 0 := by
  ext d
  rw [coeff_coneMap, Polynomial.coeff_zero]
  have h := hz.2 _ (hP f hf d)
  rw [eval_map] at h
  rw [aeval_def, show algebraMap ℤ ℂ = Int.castRingHom ℂ from Subsingleton.elim _ _]
  exact h

theorem coneMap_rename {J J' : Type} {R : Type*} [CommRing R] [Algebra ℤ R] (x : J → R) (e : J' → J)
    (g : MvPolynomial J' ℤ) : coneMap ℤ x (rename e g) = coneMap ℤ (x ∘ e) g := by
  simp only [coneMap, aeval_rename]
  rfl

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
