import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStE

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

def prFib (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (w : Fin (D + 1) → ℂ) : Set (Ix κ → ℂ) :=
  {z | z ∈ pts (coordIdeal ℤ x) ∧ ∀ k, z (e k) = w k}

theorem exists_proj_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e)
    {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) : ∃ k, z (e k) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push Not at h; exact hz.1 (funext h)
  obtain ⟨q, hqm, hq⟩ := hfr.integral i
  have hg : ∀ j, ∃ g, coneMap ℤ (x ∘ e) g = ((q.coeff j : coneRing ℤ (x ∘ e)) : Polynomial Ω) :=
    fun j => (q.coeff j).2
  choose g hg using hg
  set n := q.natDegree
  let Q : MvPolynomial (Ix κ) ℤ := ∑ j ∈ Finset.range (n + 1), rename e (g j) * X i ^ j
  have hQ : Q ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker]
    rw [Polynomial.eval₂_eq_sum_range] at hq
    simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hg]
    convert hq using 2
    simp [coneMap]
  have hz0 := Fib.coneMap_eq_zero_of_mem_pts (coordIdeal_isHomogIdeal ℤ x) hz hQ
  have hze : z ∘ e = 0 := funext hcon
  have hcn : constantCoeff (g n) = 1 := by
    have h1 := congrArg (fun p => Polynomial.coeff p 0) (hg n)
    simp only [coeff_coneMap, homogeneousComponent_zero, aeval_C] at h1
    rw [hqm.coeff_natDegree] at h1
    simp at h1
    exact_mod_cast h1
  have h2 := congrArg (fun p => Polynomial.coeff p n) hz0
  simp only [Q, map_sum, map_mul, map_pow, Fib.coneMap_rename, hze] at h2
  have h3 : ∀ j, coneMap ℤ (0 : Fin (D + 1) → ℂ) (g j) =
      Polynomial.C ((constantCoeff (g j) : ℤ) : ℂ) := by
    intro j
    simp [coneMap]
  have hX : coneMap ℤ z (X i) = Polynomial.C (z i) * Polynomial.X := by simp [coneMap]
  simp only [h3, hX, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h2
  rw [Finset.sum_eq_single n] at h2
  · rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_pos rfl, hcn] at h2
    simp at h2
    exact hi h2.1
  · intro j _ hj
    rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_neg (Ne.symm hj)]
  · intro h; simp at h

def IsDiscr (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (Δ : MvPolynomial (Fin (D + 1)) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ w, eval w Δ ≠ 0 →
    (prFib x e w).Finite ∧ (prFib x e w).ncard = projDeg x e ∧
    (∀ z ∈ prFib x e w, ∃ (U : Set (Fin (D + 1) → ℂ)) (γ : (Fin (D + 1) → ℂ) → Ix κ → ℂ),
      IsOpen U ∧ w ∈ U ∧ DifferentiableOn ℂ γ U ∧ γ w = z ∧ ∀ w' ∈ U, γ w' ∈ prFib x e w') ∧
    ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) (g : MvPolynomial (Fin (D + 1)) ℤ),
      f.IsHomogeneous n → g.IsHomogeneous n → aeval (x ∘ e) g = secTrace x e n (aeval x f) →
      eval w (map (Int.castRingHom ℂ) g) = ∑ᶠ z ∈ prFib x e w, eval z (map (Int.castRingHom ℂ) f)

theorem exists_isDiscr {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) :
    ∃ Δ, IsDiscr x e Δ := by
  classical
  obtain ⟨G, hdeg, hTr, hsc⟩ := Fib.exists_gen x e hfr
  have hy0 : (x ∘ e) 0 ≠ 0 := Fib.coord_ne_zero _ hfr.free 0
  have hx0 : x (e 0) ≠ 0 := hy0
  let Δ0 : MvPolynomial (Fin (D + 1)) ℤ :=
    X 0 * Fib.homog 0 G.dd.totalDegree G.dd * Fib.homog 0 G.cc.totalDegree G.cc
  have hevΔ : ∀ w : Fin (D + 1) → ℂ, w 0 ≠ 0 →
      eval w (map (Int.castRingHom ℂ) Δ0) = w 0 * (w 0 ^ G.dd.totalDegree * Fib.deh w 0 G.dd) *
        (w 0 ^ G.cc.totalDegree * Fib.deh w 0 G.cc) := by
    intro w hw0
    rw [eval_map]
    simp only [Δ0, eval₂_mul, eval₂_X, Fib.eval₂_homog w 0 hw0 _ le_rfl]
  have hgood : ∀ w : Fin (D + 1) → ℂ, eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0 → G.Good w := by
    intro w hw
    have hw0 : w 0 ≠ 0 := by
      intro h0
      apply hw
      rw [eval_map]
      simp [Δ0, h0]
    rw [hevΔ w hw0] at hw
    refine ⟨hw0, fun m hm => ?_, fun h0 => hw (by rw [h0]; ring), fun h0 => hw (by rw [h0]; ring)⟩
    exact Fib.deh_eq_zero_of_deh_eq_zero (x ∘ e) w 0 hy0 hw0
      (fun f hf => by rw [hfr.free, Ideal.mem_bot] at hf; simp [hf]) hm
  refine ⟨map (Int.castRingHom ℂ) Δ0, ?_, fun w hw => ?_⟩
  · intro h0
    have h1 : Δ0 = 0 :=
      map_injective _ (RingHom.injective_int (Int.castRingHom ℂ)) (by rw [h0, map_zero])
    have h2 : aeval (x ∘ e) Δ0 = (x ∘ e) 0 * ((x ∘ e) 0 ^ G.dd.totalDegree *
        Fib.deh (x ∘ e) 0 G.dd) * ((x ∘ e) 0 ^ G.cc.totalDegree * Fib.deh (x ∘ e) 0 G.cc) := by
      simp only [Δ0, aeval_def, algebraMap_int_eq, eval₂_mul, eval₂_X,
        Fib.eval₂_homog _ 0 hy0 _ le_rfl]
    rw [h1, map_zero] at h2
    exact (mul_ne_zero (mul_ne_zero hy0 (mul_ne_zero (pow_ne_zero _ hy0) G.dd_ne))
      (mul_ne_zero (pow_ne_zero _ hy0) G.cc_ne)) h2.symm
  have hgw := hgood w hw
  have hfib : prFib x e w = Fib.fib x e w := rfl
  refine ⟨hfib ▸ G.fib_finite hx0 hgw, by rw [hfib, G.fib_ncard hx0 hgw, hdeg], ?_, ?_⟩
  · intro z hz
    have hWo : IsOpen {w : Fin (D + 1) → ℂ | eval w (map (Int.castRingHom ℂ) Δ0) ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    obtain ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩ :=
      G.exists_section hx0 hWo (fun w' hw' => hgood w' hw') (w := w) hw (z := z) hz
    exact ⟨U, γ, hU, hwU, hγ, hγw, hγf⟩
  · intro n f g hf hg hfg
    have hdf : aeval x f = x (e 0) ^ n * Fib.deh x (e 0) f :=
      Fib.aeval_eq_pow_mul_deh x (e 0) hx0 hf
    have hdg : aeval (x ∘ e) g = (x ∘ e) 0 ^ n * Fib.deh (x ∘ e) 0 g :=
      Fib.aeval_eq_pow_mul_deh (x ∘ e) 0 hy0 hg
    have hT : Fib.deh (x ∘ e) 0 g = fnTrace x e (Fib.deh x (e 0) f) := by
      rw [hdg, secTrace, hdf, mul_div_cancel_left₀ _ (pow_ne_zero _ hx0)] at hfg
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) hfg
    have htw := G.trace_w hgw (fnTrace x e) hTr hsc hT
    have hw0 := hgw.w0
    rw [hfib, G.finsum_fib hx0 hgw, eval_map, ← algebraMap_int_eq, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh w 0 hw0 hg, htw, ← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun ρ hρ => ?_
    have hρ' := (G.mem_roots).1 hρ
    rw [eval_map, ← aeval_def,
      Fib.aeval_eq_pow_mul_deh _ (e 0) (by rw [G.zOf_e hgw hρ' 0]; exact hw0) hf, G.zOf_e hgw hρ' 0]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
