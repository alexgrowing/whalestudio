import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusK

theorem flow_vanish {W : Type} [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ W) [FiniteDimensional ℂ S]
    (A : W →ₗ[ℂ] W) (hA : ∀ x ∈ S, A x ∈ S) (φ : ℝ → W →ₗ[ℂ] ℂ)
    (hφ : ∀ t x, HasDerivAt (fun s => φ s x) (φ t (A x)) t) (h0 : ∀ x ∈ S, φ 0 x = 0) :
    ∀ t, ∀ x ∈ S, φ t x = 0 := by
  let b := Module.finBasis ℂ S
  let M : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    Matrix.of fun i j => b.repr ⟨A (b i), hA _ (b i).2⟩ j
  let L : (Fin (Module.finrank ℂ S) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hexp : ∀ t (x : S), φ t x = ∑ j, b.repr x j * φ t (b j) := by
    intro t x
    have h := congrArg (φ t ∘ₗ S.subtype) (b.sum_repr x)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  have key : (fun t i => φ t (b i)) = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ y => L y) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨?_, trivial⟩) (fun t => ⟨?_, trivial⟩) ?_
    · refine hasDerivAt_pi.2 fun i => ?_
      refine (hφ t (b i)).congr_deriv ?_
      rw [hexp t ⟨A (b i), hA _ (b i).2⟩]
      simp [L, M, Matrix.mulVec, dotProduct]
    · simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ S) → ℂ)
    · funext i
      exact h0 _ (b i).2
  intro t x hx
  rw [hexp t ⟨x, hx⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun (congrFun key t) j
  simp only [Pi.zero_apply] at this
  rw [this, mul_zero]

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem deriv_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

theorem deriv_exp_entry' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) s := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

end Linfty

theorem deriv_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this

theorem deriv_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y)
    (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • Y)) ((∑ a, ∑ b, Y a b • E a b v : V) : H)) t := by
  have h1 := hD.2.2.1 Y hY v
  have h2 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) t := by
    have h3 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) (t - t) := by rw [sub_self]; exact h1
    exact h3.comp_sub_const t t
  have h4 := ((σ (NormedSpace.exp ((t : ℂ) • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  have h5 := oneParam n Y t (s - t)
  rw [add_sub_cancel] at h5
  rw [h5, hσ.1.2 _ (expUJ n ε Y hY t) _ (expUJ n ε Y hY (s - t))]
  rfl

def matOf {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ℓ : V →ₗ[ℂ] ℂ) :
    Arr V n 1 →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun G := Matrix.of fun a b => ℓ (at1 G a b)
  map_add' G G' := by
    ext a b
    simp [at1]
  map_smul' c G := by
    ext a b
    simp [at1]

theorem matOf_act {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Arr V n 1) :
    matOf ℓ ((∑ c, ∑ d, Y c d • arrE E 1 c d) G) =
      Y * matOf ℓ G - matOf ℓ G * Y +
        Matrix.of fun a b => ℓ (∑ c, ∑ d, Y c d • E c d (at1 G a b)) := by
  have h : ∀ c d a b, matOf ℓ (arrE E 1 c d G) a b =
      (if a = c then matOf ℓ G d b else 0) - (if b = d then matOf ℓ G a c else 0) + ℓ (E c d (at1 G a b)) := by
    intro c d a b
    have := congrArg ℓ (arr_operator_one_apply E c d G a b)
    rw [map_add, map_sub, apply_ite ℓ, apply_ite ℓ, map_zero] at this
    exact this
  ext a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Matrix.sum_apply,
    Matrix.smul_apply, h, smul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_zero]
  congr 2
  · rw [Finset.sum_comm]
    simp
  · simp [mul_comm]

theorem inK_entry {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {c d : Fin n}
    (h : ε c ≠ ε d) : Y c d = 0 := by
  have h1 := congrFun (congrFun hY.2 c) d
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h h1
  · linear_combination h1 / 2
  · linear_combination -h1 / 2

theorem vminus_K : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E abelian₂ u, ∀ k ∈ Kset ε, ∀ c d : Fin n, ¬ d < c → ∑ a, ∑ b, k⁻¹ c a * k b d * ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ = 0 := by
  intro n ε H _ _ _ σ V E abelian₂ u hσ hD hΛ hfd G hG k hk c d hcd
  obtain ⟨hst, -, hfm, hvan⟩ := VminusComp.vminus_comp V n ε E abelian₂ u hD.1 hD.2.1 hΛ hfd
  have hks := Kset_star ε hk
  have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hk.1.1
  obtain ⟨Y, hY, hexp, -⟩ := compact_exponential_surjective n ε _ hks
  have hexp' : NormedSpace.exp (-Y) = k := by
    rw [Matrix.exp_neg, hexp]
    exact Matrix.inv_eq_left_inv hk.1.2
  let ℓ : ℝ → V →ₗ[ℂ] ℂ := fun t =>
    (innerₛₗ ℂ (u : H)) ∘ₗ (σ (NormedSpace.exp ((t : ℂ) • Y))).toLinearMap ∘ₗ V.subtype
  have hℓ : ∀ t (v : V), ℓ t v = ⟪(u : H), σ (NormedSpace.exp ((t : ℂ) • Y)) v⟫_ℂ := fun _ _ => rfl
  let φ : ℝ → Arr V n 1 →ₗ[ℂ] ℂ := fun t =>
    Matrix.entryLinearMap ℂ ℂ c d ∘ₗ LinearMap.mulRight ℂ (NormedSpace.exp ((t : ℂ) • (-Y))) ∘ₗ
      LinearMap.mulLeft ℂ (NormedSpace.exp ((t : ℂ) • Y)) ∘ₗ matOf (ℓ t)
  have hφ : ∀ t G, φ t G = (NormedSpace.exp ((t : ℂ) • Y) * matOf (ℓ t) G *
      NormedSpace.exp ((t : ℂ) • (-Y))) c d := fun _ _ => rfl
  have main := flow_vanish (Vminus ε E abelian₂ u) (∑ c, ∑ d, Y c d • arrE E 1 c d) ?_ φ ?_ ?_ 1 G hG
  · rw [hφ, Complex.ofReal_one, one_smul, one_smul, hexp, hexp', ← hinv] at main
    rw [← main]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    have e1 : matOf (ℓ 1) G a b = ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ := by
      show ℓ 1 (at1 G a b) = _
      rw [hℓ, Complex.ofReal_one, one_smul, hexp]
      have hkU : k ∈ UJset ε := (kFacts n ε).1 k hk
      have hsU : star k ∈ UJset ε := (kFacts n ε).1 _ hks
      have h1 : σ k (σ (star k) (at1 G a b : V)) = (at1 G a b : V) := by
        have := hσ.1.2 k hkU _ hsU
        rw [hk.1.2, hσ.1.1] at this
        exact (congrArg (fun T : H →L[ℂ] H => T (at1 G a b : V)) this).symm
      let I : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k hkU⟩
      have h2 := I.inner_map_map (u : H) (σ (star k) (at1 G a b : V))
      rw [← h2]
      show ⟪σ k (u : H), σ k (σ (star k) (at1 G a b : V))⟫_ℂ = _
      rw [h1]
    rw [e1]
    ring
  · intro x hx
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ (hst a b h x hx)
    · rw [inK_entry hY h, zero_smul]
      exact Submodule.zero_mem _
  · intro t x
    have hM : ∀ a b, HasDerivAt (fun s => matOf (ℓ s) x a b)
        ((Matrix.of fun a b => ℓ t (∑ c, ∑ d, Y c d • E c d (at1 x a b))) a b) t := by
      intro a b
      exact ((innerSL ℂ (u : H)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (deriv_orbit hσ hD hY.1 (at1 x a b) t)
    have h1 := deriv_mul_entry _ _ _ _ t
      (deriv_mul_entry _ _ _ _ t (deriv_exp_entry Y t) hM) (deriv_exp_entry' (-Y) t) c d
    simp only [hφ]
    refine h1.congr_deriv ?_
    rw [matOf_act]
    refine congrFun (congrFun ?_ c) d
    noncomm_ring
  · intro x hx
    rw [hφ]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]
    show ℓ 0 (at1 x c d) = 0
    rw [hℓ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1]
    exact hvan x hx c d hcd

end GlobalTheory.Jet.VminusK
