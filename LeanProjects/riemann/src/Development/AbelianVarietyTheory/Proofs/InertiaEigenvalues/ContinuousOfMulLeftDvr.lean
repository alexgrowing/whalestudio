import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem continuous_of_mul_left_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {a : O} (ha : a ≠ 0) {f : X → O}
    (hf : Continuous fun x => a * f x) : Continuous f := by
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm := hϖ.maximalIdeal_eq
  rw [continuous_iff_continuousAt]
  intro x0
  have h0 : Filter.Tendsto (fun x => f x - f x0) (nhds x0) (nhds 0) := by
    intro s hs
    obtain ⟨n, hn⟩ := hbasis s hs
    have h1 : Continuous fun x => (u : O) * ϖ ^ k * f x - (u : O) * ϖ ^ k * f x0 := hf.sub continuous_const
    have h2 := (h1.isOpen_preimage _ (hopen (k + n))).mem_nhds (x := x0) (by simp)
    rw [Filter.mem_map]
    filter_upwards [h2] with x hx
    apply hn
    simp only [Set.mem_preimage, SetLike.mem_coe, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    rw [← mul_sub, pow_add, mul_assoc, u.isUnit.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)] at hx
    exact hx
  have := h0.add_const (f x0)
  simpa [ContinuousAt] using this

theorem continuous_of_coeff_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {n : ℕ} {M : X → Matrix (Fin n) (Fin n) O} (hM : Continuous M)
    (L : (Fin n → FractionRing O) →ₗ[FractionRing O] FractionRing O) (v : Fin n → FractionRing O) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) = L (((M x).map (algebraMap O (FractionRing O))).mulVec v)) :
    Continuous f := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin n × Fin n => L (Pi.single p.1 1) * v p.2)
  choose d hd using hb
  refine continuous_of_mul_left_dvr hO (nonZeroDivisors.coe_ne_zero b) ?_
  have : (fun x => (b : O) * f x) = fun x => ∑ p, ∑ q, d (p, q) * M x p q := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, hf, LinearMap.pi_apply_eq_sum_univ L]
    simp only [map_sum, map_mul, hd, Finset.mul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
      Finset.sum_mul, Algebra.smul_def]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have : (fun j => if p = j then (1 : FractionRing O) else 0) = Pi.single p 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  rw [this]
  fun_prop

theorem mapM_twistM_mulVec {O S Γ : Type} [CommRing O] [CommRing S] [Group Γ] {k : ℕ} (f : O →+* S)
    (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) (v : Fin k → S) :
    (mapM f (twistM M χ) g).mulVec v = f (χ g : O) • (mapM f M g).mulVec v := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext p q
  simp [mapM, twistM]

theorem subTw_blocks : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r → ∀ (π : D.nd.X i) (e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i))), (∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) = ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1, fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)) → ∀ Xs : Set (D.nd.X i), π ∈ Xs → SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c) := by
  intro D i r ρ hr π e he Xs hπ
  have hO := D.nd.O_adic i
  have hrc : Continuous fun g => rO D.nd i r π g := (hr π).1
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) := fun c => D.nd.chi_cont i c
  have hχi : Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have := (hχ 1).comp (continuous_inv (G := GE D.nd))
    refine this.congr fun g => ?_
    simp
  have hρc : Continuous fun g => rhoO D.nd i ρ π g := by
    refine continuous_matrix fun p q => ?_
    refine continuous_of_coeff_dvr hO hrc
      ((LinearMap.proj p).comp ((LinearMap.fst _ _ _).comp e.toLinearMap)) (e.symm (Pi.single q 1, 0)) fun g => ?_
    have := congrArg (fun z => z.1 p) (he g (e.symm (Pi.single q 1, 0)))
    simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at this
    exact this.symm
  refine ⟨⟨hχi.smul hρc, π, hπ, e.symm.toLinearMap.comp (LinearMap.inl _ _ _),
    e.symm.injective.comp LinearMap.inl_injective, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [WpO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul]
    congr 1
    apply e.injective
    rw [he]
    simp
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let c' : Fin D.R.t := ⟨c - 1, by omega⟩
    have hcc : (c' : ℕ) + 1 = c := by simp only [c']; omega
    refine ⟨?_, π, hπ, e.symm.toLinearMap.comp ((LinearMap.inr _ _ _).comp
      ((LinearMap.single _ (fun _ => KK D.nd i) c').comp (LinearMap.proj 0))), ?_, fun g v => ?_⟩
    · have : Continuous fun g => (((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) *
          (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) :=
        ((hχ c).mul hχi).smul continuous_const
      exact this
    · intro v w h
      have h1 := congrArg (fun z => (e z).2 c') h
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h1
    · rw [chiRatO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul, MonoidHom.mul_apply, Units.val_mul,
        map_mul, mul_comm, mul_smul]
      congr 1
      apply e.injective
      rw [he, map_smul]
      ext j
      · simp
      · by_cases hj : j = c'
        · subst hj
          simp [hcc, mapM, Algebra.smul_def]
        · simp [hj]

end GlobalTheory.Pass
