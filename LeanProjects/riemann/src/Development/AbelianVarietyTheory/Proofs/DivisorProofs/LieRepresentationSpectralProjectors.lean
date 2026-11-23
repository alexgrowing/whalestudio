import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised

open NumberField Polynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieProj

theorem aeval_mul_of_mul_eq {g : ℕ} {T P : Matrix (Fin g) (Fin g) ℂ} {r : ℂ} (h : T * P = r • P) (q : ℂ[X]) :
    aeval T q * P = q.eval r • P := by
  have hp : ∀ k : ℕ, T ^ k * P = r ^ k • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', mul_assoc, ih, mul_smul_comm, h, smul_smul, pow_succ, mul_comm (r ^ k)]
  induction q using Polynomial.induction_on' with
  | add p q hp' hq' => rw [map_add, add_mul, hp', hq', eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, hp,
      smul_smul]

theorem X_sub_C_mul_basis {s : Finset ℂ} {r : ℂ} (hr : r ∈ s) :
    (X - C r) * Lagrange.basis s id r = C (Lagrange.nodalWeight s id r) * Lagrange.nodal s id := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hr, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero r) (Lagrange.X_sub_C_dvd_nodal id hr)

theorem spectral (K : Type) [Field K] [NumberField K] (g : ℕ) (Φ : K →+* Matrix (Fin g) (Fin g) ℂ) :
    ∃ E : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ τ, E τ * E τ = E τ) ∧ ∑ τ, E τ = 1 ∧
      (∀ τ x, Φ x * E τ = τ x • E τ) ∧ (∀ τ x, E τ * Φ x = τ x • E τ) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ K
  let θ := pb.gen
  let T := Φ θ
  let f : ℂ[X] := (minpoly ℚ θ).map (algebraMap ℚ ℂ)
  let S : Finset ℂ := f.roots.toFinset
  have hfmon : f.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _
  have hnod : f.roots.Nodup := nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ θ))
  have hnodal : Lagrange.nodal S id = f := by
    rw [Lagrange.nodal]
    conv_rhs => rw [(IsAlgClosed.splits f).eq_prod_roots_of_monic hfmon]
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnod.dedup]
    rfl
  have hfT : aeval T f = 0 := by
    rw [aeval_map_algebraMap, show T = Φ.toRatAlgHom θ from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hroot : ∀ r : ℂ, r ∈ S ↔ aeval r (minpoly ℚ θ) = 0 := by
    intro r
    rw [Multiset.mem_toFinset, mem_roots hfmon.ne_zero, IsRoot.def, eval_map_algebraMap]
  have hmemS : ∀ τ : K →+* ℂ, τ θ ∈ S := by
    intro τ
    rw [hroot, show τ θ = τ.toRatAlgHom θ from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have himage : Finset.univ.image (fun τ : K →+* ℂ => τ θ) = S := by
    ext r
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp h
      exact hmemS τ
    · have h' := (hroot r).mp h
      exact Finset.mem_image.mpr ⟨(pb.lift r h').toRingHom, Finset.mem_univ _, pb.lift_gen r h'⟩
  have hinjθ : ∀ τ τ' : K →+* ℂ, τ θ = τ' θ → τ = τ' := by
    intro τ τ' h
    have := pb.algHom_ext (f := τ.toRatAlgHom) (g := τ'.toRatAlgHom) h
    ext x
    exact DFunLike.congr_fun this x
  have hpoly : ∀ x : K, ∃ q : ℂ[X], Φ x = aeval T q ∧ ∀ τ : K →+* ℂ, τ x = q.eval (τ θ) := by
    intro x
    obtain ⟨h, -, hh⟩ := pb.exists_eq_aeval x
    refine ⟨h.map (algebraMap ℚ ℂ), ?_, fun τ => ?_⟩
    · rw [aeval_map_algebraMap, hh, show T = Φ.toRatAlgHom θ from rfl, aeval_algHom_apply]
      rfl
    · rw [eval_map_algebraMap, hh, show τ θ = τ.toRatAlgHom θ from rfl, aeval_algHom_apply]
      rfl
  let P : ℂ → Matrix (Fin g) (Fin g) ℂ := fun r => aeval T (Lagrange.basis S id r)
  have heig : ∀ r ∈ S, T * P r = r • P r := by
    intro r hr
    have h := congrArg (aeval T) (X_sub_C_mul_basis hr)
    simp only [map_mul, map_sub, aeval_X, aeval_C, hnodal, hfT, mul_zero] at h
    rw [sub_mul, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
    exact h
  have hinjS : Set.InjOn (id : ℂ → ℂ) S := fun _ _ _ _ h => h
  refine ⟨fun τ => P (τ θ), fun τ => ?_, ?_, fun τ x => ?_, fun τ x => ?_⟩
  · show aeval T (Lagrange.basis S id (τ θ)) * P (τ θ) = P (τ θ)
    rw [aeval_mul_of_mul_eq (heig _ (hmemS τ))]
    have := Lagrange.eval_basis_self (v := id) hinjS (hmemS τ)
    simp only [id] at this
    rw [this, one_smul]
  · have hne : S.Nonempty := ⟨_, hmemS (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
    rw [← Finset.sum_image (f := P) (fun τ _ τ' _ h => hinjθ τ τ' h), himage]
    show ∑ r ∈ S, aeval T (Lagrange.basis S id r) = 1
    rw [← map_sum, Lagrange.sum_basis hinjS hne, map_one]
  · obtain ⟨q, hq, hτq⟩ := hpoly x
    rw [hq, aeval_mul_of_mul_eq (heig _ (hmemS τ)), hτq]
  · obtain ⟨q, hq, hτq⟩ := hpoly x
    show aeval T (Lagrange.basis S id (τ θ)) * Φ x = _
    rw [hq, ← map_mul, mul_comm, map_mul, aeval_mul_of_mul_eq (heig _ (hmemS τ)), hτq]

end GlobalTheory.UPel.HT.LieProj

namespace GlobalTheory.UPel.HT.LieProj

theorem exists_mul_eq_nat {K : Type} [Field K] [NumberField K] {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ (y : 𝓞 K) (N : ℕ), N ≠ 0 ∧ x * y = N := by
  have hI : Ideal.span {x} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {x}))
  exact ⟨y, _, fun h => hI (Ideal.absNorm_eq_zero_iff.mp h), by rw [mul_comm, hy]⟩

theorem extend {K : Type} [Field K] [NumberField K] {g : ℕ} (ψ : 𝓞 K →+* Matrix (Fin g) (Fin g) ℂ) :
    ∃ Φ : K →+* Matrix (Fin g) (Fin g) ℂ, ∀ c : 𝓞 K, Φ (c : K) = ψ c := by
  have hcomm : ∀ a ∈ Set.range ψ, ∀ b ∈ Set.range ψ, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, mul_comm, map_mul]
  letI : CommRing (Algebra.adjoin ℚ (Set.range ψ)) := Algebra.adjoinCommRingOfComm ℚ hcomm
  let ψ' : 𝓞 K →+* Algebra.adjoin ℚ (Set.range ψ) :=
    ψ.codRestrict (Algebra.adjoin ℚ (Set.range ψ)) fun x => Algebra.subset_adjoin ⟨x, rfl⟩
  have hu : ∀ y : nonZeroDivisors (𝓞 K), IsUnit (ψ' y) := by
    intro y
    obtain ⟨y', N, hN, hy⟩ := exists_mul_eq_nat (nonZeroDivisors.coe_ne_zero y)
    refine IsUnit.of_mul_eq_one (ψ' y' * algebraMap ℚ _ (N : ℚ)⁻¹) ?_
    rw [← mul_assoc, ← map_mul, hy, map_natCast, ← map_natCast (algebraMap ℚ (Algebra.adjoin ℚ (Set.range ψ))),
      ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hN), map_one]
  refine ⟨(Algebra.adjoin ℚ (Set.range ψ)).val.toRingHom.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 K)) (S := K) hu), fun c => ?_⟩
  have := IsLocalization.lift_eq (M := nonZeroDivisors (𝓞 K)) (S := K) hu c
  simp only [RingHom.comp_apply]
  erw [this]
  rfl

theorem idem_eq_zero {g : ℕ} {P : Matrix (Fin g) (Fin g) ℂ} (h : P * P = P) (ht : P.trace = 0) : P = 0 := by
  have hPid : IsIdempotentElem (Matrix.toLinAlgEquiv' P) := (show IsIdempotentElem P from h).map _
  have hPtr : LinearMap.trace ℂ (Fin g → ℂ) (Matrix.toLinAlgEquiv' P) = 0 := by
    show LinearMap.trace ℂ (Fin g → ℂ) (Matrix.toLin' P) = 0
    rw [Matrix.trace_toLin'_eq, ht]
  have := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (e := Matrix.toLinAlgEquiv' P) hPid hPtr
  exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).injective).mp this

end GlobalTheory.UPel.HT.LieProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.LieProj

theorem lie_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  intro p _ D R _ b σ ρ hT
  classical
  obtain ⟨Φ, hΦ⟩ := extend (ρ.comp (algebraMap (𝓞 D.F) D.O))
  obtain ⟨E, hidem, hsum, hl, hr⟩ := spectral D.F D.g Φ
  have hΦ' : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Φ (c : D.F) := fun c => (hΦ c).symm
  set lam : ℂ := σ b.ρ with hlam
  have hinj : ∀ i, Function.Injective (σ.comp (b.t i)) := by
    intro i
    refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    by_contra h0
    obtain ⟨y, N, hN, hy⟩ := exists_mul_eq_nat h0
    have := congrArg (σ.comp (b.t i)) hy
    rw [map_mul, hx, zero_mul, map_natCast] at this
    exact hN (by exact_mod_cast this.symm)
  let τ : Fin D.a → (D.F →+* ℂ) := fun i => IsFractionRing.lift (hinj i)
  have hτ : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c =>
    IsFractionRing.lift_algebraMap (hinj i) c
  have hτinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub]
      rw [← hτ, ← hτ, hij, sub_self]
    have h1 : (1 : R) ∈ RingHom.ker σ := hle (by rw [b.comax i j hne]; exact Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have hroot : lam ^ 2 - D.tr * lam + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hnreal : (starRingEnd ℂ) lam ≠ lam := by
    intro h
    have hr := Complex.conj_eq_iff_re.mp h
    rw [← hr] at hroot
    have h2 : (lam.re) ^ 2 - D.tr * lam.re + D.nm = 0 := by exact_mod_cast hroot
    have h3 : ((D.tr : ℝ)) ^ 2 - 4 * D.nm < 0 := by exact_mod_cast D.disc_neg
    nlinarith [sq_nonneg (2 * lam.re - D.tr)]
  have hω : ∀ τ' : D.F →+* ℂ, (τ' (D.ω : D.F)) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have h0 : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have := congrArg (τ'.comp (algebraMap (𝓞 D.F) D.F)) h0
    simp only [map_sub, map_add, map_mul, map_pow, map_intCast, map_zero] at this
    exact this
  have hτω : ∀ i, τ i (D.ω : D.F) = lam := fun i => by rw [hτ, b.t_ω]
  have hexp : ∀ x : D.F, Φ x = ∑ τ', τ' x • E τ' := by
    intro x
    rw [← mul_one (Φ x), ← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ' _ => hl τ' x
  set I := Finset.univ.image τ with hIdef
  set J := Finset.univ.image (fun i => (starRingEnd ℂ).comp (τ i)) with hJdef
  have hJinj : Function.Injective fun i => (starRingEnd ℂ).comp (τ i) := by
    intro i j h
    apply hτinj
    ext x
    have := congrArg (fun f : D.F →+* ℂ => (starRingEnd ℂ) (f x)) h
    simpa using this
  have hnJ : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = lam → τ' ∉ J := by
    intro τ' hω' hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have := congrArg (fun f : D.F →+* ℂ => f (D.ω : D.F)) hj
    simp only [RingHom.comp_apply, hτω, hω'] at this
    exact hnreal this
  let coef : (D.F →+* ℂ) → ℂ := fun τ' => (D.m : ℂ) * ((if τ' ∈ I then 1 else 0) +
    (if τ' (D.ω : D.F) = lam then 0 else (D.n : ℂ)) - (if τ' ∈ J then 1 else 0))
  have hdiff : ∀ c : 𝓞 D.F, ∑ τ', ((E τ').trace - coef τ') * τ' (c : D.F) = 0 := by
    intro c
    have h1 := hT c
    have hI : ∑ i, σ (b.t i c) = ∑ τ', (if τ' ∈ I then τ' (c : D.F) else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hτinj h)]
      exact Finset.sum_congr rfl fun i _ => (hτ i c).symm
    have hJ : ∑ i, (starRingEnd ℂ) (σ (b.t i c)) = ∑ τ', (if τ' ∈ J then τ' (c : D.F) else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hJinj h)]
      exact Finset.sum_congr rfl fun i _ => by simp [hτ i c]
    rw [hI, hJ, Finset.sum_filter, hΦ', hexp, Matrix.trace_sum] at h1
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← sub_eq_zero,
      ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    simp only [coef, Matrix.trace_smul, smul_eq_mul]
    split_ifs <;> first | ring1 | (exfalso; tauto)
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp
    (fun τ' : D.F →+* ℂ => ((τ'.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom : 𝓞 D.F →* ℂ)) (by
      intro a a' h
      apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
      ext x
      exact DFunLike.congr_fun h x)
  have hcoef : ∀ τ', (E τ').trace - coef τ' = 0 := by
    refine Fintype.linearIndependent_iff.mp hlin _ ?_
    funext c
    rw [Finset.sum_apply]
    simpa using hdiff c
  have hmτ : ∀ i, (E (τ i)).trace = D.m := by
    intro i
    have h := hcoef (τ i)
    have h1 : τ i ∈ I := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    simp only [coef, h1, hτω i, hnJ (τ i) (hτω i), if_true, if_false] at h
    linear_combination h
  have hzero : ∀ τ', τ' ∉ I → τ' (D.ω : D.F) = lam → E τ' = 0 := by
    intro τ' hI' hω'
    refine idem_eq_zero (hidem τ') ?_
    have h := hcoef τ'
    simp only [coef, hI', hω', hnJ τ' hω', if_true, if_false] at h
    linear_combination h
  refine ⟨fun i => E (τ i), fun i => hidem _, hmτ, fun i c => ?_, fun i c => ?_, ?_⟩
  · rw [hΦ', hl, hτ]
  · rw [hΦ', hr, hτ]
  · have hL : ∑ i, E (τ i) = ∑ τ', (if τ' ∈ I then E τ' else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (fun i _ j _ h => hτinj h)]
    have h1 : ((D.tr : ℂ) - lam) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) = ∑ τ', ((D.tr : ℂ) - lam) • E τ' := by
      rw [← hsum, Finset.smul_sum]
    rw [hL, h1, hΦ', hexp, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    by_cases hI' : τ' ∈ I
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI'
      rw [if_pos hI', ← sub_smul, hτω i]
      congr 1
      ring
    · rw [if_neg hI', smul_zero]
      by_cases hω' : τ' (D.ω : D.F) = lam
      · rw [hzero τ' hI' hω', smul_zero, smul_zero, sub_zero]
      · have hq : (τ' (D.ω : D.F) - lam) * (τ' (D.ω : D.F) - ((D.tr : ℂ) - lam)) = 0 := by
          linear_combination hω τ' - hroot
        have h2 := sub_eq_zero.mp ((mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr hω'))
        rw [← sub_smul, h2, sub_self, zero_smul]

end GlobalTheory.UPel.HT.LieProj

end
