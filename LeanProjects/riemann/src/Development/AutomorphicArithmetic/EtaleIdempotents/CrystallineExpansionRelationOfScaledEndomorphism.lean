import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

private theorem core {F R C : Type} {V : Type*} [Field F] [AddCommGroup V] [Module F V] [CommRing R] [CommRing C] [Algebra F C]
    (c : R →+* C) (φ : C →ₐ[F] C) (φR : R →+* R) (t : R) (ht : IsUnit (c t)) (hφ : ∀ a, φ (c a) = c (φR a))
    (L : ℕ) (hL : (L : F) ≠ 0) (hφt : φR t = (L : R) * t) (f n N r s κ : ℕ) (hκ : (κ : F) ≠ 0)
    {ι : Type} [Fintype ι] (A : Fin (n + 1) → (V →ₗ[F] V)) (v : ι → V) (d : ι → R)
    (w : Fin (n + 1) → ι → V) (σ : Fin (n + 1) → ℤ)
    (hw : ∀ i k, w i k = (L ^ s : ℕ) • A i (v k))
    (hvec : ∑ q : Fin (n + 1) × ι, w q.1 q.2 ⊗ₜ[F] (c ((κ : R) * (((σ q.1 : ℤ) : R) * (L : R) ^ (f * (q.1 : ℕ) * r) *
      φR^[f * (n - q.1 + N)] (d q.2))) * Ring.inverse (c t) ^ 0) = 0) :
    ∑ i : Fin (n + 1), σ i • TensorProduct.map (A i) (φ.toLinearMap ^ (f * (n - i + N)))
      (∑ k, v k ⊗ₜ[F] (c (d k) * Ring.inverse (c t) ^ r)) = 0 := by
  set τ := Ring.inverse (c t) with hτdef
  have hτ : τ * c t = 1 := Ring.inverse_mul_cancel _ ht
  have hpow : ∀ (m : ℕ) (x : C), (φ.toLinearMap ^ m) x = (⇑φ)^[m] x := by
    intro m x
    rw [Module.End.pow_apply]
    rfl
  have hic : ∀ (m : ℕ) (a : R), (⇑φ)^[m] (c a) = c (φR^[m] a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hφ, ih]
  have hit : ∀ m : ℕ, φR^[m] t = (L : R) ^ m * t := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, hφt, pow_succ]
      ring
  have hτm : ∀ m : ℕ, (⇑φ)^[m] τ * ((L : C) ^ m * c t) = 1 := by
    intro m
    have h2 := congrArg (⇑φ)^[m] hτ
    rw [iterate_map_mul, iterate_map_one, hic, hit, map_mul, map_pow, map_natCast] at h2
    exact h2
  have nat_unit : ∀ a : ℕ, (a : F) ≠ 0 → IsUnit (a : C) := by
    intro a ha
    have := (IsUnit.mk0 _ ha).map (algebraMap F C)
    simpa using this
  set u : C := (κ : C) * (L : C) ^ (s + f * (n + N) * r) * c t ^ r with hu
  have huu : IsUnit u := ((nat_unit κ hκ).mul ((nat_unit L hL).pow _)).mul (ht.pow _)
  obtain ⟨u', hu'⟩ := huu.exists_left_inv
  have hinj : ∀ x : V ⊗[F] C, LinearMap.lTensor V (LinearMap.mulLeft F u) x = 0 → x = 0 := by
    intro x hx
    have hl : ∀ y : V ⊗[F] C, LinearMap.lTensor V (LinearMap.mulLeft F u') (LinearMap.lTensor V (LinearMap.mulLeft F u) y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [← mul_assoc, hu']
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [← hl x, hx, map_zero]
  have hsc : ∀ (i : Fin (n + 1)) (x : R),
      u * (⇑φ)^[f * (n - i + N)] (c x * τ ^ r) =
        (L ^ s : ℕ) • c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] x)) := by
    intro i x
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have hexp : f * (n + N) * r = f * (n - i + N) * r + f * (i : ℕ) * r := by
      have h1 : n + N = (n - i + N) + i := by omega
      rw [h1]
      ring
    rw [iterate_map_mul, iterate_map_pow, hic, nsmul_eq_mul, Nat.cast_pow, map_mul, map_mul, map_natCast, map_pow,
      map_natCast]
    have h := hτm (f * (n - i + N))
    rw [hu, hexp]
    calc _ = (κ : C) * (L : C) ^ s * (L : C) ^ (f * (i : ℕ) * r) * c (φR^[f * (n - i + N)] x) *
          ((⇑φ)^[f * (n - i + N)] τ * ((L : C) ^ (f * (n - i + N)) * c t)) ^ r := by
          rw [mul_pow, mul_pow, pow_add, pow_add, pow_mul]
          ring
      _ = _ := by
          rw [h, one_pow]
          ring
  have hterm : ∀ (i : Fin (n + 1)) (k : ι),
      σ i • (A i (v k) ⊗ₜ[F] (u * (⇑φ)^[f * (n - i + N)] (c (d k) * τ ^ r))) =
        w i k ⊗ₜ[F] (c ((κ : R) * (((σ i : ℤ) : R) * (L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) * τ ^ 0) := by
    intro i k
    have hy : c ((κ : R) * (((σ i : ℤ) : R) * (L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) =
        σ i • c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) := by
      rw [zsmul_eq_mul, ← map_intCast c, ← map_mul]
      congr 1
      ring
    rw [hsc, hw, pow_zero, mul_one, hy]
    generalize c ((κ : R) * ((L : R) ^ (f * (i : ℕ) * r) * φR^[f * (n - i + N)] (d k))) = y
    generalize A i (v k) = a
    have e1 : a ⊗ₜ[F] ((L ^ s : ℕ) • y) = (L ^ s : ℕ) • (a ⊗ₜ[F] y) := map_nsmul (TensorProduct.mk F V C a) _ y
    have e2 : ((L ^ s : ℕ) • a) ⊗ₜ[F] (σ i • y) = (L ^ s : ℕ) • (a ⊗ₜ[F] (σ i • y)) :=
      map_nsmul ((TensorProduct.mk F V C).flip (σ i • y)) _ a
    have e3 : a ⊗ₜ[F] (σ i • y) = σ i • (a ⊗ₜ[F] y) := map_zsmul (TensorProduct.mk F V C a) _ y
    rw [e1, e2, e3, smul_comm]
  apply hinj
  rw [← hvec, Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, hpow, hterm i k]

section
variable {l : ℕ} [Fact l.Prime]
private theorem crisFrobenius_cyclotomicPeriod : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))
end

theorem UpperTheory.crystalline_expansion_relation_of_scaled_endomorphisms :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (B : PB l K) (M : Model l K) (j f n N r s κ : ℕ) (_ : κ ≠ 0)
        {ι : Type} [Fintype ι] (A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j)) (v : ι → M.T j) (c : ι → Acris l)
        (w : Fin (n + 1) → ι → M.T j) (σ : Fin (n + 1) → ℤ)
        (_ : ∀ i k, M.toV j (w i k) = (l ^ s : ℕ) • A i (M.toV j (v k)))
        (_ : vec B M j 0 (fun q : Fin (n + 1) × ι => w q.1 q.2)
          (fun q => (κ : Acris l) * (((σ q.1 : ℤ) : Acris l) * (l : Acris l) ^ (f * (q.1 : ℕ) * r) * (phiA l)^[f * (n - q.1 + N)] (c q.2))) = 0),
        ∑ i : Fin (n + 1), σ i • TensorProduct.map (A i) (B.φ.toLinearMap ^ (f * (n - i + N))) (vec B M j r v c) = 0 := by
  intro l _ K B M j f n N r s κ hκ ι _ A v c w σ hw hv
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hκ' : (κ : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hκ
  simp only [vec] at hv ⊢
  exact core (F := ℚ_[l]) (V := M.V j) B.c B.φ (phiA l) (tA l) B.t_unit B.φ_c l hl crisFrobenius_cyclotomicPeriod f n N r s κ hκ' A
    (fun k => M.toV j (v k)) c (fun i k => M.toV j (w i k)) σ hw hv
