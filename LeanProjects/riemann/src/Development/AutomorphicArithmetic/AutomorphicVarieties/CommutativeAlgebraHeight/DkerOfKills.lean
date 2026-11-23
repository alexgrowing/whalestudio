import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem dker_poly_eq (S : Type) [CommRing S] [Algebra A S] (p q : S[X] ⊗[A] E)
    (H : ∀ (T : Type) [CommRing T] [Algebra A T] (f : S[X] →ₐ[A] T), IsNilpotent (f X) →
      D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) p) =
        D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) q)) :
    D.D S[X] p = D.D S[X] q := by
  ext k
  have h := H _ (Ideal.Quotient.mkₐ A (Ideal.span {(X : S[X]) ^ (k + 1)})) ⟨k + 1, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  rw [D.nat, D.nat] at h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h3 := X_pow_dvd_iff.1 h2 k (Nat.lt_succ_self k)
  rwa [coeff_sub, sub_eq_zero] at h3

private theorem dker_unit (T : Type) [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) (w : T ⊗[A] E) :
    IsUnit (1 + (t ⊗ₜ[A] (1 : E)) * w) := by
  apply IsNilpotent.isUnit_one_add
  obtain ⟨k, hk⟩ := ht
  have : (t ⊗ₜ[A] (1 : E)) * w = t • w := by rw [Algebra.smul_def]; rfl
  exact ⟨k, by rw [this, _root_.smul_pow, hk, zero_smul]⟩

private theorem dker_cancel (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    Det.cancel A E S S[X] (1 + X ⊗ₜ w) = 1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w := by
  rw [map_add, map_one]
  congr 1

private theorem dker_top (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    (D.D S[X] (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w)).coeff n = D.D S w := by
  obtain ⟨h1, h2, -⟩ := d_bc D S
  obtain ⟨-, -, h3, h4, -⟩ := d_chi (D.baseChange S) w
  rw [← dker_cancel, ← h1, h3, ← h2, ← h4, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

private theorem dker_of_kills {x : E} (hx : D.Kills x) : x ∈ D.ker := by
  rw [Det.mem_ker]
  intro S _ _ y u v
  rw [← dker_top, ← dker_top D S y]
  congr 1
  apply dker_poly_eq
  intro T _ _ f hf
  simp only [map_add, map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y) = y'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) u) = u'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) v) = v'
  obtain ⟨c, hc⟩ := dker_unit T (f X) hf y'
  have e : 1 + (f X ⊗ₜ[A] (1 : E)) * (y' + u' * (1 ⊗ₜ x) * v') =
      (c : T ⊗[A] E) * (1 + ((↑c⁻¹ : T ⊗[A] E) * (f X ⊗ₜ[A] (1 : E)) * u' * (1 ⊗ₜ x)) * v') := by
    rw [mul_add, mul_add, ← add_assoc, ← hc]
    simp only [← mul_assoc, Units.mul_inv, one_mul, mul_one]
  rw [e, map_mul, d_comm, ← mul_assoc, hx, mul_one, hc]

private theorem dker_kills_of {x : E}
    (hx : ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) :
    D.Kills x := by
  intro S _ _ h
  have key : D.D S[X] (1 + (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) * (1 ⊗ₜ x)) =
      D.D S[X] 1 := by
    apply dker_poly_eq
    intro T _ _ f hf
    simp only [map_add, map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h'
    obtain ⟨c, hc⟩ := dker_unit T (f X) hf h'
    have e : 1 + (c : T ⊗[A] E) * (1 ⊗ₜ x) = (c : T ⊗[A] E) * ((↑c⁻¹ : T ⊗[A] E) + 1 ⊗ₜ x) := by
      rw [mul_add, Units.mul_inv]
    rw [← hc, e, map_mul, hx, ← map_mul, Units.mul_inv, map_one]
  let ev : S[X] →ₐ[A] S := (Polynomial.aeval (R := S) (1 : S)).restrictScalars A
  have hev : Algebra.TensorProduct.map ev (AlgHom.id A E)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h := by
    clear key
    induction h with
    | zero => simp
    | tmul b z => simp [ev]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hX : ev X = 1 := by simp [ev]
  have k2 := congrArg ev key
  rw [← D.nat, map_one, map_one] at k2
  simp only [map_add, map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hev, hX] at k2
  rw [← Algebra.TensorProduct.one_def, one_mul, add_mul, one_mul, add_comm (_ ⊗ₜ x), ← add_assoc, hx] at k2
  exact k2

end

theorem UpperTheory.V.CA.d_ker :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), (x ∈ D.ker ↔ D.Kills x) ∧ (x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) ∧ (x ∈ D.ker → ∀ h i, 1 ≤ i → i ≤ n → D.lam i (h * x) = 0) := by
  intro n A E _ _ _ D x
  refine ⟨⟨fun hx S _ _ h => ?_, dker_of_kills D⟩,
    ⟨fun hx S _ _ s y => ?_, fun hx => dker_of_kills D (dker_kills_of D hx)⟩, fun hx h i h1 hi => ?_⟩
  · simpa using D.mem_ker.1 hx S 1 h 1
  · simpa using D.mem_ker.1 hx S y (s ⊗ₜ 1) 1
  · obtain ⟨-, -, h3, -⟩ := d_chi D (h * x)
    have h4 : D.D A[X] (1 + X ⊗ₜ (h * x)) = 1 := by
      simpa using D.mem_ker.1 hx A[X] 1 (X ⊗ₜ h) 1
    have h5 := congrArg (fun p => p.coeff i) (h3.symm.trans h4)
    simp only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_one] at h5
    simpa [Nat.lt_succ_of_le hi, show i ≠ 0 by omega] using h5
