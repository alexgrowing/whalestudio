import Formalism.DoubleCosetMeasures.Statement

set_option maxHeartbeats 400000

noncomputable section

open Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

section SlopeTestRemainingChoices

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

def liftR (M : Matrix (Fin n) (Fin n) K) (hM : IsInt R M) : Matrix (Fin n) (Fin n) R :=
  fun i j => ⟨M i j, hM i j⟩

theorem liftR_map (M : Matrix (Fin n) (Fin n) K) (hM : IsInt R M) :
    (liftR R M hM).map R.subtype = M := by
  ext i j
  rfl

theorem coeLin_apply (v : Fin n → R) (j : Fin n) : coeLin R v j = (v j : K) := by
  rfl

theorem coeLin_injective : Function.Injective (coeLin R : (Fin n → R) →ₗ[R] (Fin n → K)) := by
  intro v w h
  funext j
  have hj := congrFun h j
  rw [coeLin_apply, coeLin_apply] at hj
  exact Subtype.ext hj

theorem coeLin_mulVec (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    coeLin R (M *ᵥ v) = M.map R.subtype *ᵥ coeLin R v := by
  funext i
  simp [Matrix.mulVec, dotProduct, coeLin_apply]

theorem mem_latZ (Z : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    x ∈ latZ R Z ↔ ∃ y, Z *ᵥ coeLin R y = coeLin R x := by
  exact Iff.rfl

theorem det_lift_eq_one (M : Matrix (Fin n) (Fin n) R) (h : (M.map R.subtype).det = 1) :
    M.det = 1 := by
  have h2 : R.subtype M.det = R.subtype 1 := by
    rw [RingHom.map_det, map_one]
    exact h
  exact Subtype.ext h2

theorem lowUni_mulVec_eLast {M : Matrix (Fin n) (Fin n) K} (h : IsLowUni M) :
    M *ᵥ coeLin R (eLast R) = coeLin R (eLast R) := by
  have hw : ∀ j : Fin n, coeLin R (eLast R) j = if j.val + 1 = n then 1 else 0 := by
    intro j
    rw [coeLin_apply]
    unfold eLast
    split_ifs <;> simp
  funext i
  rw [hw i]
  simp only [Matrix.mulVec, dotProduct, hw, mul_ite, mul_one, mul_zero]
  by_cases hi : i.val + 1 = n
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [if_pos hi, h.2 i]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Fin.ext (by omega))
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · have hij : i < j := Fin.lt_def.mpr (by have := i.isLt; omega)
      exact h.1 hij
    · rfl

theorem lastCoord_apply (w : Fin n → K) :
    lastCoord R w = ∑ j : Fin n, if j.val + 1 = n then w j else 0 := by
  unfold lastCoord
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> rfl

theorem lastCoord_upUni {M : Matrix (Fin n) (Fin n) K} (h : IsUpUni M) (w : Fin n → K) :
    lastCoord R (M *ᵥ w) = lastCoord R w := by
  rw [lastCoord_apply, lastCoord_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with hj
  · simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j]
    · rw [h.2 j, one_mul]
    · intro k _ hk
      have hne : k.val ≠ j.val := fun e => hk (Fin.ext e)
      have hkj : k < j := Fin.lt_def.mpr (by have := k.isLt; omega)
      rw [h.1 hkj, zero_mul]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'
  · rfl

theorem lamLin_apply (Z : Matrix (Fin n) (Fin n) K) (v : Fin n → R) :
    lamLin R Z v = Submodule.mkQ _ (lastCoord R (Z⁻¹ *ᵥ coeLin R v)) := rfl

end SlopeTestRemainingChoices

section Inv

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

def eqvA (A : Matrix (Fin n) (Fin n) R) (hA : (A.map R.subtype).det = 1) :
    (Fin n → R) ≃ₗ[R] (Fin n → R) :=
  LinearEquiv.ofLinear A.mulVecLin A⁻¹.mulVecLin
    (by
      apply LinearMap.ext; intro v
      simp [mulVec_mulVec, Matrix.mul_nonsing_inv A (by simp [det_lift_eq_one R A hA])])
    (by
      apply LinearMap.ext; intro v
      simp [mulVec_mulVec, Matrix.nonsing_inv_mul A (by simp [det_lift_eq_one R A hA])])

theorem map_latZ (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) :
    (latZ R Z).map (eqvA R A hA : (Fin n → R) →ₗ[R] (Fin n → R)) =
      latZ R (A.map R.subtype * Z * B.map R.subtype) := by
  have hAd := det_lift_eq_one R A hA
  have hBd := det_lift_eq_one R B hB
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hAd]; exact isUnit_one)
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hAd]; exact isUnit_one)
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (by rw [hBd]; exact isUnit_one)
  have hAm' : (A⁻¹).map R.subtype * A.map R.subtype = 1 := by
    rw [← Matrix.map_mul, hAA']
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBm : B.map R.subtype * (B⁻¹).map R.subtype = 1 := by
    rw [← Matrix.map_mul, hBB]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy'⟩ := (mem_latZ R Z y).1 hy
    refine (mem_latZ R _ _).2 ⟨B⁻¹ *ᵥ y', ?_⟩
    show _ = coeLin R (A *ᵥ y)
    rw [coeLin_mulVec, coeLin_mulVec, ← hy', Matrix.mulVec_mulVec, Matrix.mul_assoc, hBm,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  · intro hx
    obtain ⟨y', hy'⟩ := (mem_latZ R _ x).1 hx
    refine ⟨A⁻¹ *ᵥ x, (mem_latZ R Z _).2 ⟨B *ᵥ y', ?_⟩, ?_⟩
    · rw [coeLin_mulVec, coeLin_mulVec, ← hy', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAm', Matrix.one_mul]
    · show A *ᵥ (A⁻¹ *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]

def cokEquiv (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) :
    coker R Z ≃ₗ[R] coker R (A.map R.subtype * Z * B.map R.subtype) :=
  Submodule.Quotient.equiv _ _ (eqvA R A hA) (map_latZ R A B Z hA hB)

theorem cokEquiv_mk (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) (v : Fin n → R) :
    cokEquiv R A B Z hA hB (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A *ᵥ v) := rfl

theorem cokEquiv_eZ (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1)
    (hlow : IsLowUni (A.map R.subtype)) :
    cokEquiv R A B Z hA hB (eZ R Z) = eZ R (A.map R.subtype * Z * B.map R.subtype) := by
  show cokEquiv R A B Z hA hB (Submodule.Quotient.mk (eLast R)) = Submodule.Quotient.mk (eLast R)
  rw [cokEquiv_mk]
  exact congrArg Submodule.Quotient.mk
    (coeLin_injective R (by rw [coeLin_mulVec]; exact lowUni_mulVec_eLast R hlow))

theorem lamLin_mul (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hup : IsUpUni (B.map R.subtype)) (v : Fin n → R) :
    lamLin R (A.map R.subtype * Z * B.map R.subtype) (A *ᵥ v) = lamLin R Z v := by
  have hAinv : (A.map R.subtype)⁻¹ * A.map R.subtype = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [hA]; exact isUnit_one)
  have hBd : (B.map R.subtype).det = 1 := by
    rw [Matrix.det_of_upperTriangular hup.1]
    exact Finset.prod_eq_one (fun i _ => hup.2 i)
  have hBinv : B.map R.subtype * (B.map R.subtype)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hBd]; exact isUnit_one)
  have hlast : ∀ w : Fin n → K, lastCoord R ((B.map R.subtype)⁻¹ *ᵥ w) = lastCoord R w := by
    intro w
    rw [← lastCoord_upUni R hup ((B.map R.subtype)⁻¹ *ᵥ w), Matrix.mulVec_mulVec, hBinv,
      Matrix.one_mulVec]
  rw [lamLin_apply, lamLin_apply, coeLin_mulVec, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAinv, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hlast]

end Inv

theorem isoInv : IsoInv := by
  intro K _ R n a b Z ha hb hai hbi C _ _ e lam
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin n) (Fin n) R, A.map R.subtype = a :=
    ⟨liftR R a hai, liftR_map R a hai⟩
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin n) (Fin n) R, B.map R.subtype = b :=
    ⟨liftR R b hbi, liftR_map R b hbi⟩
  have hA : (A.map R.subtype).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ha.1]
    exact Finset.prod_eq_one (fun i _ => ha.2 i)
  have hB : (B.map R.subtype).det = 1 := by
    rw [Matrix.det_of_upperTriangular hb.1]
    exact Finset.prod_eq_one (fun i _ => hb.2 i)
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (by rw [det_lift_eq_one R A hA]; exact isUnit_one)
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun φ => (cokEquiv R A B Z hA hB).trans φ
      invFun := fun ψ => (cokEquiv R A B Z hA hB).symm.trans ψ
      left_inv := fun φ => by
        ext x
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      right_inv := fun ψ => by
        ext x
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] } ?_)
  intro φ
  simp only [isoSet, Set.mem_setOf_eq, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun v => ?_⟩
    · show φ (cokEquiv R A B Z hA hB (eZ R Z)) = e
      rw [cokEquiv_eZ R A B Z hA hB ha]
      exact h1
    · show lam (φ (cokEquiv R A B Z hA hB (Submodule.Quotient.mk v))) = lamLin R Z v
      rw [cokEquiv_mk, h2, lamLin_mul R A B Z hA hb]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun v => ?_⟩
    · rw [← cokEquiv_eZ R A B Z hA hB ha]
      exact h1
    · have h3 := h2 (A⁻¹ *ᵥ v)
      change lam (φ (cokEquiv R A B Z hA hB (Submodule.Quotient.mk (A⁻¹ *ᵥ v)))) = _ at h3
      rw [cokEquiv_mk, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h3
      rw [h3, ← lamLin_mul R A B Z hA hb (A⁻¹ *ᵥ v), Matrix.mulVec_mulVec, hAA,
        Matrix.one_mulVec]

theorem isoFinite : IsoFinite := by
  intro K _ R hfin n Z hZ hdet
  obtain ⟨Zr, rfl⟩ : ∃ Zr : Matrix (Fin n) (Fin n) R, Zr.map R.subtype = Z :=
    ⟨liftR R Z hZ, liftR_map R Z hZ⟩
  have hd : ((Zr.det : R) : K) = (Zr.map R.subtype).det := RingHom.map_det R.subtype Zr
  haveI : Finite (R ⧸ Ideal.span {Zr.det}) := hfin Zr.det (by rw [hd]; exact hdet)
  have hmem : ∀ x : Fin n → R, Zr.det • x ∈ latZ R (Zr.map R.subtype) := by
    intro x
    refine (mem_latZ R _ _).2 ⟨Zr.adjugate *ᵥ x, ?_⟩
    rw [coeLin_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_adjugate,
      ← coeLin_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hs := Ideal.Quotient.mk_surjective (I := Ideal.span {Zr.det})
  have hcok : Finite (coker R (Zr.map R.subtype)) := by
    let g : (Fin n → R ⧸ Ideal.span {Zr.det}) → coker R (Zr.map R.subtype) :=
      fun w => Submodule.Quotient.mk (fun j => Function.surjInv hs (w j))
    have hg : Function.Surjective g := by
      intro q
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      refine ⟨fun j => Ideal.Quotient.mk _ (x j), ?_⟩
      have hc : ∀ j, ∃ c : R,
          Function.surjInv hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j)) - x j
            = Zr.det * c := by
        intro j
        have h1 := Function.surjInv_eq hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j))
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
        exact h1
      choose c hc using hc
      show Submodule.Quotient.mk _ = Submodule.Quotient.mk x
      rw [Submodule.Quotient.eq]
      have hsub : (fun j => Function.surjInv hs (Ideal.Quotient.mk (Ideal.span {Zr.det}) (x j)))
          - x = Zr.det • c := by
        funext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact hc j
      rw [hsub]
      exact hmem c
    exact Finite.of_surjective g hg
  refine ⟨hcok, fun C _ _ e lam => ?_⟩
  by_cases hne : (isoSet R (Zr.map R.subtype) C e lam).Nonempty
  · obtain ⟨φ₀, -⟩ := hne
    haveI := hcok
    haveI : Finite C := Finite.of_surjective φ₀ φ₀.surjective
    haveI : Finite (coker R (Zr.map R.subtype) ≃ₗ[R] C) :=
      Finite.of_injective (fun φ : coker R (Zr.map R.subtype) ≃ₗ[R] C =>
        (φ : coker R (Zr.map R.subtype) → C)) (fun φ ψ h => LinearEquiv.ext (congrFun h))
    exact Set.toFinite _
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact Set.finite_empty

end Formalism.DoubleCosetMeasures.P
