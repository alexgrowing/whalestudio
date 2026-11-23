import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace IncidenceGeneric

theorem hom_aeval {F σ R T : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R] [Algebra F T]
    (Φ : R →+* T) (hΦ : ∀ r : F, Φ (algebraMap F R r) = algebraMap F T r) (y : σ → R)
    (g : MvPolynomial σ F) : Φ (aeval y g) = aeval (fun s => Φ (y s)) g := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  ext r
  exact hΦ r

theorem map_genSubst {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n k : ℕ}
    (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    map φ (genSubst ζ c ij) = genSubst (fun l => φ (ζ l)) (fun l => φ (c l)) ij := by
  simp [genSubst, map_sum]

theorem aeval_genSubst_genSubst {R : Type*} [CommRing R] {n k : ℕ} (ζ c c' : Fin n → R)
    (hc : ∑ l, c l * ζ l = 1) (ij : Fin k × Fin n) :
    aeval (genSubst ζ c) (genSubst ζ c' ij) = genSubst ζ c ij := by
  have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin k × Fin n) R) := by
    rw [← C_1, ← hc, map_sum]
    simp only [C_mul]
  have h0 : ∑ l, genSubst ζ c (ij.1, l) * C (ζ l) = 0 := by
    simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
      sub_self]
  rw [show genSubst ζ c' ij = X ij - (∑ l, X (ij.1, l) * C (ζ l)) * C (c' ij.2) from rfl]
  simp only [map_sub, map_mul, map_sum, aeval_X, aeval_C, algebraMap_eq, h0, zero_mul, sub_zero]

theorem aeval_genSubst_eq_zero_of {F R : Type*} [Field F] [CommRing R] [Algebra F R] {n k : ℕ}
    (ζ c c' : Fin n → R) (hc : ∑ l, c l * ζ l = 1) (g : MvPolynomial (Fin k × Fin n) F)
    (h : aeval (genSubst ζ c') g = 0) : aeval (genSubst ζ c) g = 0 := by
  have := hom_aeval (F := F) (aeval (genSubst ζ c) : MvPolynomial (Fin k × Fin n) R →ₐ[R] _).toRingHom
    (fun r => by simp [MvPolynomial.algebraMap_apply]) (genSubst ζ c') g
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_genSubst_genSubst ζ c c' hc, h,
    map_zero] at this
  exact this.symm

theorem mem_incIdeal_of_aeval_eq_zero {F : Type*} [Field F] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)))
    (g : MvPolynomial (Fin k × Fin n) F) (h : aeval (genSubst (genPt P) c) g = 0) :
    g ∈ incIdeal P k := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  intro v hv
  obtain ⟨x, hx0, hxP, hvx⟩ := hv
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx0
  set a : (MvPolynomial (Fin n) F ⧸ P) := Ideal.Quotient.mk P (X j) with ha_def
  have ha : a ≠ 0 := by
    intro h0
    apply hj
    simpa using hxP _ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hξj : genPt P j ≠ 0 := by
    show algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a ≠ 0
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]

  obtain ⟨c', hc'_def⟩ : ∃ c' : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ P)), c' = Pi.single j (genPt P j)⁻¹ := ⟨_, rfl⟩
  have hc' : ∑ l, c' l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j (fun l _ hl => by rw [hc'_def, Pi.single_eq_of_ne hl, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h), hc'_def, Pi.single_eq_same, inv_mul_cancel₀ hξj]
  have h' : aeval (genSubst (genPt P) c') g = 0 := aeval_genSubst_eq_zero_of _ c' c hc' g h

  let L := Localization.Away a
  have hθu : IsUnit (algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P)) a) := isUnit_iff_ne_zero.mpr hξj
  let θ : L →+* (FractionRing (MvPolynomial (Fin n) F ⧸ P)) := IsLocalization.Away.lift a hθu
  have hθinj : Function.Injective θ := by
    unfold θ IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro y z
    rw [(IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors ha)).eq_iff,
      (IsFractionRing.injective (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).eq_iff]
  let ev : (MvPolynomial (Fin n) F ⧸ P) →+* AlgebraicClosure F :=
    Ideal.Quotient.lift P (aeval x).toRingHom (fun p hp => hxP p hp)
  have hev : ∀ p, ev (Ideal.Quotient.mk P p) = aeval x p := fun p => rfl
  have hψu : IsUnit (ev a) := isUnit_iff_ne_zero.mpr (by rw [ha_def, hev, aeval_X]; exact hj)
  let ψ : L →+* AlgebraicClosure F := IsLocalization.Away.lift a hψu
  let ξL : Fin n → L := fun l => algebraMap (MvPolynomial (Fin n) F ⧸ P) L (Ideal.Quotient.mk P (X l))
  let cL : Fin n → L := Pi.single j (IsLocalization.Away.invSelf a)
  have hθξ : ∀ l, θ (ξL l) = genPt P l := fun l => IsLocalization.Away.lift_eq a hθu _
  have hθinv : θ (IsLocalization.Away.invSelf a) = (genPt P j)⁻¹ := by
    have := congrArg θ (IsLocalization.Away.mul_invSelf (S := L) a)
    rw [map_mul, map_one, show θ (algebraMap (MvPolynomial (Fin n) F ⧸ P) L a) = genPt P j from hθξ j] at this
    exact eq_inv_of_mul_eq_one_right this
  have hθc : ∀ l, θ (cL l) = c' l := by
    intro l
    by_cases hl : l = j
    · subst hl; simp [cL, hc'_def, hθinv]
    · simp [cL, hc'_def, Pi.single_eq_of_ne hl]
  have hψξ : ∀ l, ψ (ξL l) = x l := fun l => by
    rw [IsLocalization.Away.lift_eq, hev, aeval_X]

  let f₀ : F →+* MvPolynomial (Fin k × Fin n) L :=
    C.comp ((algebraMap (MvPolynomial (Fin n) F ⧸ P) L).comp (algebraMap F (MvPolynomial (Fin n) F ⧸ P)))
  let Q := eval₂ f₀ (genSubst ξL cL) g
  have hQ : map θ Q = aeval (genSubst (genPt P) c') g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp [f₀, θ, MvPolynomial.algebraMap_apply, IsScalarTower.algebraMap_apply F (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))]
    · funext ij
      simp only [Function.comp_apply, map_genSubst, hθξ, hθc]
  have hQ0 : Q = 0 := by
    apply map_injective θ hθinj
    rw [hQ, h', map_zero]
  have hvQ : eval₂Hom ψ v Q = aeval v g := by
    rw [eval₂_comp_left, aeval_def]
    congr 1
    · ext r
      simp only [f₀, RingHom.coe_comp, Function.comp_apply, eval₂Hom_C]
      rw [IsLocalization.Away.lift_eq, ← Ideal.Quotient.mk_algebraMap, hev, AlgHom.commutes]
    · funext ij
      simp [genSubst, hψξ, hvx ij.1]
  rw [← hvQ, hQ0, map_zero]

theorem aeval_eq_zero_of_mem_incIdeal (h₁ : FGNullstellensatz.Statement) {F : Type} [Field F]
    {n k : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)) (hc : ∑ j, c j * genPt P j = 1)
    (g : MvPolynomial (Fin k × Fin n) F) (hg : g ∈ incIdeal P k) :
    aeval (genSubst (genPt P) c) g = 0 := by
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg

  let e : MvPolynomial (Fin n ⊕ Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ P) :=
    aeval (Sum.elim (genPt P) c)
  let D := e.range
  have : Algebra.FiniteType F D :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have : Algebra.FiniteType F (MvPolynomial (Fin k × Fin n) D) :=
    Algebra.FiniteType.trans (S := D) inferInstance inferInstance
  let ξD : Fin n → D := fun l => ⟨genPt P l, X (Sum.inl l), by simp [e]⟩
  let cD : Fin n → D := fun l => ⟨c l, X (Sum.inr l), by simp [e]⟩
  have hD : ∑ l, cD l * ξD l = 1 := Subtype.ext (by simpa [ξD, cD] using hc)
  let r : MvPolynomial (Fin k × Fin n) D := aeval (genSubst ξD cD) g
  have hr : map D.val.toRingHom r = aeval (genSubst (genPt P) c) g := by
    show map D.val.toRingHom (aeval (genSubst ξD cD) g) = _
    rw [hom_aeval (F := F) (R := MvPolynomial (Fin k × Fin n) D)
      (T := MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) (map D.val.toRingHom) (fun s => by simp [MvPolynomial.algebraMap_apply])]
    rw [show (fun s => map D.val.toRingHom (genSubst ξD cD s)) = genSubst (genPt P) c from
      funext fun ij => by rw [map_genSubst]; rfl]
  rw [← hr]
  suffices r = 0 by rw [this, map_zero]
  refine h₁ F (MvPolynomial (Fin k × Fin n) D) r fun φ => ?_

  let x : Fin n → AlgebraicClosure F := fun l => φ (C (ξD l))
  let cx : Fin n → AlgebraicClosure F := fun l => φ (C (cD l))
  let w : Fin k × Fin n → AlgebraicClosure F := fun ij => φ (X ij)
  let v : Fin k × Fin n → AlgebraicClosure F :=
    fun ij => w ij - (∑ l, w (ij.1, l) * x l) * cx ij.2
  have hφC : ∀ s : F, φ (C (algebraMap F D s)) = algebraMap F (AlgebraicClosure F) s := fun s => by
    rw [← MvPolynomial.algebraMap_apply, AlgHom.commutes]
  have key : ∑ l, cx l * x l = 1 := by
    calc ∑ l, cx l * x l = φ (C (∑ l, cD l * ξD l)) := by simp [cx, x, map_sum]
      _ = 1 := by rw [hD, map_one, map_one]
  have hφr : φ r = aeval v g := by
    rw [show φ r = φ.toRingHom r from rfl,
      hom_aeval (F := F) φ.toRingHom (fun s => φ.commutes s)]
    rw [show (fun s => φ.toRingHom (genSubst ξD cD s)) = v from funext fun ij => by
      simp [genSubst, v, w, x, cx]]
  have hvI : v ∈ incidence P k := by
    refine ⟨x, fun hx => ?_, fun p hp => ?_, fun i => ?_⟩
    · rw [hx] at key
      simp at key
    · have hpD : aeval ξD p = 0 := by
        apply Subtype.ext
        have h1 := hom_aeval (F := F) D.val.toRingHom (fun s => D.val.commutes s) ξD p
        have h2 := hom_aeval (F := F)
          ((algebraMap (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp
            (Ideal.Quotient.mk P)) (fun s => by
              rw [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]) X p
        simp only [aeval_X_left_apply, RingHom.coe_comp, Function.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero] at h2
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val] at h1
        rw [h1]
        exact h2.symm
      have h3 := hom_aeval (F := F) (φ.toRingHom.comp C) hφC ξD p
      simp only [hpD, map_zero, RingHom.coe_comp, Function.comp_apply] at h3
      exact h3.symm
    · simp only [v, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, key, mul_one,
        sub_self]
  rw [hφr]
  exact hg v hvI

theorem proof (h₁ : FGNullstellensatz.Statement) : IncidenceGeneric.Statement := by
  intro F _ n k P _ c hc g
  exact ⟨aeval_eq_zero_of_mem_incIdeal h₁ P c hc g, mem_incIdeal_of_aeval_eq_zero P c g⟩

end IncidenceGeneric

end

end GroundTheory.Heights₂.Heights
