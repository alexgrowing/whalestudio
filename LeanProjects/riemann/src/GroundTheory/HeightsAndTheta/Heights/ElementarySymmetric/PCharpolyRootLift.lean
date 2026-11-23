import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCharpolyRootLift
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRingHomExtendOfIsIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace CharpolyRootLift

theorem charpoly_blockDiagonal {n o R : Type*} [DecidableEq n] [Fintype n] [DecidableEq o] [Fintype o]
    [CommRing R] (M : o → Matrix n n R) :
    (Matrix.blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  unfold Matrix.charpoly
  rw [show Matrix.charmatrix (Matrix.blockDiagonal M) =
      Matrix.blockDiagonal (fun k => Matrix.charmatrix (M k)) from ?_, Matrix.det_blockDiagonal]
  ext ⟨i, k⟩ ⟨j, k'⟩
  by_cases hk : k = k'
  · subst hk
    by_cases hij : i = j
    · subst hij; simp [Matrix.blockDiagonal_apply]
    · simp [Matrix.blockDiagonal_apply, hij]
  · simp [Matrix.blockDiagonal_apply, hk]

theorem charpoly_lmul_eq_minpoly_pow {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (x : L) :
    LinearMap.charpoly (Algebra.lmul K L x) = minpoly K x ^ Module.finrank (IntermediateField.adjoin K {x}) L := by
  classical
  have hx : IsIntegral K x := .of_finite K x
  let pb := IntermediateField.adjoin.powerBasis hx
  let c := Module.Free.chooseBasis (IntermediateField.adjoin K {x}) L
  let bc := pb.basis.smulTower c
  rw [← LinearMap.charpoly_toMatrix _ bc]
  have h1 : (LinearMap.toMatrix bc bc) (Algebra.lmul K L x) = Algebra.leftMulMatrix bc x :=
    Algebra.toMatrix_lmul_eq bc x
  have h2 : Algebra.leftMulMatrix bc x =
      Matrix.blockDiagonal fun _ => Algebra.leftMulMatrix pb.basis pb.gen := by
    rw [IntermediateField.adjoin.powerBasis_gen]
    exact Algebra.smulTower_leftMulMatrix_algebraMap pb.basis c (IntermediateField.AdjoinSimple.gen K x)
  rw [h1, h2, charpoly_blockDiagonal, Finset.prod_const, Finset.card_univ, charpoly_leftMulMatrix,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, Module.finrank_eq_card_chooseBasisIndex]

theorem coeff_sum_C_mul_X_pow_sub {R : Type*} [CommRing R] (n : ℕ) (b : ℕ → R) (k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ (n - i)).coeff k =
      if k ≤ n then b (n - k) else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single (n - k)]
    · rw [if_pos (by omega), mul_one]
    · intro i hi hne
      rw [if_neg (by simp at hi; omega), mul_zero]
    · intro h; simp only [Finset.mem_range, not_lt] at h; omega
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [if_neg (by simp at hi; omega), mul_zero]

theorem natDegree_sum_C_mul_X_pow_sub {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) (b : ℕ → R) (hb : b 0 = 1) :
    (∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ (n - i)).natDegree = n := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sum_C_mul_X_pow_sub, if_neg (by exact_mod_cast not_le.2 hN)]
  · rw [coeff_sum_C_mul_X_pow_sub, if_pos le_rfl, Nat.sub_self, hb]
    exact one_ne_zero

theorem scaleRoots_sum_C_mul_X_pow_sub {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) (b : ℕ → R) (hb : b 0 = 1)
    (t : R) :
    (∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ (n - i)).scaleRoots t =
      ∑ i ∈ Finset.range (n + 1), Polynomial.C (t ^ i * b i) * Polynomial.X ^ (n - i) := by
  ext k
  rw [Polynomial.coeff_scaleRoots, natDegree_sum_C_mul_X_pow_sub n b hb, coeff_sum_C_mul_X_pow_sub,
    coeff_sum_C_mul_X_pow_sub]
  split_ifs with hk
  · rw [mul_comm]
  · rw [zero_mul]

theorem exists_homogenization {ι : Type*} (a : ι) (G : MvPolynomial ι ℚ) :
    ∃ (d : ℕ) (F : MvPolynomial ι ℚ), F.IsHomogeneous d ∧
      ∀ (K : Type) [Field K] [CharZero K] (y : ι → K), y a ≠ 0 →
        aeval y F = y a ^ d * aeval (fun k => y k / y a) G := by
  classical
  refine ⟨G.totalDegree, ∑ i ∈ Finset.range (G.totalDegree + 1),
    homogeneousComponent i G * X a ^ (G.totalDegree - i), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ G.totalDegree := by simp at hi; omega
    have := (homogeneousComponent_isHomogeneous i G).mul (isHomogeneous_X_pow a (G.totalDegree - i))
    rwa [Nat.add_sub_cancel' hi'] at this
  · intro K _ _ y hy
    have hG : aeval (fun k => y k / y a) G = ∑ i ∈ Finset.range (G.totalDegree + 1),
        aeval (fun k => y k / y a) (homogeneousComponent i G) := by
      conv_lhs => rw [← sum_homogeneousComponent G]
      rw [map_sum]
    rw [hG]
    simp only [map_sum, map_mul, map_pow, aeval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ G.totalDegree := by simp at hi; omega
    have hyy : (fun k => y k / y a) = fun k => (y a)⁻¹ * y k := by
      funext k; rw [div_eq_inv_mul]
    rw [hyy, FibreNormCharpoly.aeval_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous i G),
      pow_sub₀ _ hy hi', inv_pow]
    ring

theorem ne_zero_of_generic {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (k : Fin (D + 1)) : l k ≠ 0 := fun h =>
  X_ne_zero k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X, h]))

theorem aeval_div_eq_zero_of_generic {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (a : Fin (D + 1)) {G : MvPolynomial (Fin (D + 1)) ℚ} (hG : aeval (fun k => l k / l a) G = 0)
    (K : Type) [Field K] [CharZero K] (y : Fin (D + 1) → K) (hy : y a ≠ 0) :
    aeval (fun k => y k / y a) G = 0 := by
  obtain ⟨d, F, hF, hFy⟩ := exists_homogenization a G
  have h0 : F = 0 := hgen d F hF (by rw [hFy Ω l (ne_zero_of_generic hgen a), hG, mul_zero])
  have h1 := hFy K y hy
  rw [h0, map_zero] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left (pow_ne_zero _ hy)

theorem algebraicIndependent_ratios {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (a : Fin (D + 1)) :
    AlgebraicIndependent ℚ (fun k : {k // k ≠ a} => l k.1 / l a) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro G hG
  have hG' : aeval (fun k => l k / l a) (rename Subtype.val G) = 0 := by
    rw [aeval_rename]; exact hG
  refine MvPolynomial.funext fun z => ?_
  let y : Fin (D + 1) → ℚ := fun k => if h : k = a then 1 else z ⟨k, h⟩
  have hy : y a = 1 := by simp [y]
  have h1 := aeval_div_eq_zero_of_generic hgen a hG' ℚ y (by rw [hy]; exact one_ne_zero)
  rw [aeval_rename] at h1
  have hyz : ((fun k => y k / y a) ∘ Subtype.val) = z := by
    funext k; simp [y, hy, k.2]
  rw [hyz] at h1
  rw [map_zero, ← MvPolynomial.coe_aeval_eq_eval]
  exact h1

theorem adjoin_ratios_eq {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω} {a : Fin (D + 1)} (ha : l a ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun k : {k // k ≠ a} => l k.1 / l a) =
      Algebra.adjoin ℚ (Set.range fun k => l k / l a) := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (by rintro _ ⟨k, rfl⟩; exact ⟨k.1, rfl⟩)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = a
    · subst hk
      simp only [div_self ha]
      exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩

theorem exists_ratio_equiv {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (a : Fin (D + 1)) :
    ∃ e : MvPolynomial {k // k ≠ a} ℚ ≃ₐ[ℚ] Algebra.adjoin ℚ (Set.range fun k => l k / l a),
      ∀ k : {k // k ≠ a}, (e (X k) : Ω) = l k.1 / l a := by
  have hind := algebraicIndependent_ratios hgen a
  refine ⟨hind.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (adjoin_ratios_eq (ne_zero_of_generic hgen a))),
    fun k => ?_⟩
  simp only [AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply]
  have := hind.algebraMap_aevalEquiv (X k)
  rw [aeval_X] at this
  exact this

theorem isIntegrallyClosed_adjoin_ratios {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (a : Fin (D + 1)) :
    IsIntegrallyClosed (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) := by
  obtain ⟨e, -⟩ := exists_ratio_equiv hgen a
  have := e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem exists_algHom_ratios {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (a : Fin (D + 1)) (ζ : Fin (D + 1) → ℂ) (hζ : ζ a ≠ 0) :
    ∃ φ : Algebra.adjoin ℚ (Set.range fun k => l k / l a) →ₐ[ℚ] ℂ,
      ∀ (k : Fin (D + 1)) (hk : l k / l a ∈ Algebra.adjoin ℚ (Set.range fun k => l k / l a)),
        φ ⟨l k / l a, hk⟩ = ζ k / ζ a := by
  obtain ⟨e, he⟩ := exists_ratio_equiv hgen a
  refine ⟨(aeval fun k : {k // k ≠ a} => ζ k.1 / ζ a).comp e.symm.toAlgHom, fun k hk => ?_⟩
  by_cases hka : k = a
  · subst hka
    have h1 : (⟨l k / l k, hk⟩ : Algebra.adjoin ℚ (Set.range fun k' => l k' / l k)) = 1 :=
      Subtype.ext (div_self (ne_zero_of_generic hgen k))
    rw [h1, map_one, div_self hζ]
  · have h1 : (⟨l k / l a, hk⟩ : Algebra.adjoin ℚ (Set.range fun k => l k / l a)) = e (X ⟨k, hka⟩) :=
      Subtype.ext (he ⟨k, hka⟩).symm
    rw [h1]
    simp

theorem exists_ringHom_extend_of_isIntegral {R S K : Type*} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) (f : R →+* K) :
    ∃ g : S →+* K, ∀ r, g (algebraMap R S r) = f r :=
  _root_.UpperTheory.Reformulated.B.RingHomExtensionOfIntegral.exists_ringHom_extend_of_isIntegral hinj f

end CharpolyRootLift

open IntermediateField.algebraAdjoinAdjoin in

theorem CharpolyRootLift.proof : CharpolyRootLift.Statement := by
  intro Ω _ _ D l P _ hP hgen j m u c hlj hc0 hhom hchar a hu ζ hζa w hw
  have hl := CharpolyRootLift.ne_zero_of_generic hgen
  have hPa : P = IntermediateField.adjoin ℚ (Set.range fun k => l k / l a) := by
    rw [hP]
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, k, -, rfl⟩
      have h1 : l i / l k = (l i / l a) / (l k / l a) := by field_simp [hl a, hl k]
      rw [h1]
      exact div_mem (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
    · exact IntermediateField.adjoin.mono _ _ _ (by rintro _ ⟨k, rfl⟩; exact ⟨k, a, hl a, rfl⟩)
  subst hPa
  have : IsIntegrallyClosed (Algebra.adjoin ℚ (Set.range fun k => l k / l a)) :=
    CharpolyRootLift.isIntegrallyClosed_adjoin_ratios hgen a
  set A := Algebra.adjoin ℚ (Set.range fun k => l k / l a) with hA
  set P := IntermediateField.adjoin ℚ (Set.range fun k => l k / l a) with hP'
  obtain ⟨φ, hφ⟩ := CharpolyRootLift.exists_algHom_ratios hgen a ζ hζa
  set n := Module.finrank P Ω with hn
  set x := u / l j ^ m with hx
  set v := u / l a ^ m with hv
  have htP : (l j / l a) ^ m ∈ P := pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self j)) m
  let t : ↥P := ⟨(l j / l a) ^ m, htP⟩
  have ht0 : t ≠ 0 := fun h => pow_ne_zero m (div_ne_zero (hl j) (hl a)) (congrArg Subtype.val h)
  have htx : t • x = v := by
    rw [Algebra.smul_def]
    change (l j / l a) ^ m * (u / l j ^ m) = u / l a ^ m
    rw [div_pow]
    field_simp [hl j, hl a]
  have hvint : IsIntegral A v := hu
  have hfP : minpoly P v = (minpoly A v).map (algebraMap A P) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' P hvint
  have hsm : minpoly P v = (minpoly P x).scaleRoots t := by
    rw [← htx]; exact IsIntegrallyClosed.minpoly_smul ht0 (IsIntegral.of_finite P x)
  have hcp := CharpolyRootLift.charpoly_lmul_eq_minpoly_pow (K := P) x
  set r := Module.finrank (IntermediateField.adjoin P {x}) Ω
  have hcoef : ∀ i ≤ n, aeval (fun k => l k / l a) (c i) =
      ((l j / l a) ^ m) ^ i * aeval (fun k => l k / l j) (c i) := by
    intro i hi
    have h1 : (fun k => l k / l a) = fun k => (l j / l a) * (l k / l j) := by
      funext k; field_simp [hl j, hl a]
    rw [h1, FibreNormCharpoly.aeval_mul_of_isHomogeneous (hhom i hi), ← pow_mul, mul_comm i m]
  let ptA : Fin (D + 1) → A := fun k => ⟨l k / l a, Algebra.subset_adjoin ⟨k, rfl⟩⟩
  let QA : Polynomial A :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.C (aeval ptA (c i)) * Polynomial.X ^ (n - i)
  have hQA : minpoly A v ^ r = QA := by
    apply Polynomial.map_injective (algebraMap A Ω) Subtype.val_injective
    rw [Polynomial.map_pow, IsScalarTower.algebraMap_eq A P Ω, ← Polynomial.map_map, ← hfP, hsm,
      Polynomial.map_scaleRoots _ _ _ (by
        rw [(minpoly.monic (IsIntegral.of_finite P x)).leadingCoeff, map_one]; exact one_ne_zero),
      ← Polynomial.pow_scaleRoots_of_isReduced, ← Polynomial.map_pow, ← hcp, hchar,
      CharpolyRootLift.scaleRoots_sum_C_mul_X_pow_sub _ _ (by rw [hc0, map_one])]
    simp only [QA, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := by simp only [Finset.mem_range] at hi; omega
    congr 2
    change ((l j / l a) ^ m) ^ i * _ = A.val (aeval ptA (c i))
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    exact (hcoef i hi').symm
  have hroot : Polynomial.eval₂ φ.toRingHom (w / ζ a ^ m) (minpoly A v) = 0 := by
    have h1 : Polynomial.eval₂ φ.toRingHom (w / ζ a ^ m) QA = 0 := by
      simp only [QA, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X_pow]
      rw [← mul_zero (((ζ a ^ m)⁻¹) ^ n), ← hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := by simp only [Finset.mem_range] at hi; omega
      have hφc : φ.toRingHom (aeval ptA (c i)) = aeval (fun k => (ζ a)⁻¹ * ζ k) (c i) := by
        change (φ.comp (aeval ptA)) (c i) = _
        rw [MvPolynomial.comp_aeval]
        congr 1
        ext k
        simp only [aeval_X]
        rw [← div_eq_inv_mul]; exact hφ k _
      rw [hφc, FibreNormCharpoly.aeval_mul_of_isHomogeneous (hhom i hi'), MvPolynomial.eval_map,
        ← MvPolynomial.aeval_def]
      have key : (ζ a)⁻¹ ^ (i * m) * ((ζ a ^ m)⁻¹) ^ (n - i) = ((ζ a ^ m)⁻¹) ^ n := by
        rw [mul_comm i m, pow_mul, inv_pow, ← pow_add, Nat.add_sub_cancel' hi']
      rw [div_eq_mul_inv w, mul_pow, ← key]
      ring
    rw [← hQA, Polynomial.eval₂_pow] at h1
    exact pow_eq_zero_iff'.1 h1 |>.1
  let e := minpoly.equivAdjoin hvint
  let ψ0 : Algebra.adjoin A {v} →+* ℂ :=
    (AdjoinRoot.lift φ.toRingHom (w / ζ a ^ m) hroot).comp e.symm.toRingEquiv.toRingHom
  have hψ0A : ∀ y : A, ψ0 (algebraMap A _ y) = φ y := by
    intro y
    change AdjoinRoot.lift φ.toRingHom (w / ζ a ^ m) hroot (e.symm (algebraMap A _ y)) = φ y
    rw [e.symm.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]
    rfl
  have hψ0v : ψ0 ⟨v, Algebra.self_mem_adjoin_singleton A v⟩ = w / ζ a ^ m := by
    have h1 : e.symm ⟨v, Algebra.self_mem_adjoin_singleton A v⟩ = AdjoinRoot.root (minpoly A v) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      simp [e]
    change AdjoinRoot.lift φ.toRingHom (w / ζ a ^ m) hroot (e.symm _) = _
    rw [h1, AdjoinRoot.lift_root]
  have hBS : Algebra.adjoin A {v} ≤ integralClosure A Ω :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  let : Algebra (Algebra.adjoin A {v}) (integralClosure A Ω) := (Subalgebra.inclusion hBS).toAlgebra
  have : IsScalarTower A (Algebra.adjoin A {v}) (integralClosure A Ω) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral (Algebra.adjoin A {v}) (integralClosure A Ω) :=
    ⟨fun s => (integralClosure.isIntegral s).tower_top⟩
  obtain ⟨g, hg⟩ :=
    CharpolyRootLift.exists_ringHom_extend_of_isIntegral (Subalgebra.inclusion_injective hBS) ψ0
  refine ⟨g, fun k hk => ?_, ?_⟩
  · have h1 : (⟨l k / l a, hk⟩ : integralClosure A Ω) =
        algebraMap (Algebra.adjoin A {v}) _ (algebraMap A _ (ptA k)) := rfl
    rw [h1, hg, hψ0A]
    exact hφ k _
  · have h1 : (⟨v, hu⟩ : integralClosure A Ω) =
        algebraMap (Algebra.adjoin A {v}) _ ⟨v, Algebra.self_mem_adjoin_singleton A v⟩ := rfl
    rw [h1, hg, hψ0v]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
