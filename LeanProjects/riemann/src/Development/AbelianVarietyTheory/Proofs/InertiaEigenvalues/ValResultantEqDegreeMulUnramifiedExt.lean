import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyLeftMulBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGeneratesUnramifiedExtResidueFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsRootResidueCofactorUnramifiedExtStatement

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.ResVal

theorem int_lift : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∃ φO : K.O →+* K'.O, (∀ x, algebraMap K'.O K'.E (φO x) = φ (algebraMap K.O K.E x)) ∧
      @Algebra.IsIntegral K.O K'.O _ _ φO.toAlgebra := GlobalTheory.T.exists_integerMap_isIntegral_unramifiedInvolutionExt

theorem val_norm : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E,
    val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt

theorem res_gen : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ →
    ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A →
    (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) →
    ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 →
    Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree →
    ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O,
      algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) +
        algebraMap K'.O K'.E z := GlobalTheory.T.residue_generates_unramifiedExt_residueField

theorem res_mult : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ s : K'.O,
    (∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O,
      algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) +
        algebraMap K'.O K'.E z) →
    ∀ (p : K.O[X]) (r c : K'.O[X]), p.Monic → r.Monic →
    r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree →
    p.natDegree = d * r.natDegree →
    p.map (φ.comp (algebraMap K.O K.E)) = (r * c).map (algebraMap K'.O K'.E) →
    ¬ (c.map (IsLocalRing.residue K'.O)).IsRoot (IsLocalRing.residue K'.O s) := GlobalTheory.T.not_isRoot_residue_cofactor_unramifiedExt

theorem val_neg_one_pow {K : UQ} (k : ℕ) (x : K.E) : val K.O ((-1) ^ k * x) = val K.O x := by
  rcases neg_one_pow_eq_or K.E k with h | h <;> simp [h, val, Valuation.map_neg]

theorem val_mul' {K : UQ} {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add]

theorem val_mul_unit {K : UQ} (x : K.E) (u : K.O) (hu : IsUnit u) :
    val K.O (x * algebraMap K.O K.E u) = val K.O x := by
  by_cases hx : x = 0
  · simp [hx]
  have hu0 : algebraMap K.O K.E u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hu.ne_zero
  rw [val_mul' hx hu0, GlobalTheory.UnitLemma.Orbit.val_unit u hu, add_zero]

theorem norm_res {E A : Type} [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A) (p : E[X])
    (hp : p.Monic) : ∃ k : ℕ, Algebra.norm E (aeval g p) = (-1) ^ k * resultant p (LinearMap.mulLeft E g).charpoly := by
  let u := Module.finBasis E A
  have h := GlobalTheory.TraceDetSplit.det_aeval (Algebra.leftMulMatrix u g) p hp
  rw [GlobalTheory.TraceDetSplit.charpoly_leftMul_basis, aeval_algHom_apply, ← Algebra.norm_eq_matrix_det] at h
  exact ⟨_, h⟩

theorem charpoly_subsingleton {E A : Type} [Field E] [CommRing A] [Algebra E A] [Module.Finite E A]
    [Subsingleton A] (g : A) : (LinearMap.mulLeft E g).charpoly = 1 := by
  apply eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
  rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]

theorem aeval_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g B.P
  have h0 : aeval (Algebra.lmul K.E B.A B.g) B.P = 0 := LinearMap.aeval_self_charpoly _
  rw [h0] at h
  exact Algebra.lmul_injective (h.symm.trans (map_zero _).symm)

theorem norm_tower {K K' : UQ} (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (x : B.A) :
    Algebra.norm K.E x = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (@Algebra.norm K'.E B.A _ _ ψ.toAlgebra x) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  rw [Algebra.norm_apply K.E x, Algebra.norm_apply K'.E x, ← LinearMap.det_restrictScalars]
  rfl

theorem monic_dvd_pow {F : Type} [Field F] (a : F) (n : ℕ) (f : F[X]) (hf : f.Monic) (h : f ∣ (X - C a) ^ n) :
    f = (X - C a) ^ f.natDegree := by
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C a) n).1 h
  have e := eq_of_monic_of_associated hf ((monic_X_sub_C a).pow i) hi
  rw [e, natDegree_pow, natDegree_X_sub_C, mul_one]

theorem val_resultant_unr : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B₁ B₂ : InvAlg K) (ψ₁ : K'.E →+* B₁.A) (ψ₂ : K'.E →+* B₂.A) (h₁ : ∀ e, ψ₁ (φ e) = algebraMap K.E B₁.A e) (h₁' : ∀ e, B₁.σ (ψ₁ e) = ψ₁ (K'.c e)) (h₂ : ∀ e, ψ₂ (φ e) = algebraMap K.E B₂.A e) (h₂' : ∀ e, B₂.σ (ψ₂ e) = ψ₂ (K'.c e)), (∀ y : K'.O, (ψ₁.prod ψ₂) (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) → (B₁.P * B₂.P).Separable → ∀ s : K'.O, (∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B₁ ψ₁ h₁ h₁').P * (overExt φ B₂ ψ₂ h₂ h₂').P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree) → val K.O (resultant B₁.P B₂.P) = d * val K'.O (resultant (overExt φ B₁ ψ₁ h₁ h₁').P (overExt φ B₂ ψ₂ h₂ h₂').P) := by
  intro K K' d φ hU _ B₁ B₂ ψ₁ ψ₂ h₁ h₁' h₂ h₂' hO hsep s ⟨Q, hQ, hQr⟩
  set B₁' := overExt φ B₁ ψ₁ h₁ h₁' with hB₁'
  set B₂' := overExt φ B₂ ψ₂ h₂ h₂' with hB₂'
  by_cases t₁ : Subsingleton B₁.A
  · have e1 : B₁.P = 1 := charpoly_subsingleton B₁.g
    haveI : Subsingleton B₁'.A := t₁
    have e1' : B₁'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₁'.A) B₁'.g
    simp [e1, e1', val]
  by_cases t₂ : Subsingleton B₂.A
  · have e2 : B₂.P = 1 := charpoly_subsingleton B₂.g
    haveI : Subsingleton B₂'.A := t₂
    have e2' : B₂'.P = 1 := charpoly_subsingleton (E := K'.E) (A := B₂'.A) B₂'.g
    simp [e2, e2', val]
  haveI : Nontrivial B₁.A := not_subsingleton_iff_nontrivial.1 t₁
  haveI : Nontrivial B₂.A := not_subsingleton_iff_nontrivial.1 t₂
  have hPm₁ : B₁'.P.Monic := LinearMap.charpoly_monic _
  have hPm₂ : B₂'.P.Monic := LinearMap.charpoly_monic _
  have hinj' := IsFractionRing.injective K'.O K'.E
  have hinj := IsFractionRing.injective K.O K.E
  have hQm : Q.Monic := monic_of_injective hinj' (by rw [hQ]; exact hPm₁.mul hPm₂)
  obtain ⟨r₁, hr₁⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₁'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_right _ _)
  obtain ⟨r₂, hr₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hQm
    (show B₂'.P ∣ Q.map (algebraMap K'.O K'.E) by rw [hQ]; exact dvd_mul_left _ _)
  rw [hPm₁.leadingCoeff, C_1, mul_one] at hr₁
  rw [hPm₂.leadingCoeff, C_1, mul_one] at hr₂
  have hr₁m : r₁.Monic := monic_of_injective hinj' (by rw [hr₁]; exact hPm₁)
  have hr₂m : r₂.Monic := monic_of_injective hinj' (by rw [hr₂]; exact hPm₂)
  have hQr₁₂ : Q = r₁ * r₂ := Polynomial.map_injective _ hinj' (by rw [hQ, Polynomial.map_mul, hr₁, hr₂])
  have hres : ∀ r : K'.O[X], r.Monic → r ∣ Q →
      r.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ r.natDegree := by
    intro r hr hrQ
    have := monic_dvd_pow _ _ _ (hr.map _) (hQr ▸ Polynomial.map_dvd _ hrQ)
    rwa [hr.natDegree_map] at this
  have hr₁r := hres r₁ hr₁m (by rw [hQr₁₂]; exact dvd_mul_right _ _)
  have hr₂r := hres r₂ hr₂m (by rw [hQr₁₂]; exact dvd_mul_left _ _)
  obtain ⟨φO, hφO, hint⟩ := int_lift K K' d φ hU
  have hφc : (algebraMap K'.O K'.E).comp φO = φ.comp (algebraMap K.O K.E) := RingHom.ext hφO
  have hg₂ : IsIntegral K.O B₂.g := by
    letI : Algebra K.O K'.O := φO.toAlgebra
    letI : Algebra K'.O B₂.A := (ψ₂.comp (algebraMap K'.O K'.E)).toAlgebra
    haveI : IsScalarTower K.O K'.O B₂.A := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap K.O B₂.A x = ψ₂ (algebraMap K'.O K'.E (φO x))
      rw [hφO, h₂, ← IsScalarTower.algebraMap_apply]
    haveI : Algebra.IsIntegral K.O K'.O := hint
    have h2 : IsIntegral K'.O B₂.g := ⟨r₂, hr₂m, by
      change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g r₂ = 0
      rw [← eval₂_map, hr₂]
      exact aeval_P B₂'⟩
    exact isIntegral_trans (R := K.O) _ h2
  have hs₂ : B₂.P.Separable := hsep.of_mul_right
  obtain ⟨p₂, hp₂m, hp₂⟩ := GlobalTheory.UnitLemma.Orbit.exists_monic_map_eq_charpoly₂ B₂ hs₂ hg₂
  have hs₂' : B₂'.P.Separable := GlobalTheory.T.separable_charpoly_invAlgBaseChangeUnramified K K' d φ hU B₂ ψ₂ h₂ h₂' hs₂
  have hcomp : ∀ (A : Type) [CommRing A] [Algebra K.E A] [Algebra K.O A] [IsScalarTower K.O K.E A] (ψ : K'.E →+* A),
      (∀ e, ψ (φ e) = algebraMap K.E A e) → (ψ.comp (algebraMap K'.O K'.E)).comp φO = algebraMap K.O A := by
    intro A _ _ _ _ ψ hψ
    ext x
    simp [hφO, hψ, ← IsScalarTower.algebraMap_apply]
  have hf0 : aeval B₂'.g (p₂.map φO) = 0 := by
    change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g (p₂.map φO) = 0
    rw [eval₂_map, hcomp B₂.A ψ₂ h₂, ← aeval_def, ← aeval_map_algebraMap K.E, hp₂]
    exact aeval_P B₂
  obtain ⟨c', hc'⟩ := GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero B₂' hs₂' _ hf0
  have hfm : (p₂.map φO).Monic := hp₂m.map _
  have hc'm : c'.Monic := hPm₂.of_mul_monic_left (by rw [← hc']; exact hfm.map _)
  obtain ⟨c₂, hc₂⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K'.E hfm
    (show c' ∣ (p₂.map φO).map (algebraMap K'.O K'.E) from ⟨B₂'.P, by rw [hc', mul_comm]⟩)
  rw [hc'm.leadingCoeff, C_1, mul_one] at hc₂
  have hfrc : p₂.map φO = r₂ * c₂ :=
    Polynomial.map_injective _ hinj' (by rw [hc', Polynomial.map_mul, hr₂, hc₂])
  have hgen := res_gen K K' d φ hU (B₁.prod B₂) (ψ₁.prod ψ₂) (fun e => Prod.ext (h₁ e) (h₂ e)) (show Nontrivial (B₁.A × B₂.A) from inferInstance)
    hO s Q hQm (by
      show (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q : B₁.A × B₂.A) = 0
      refine Prod.ext ?_ ?_
      · change (RingHom.fst B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₁.comp (algebraMap K'.O K'.E)) B₁.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₁ B₁.g B₁'.P = 0 := aeval_P B₁'
        rw [h0, zero_mul]
      · change (RingHom.snd B₁.A B₂.A) (eval₂ ((ψ₁.prod ψ₂).comp (algebraMap K'.O K'.E)) ((B₁.g, B₂.g) : B₁.A × B₂.A) Q) = 0
        rw [hom_eval₂]
        change eval₂ (ψ₂.comp (algebraMap K'.O K'.E)) B₂.g Q = 0
        rw [← eval₂_map, hQ, eval₂_mul]
        have h0 : eval₂ ψ₂ B₂.g B₂'.P = 0 := aeval_P B₂'
        rw [h0, mul_zero]) hQr
  have hdeg : p₂.natDegree = d * r₂.natDegree := by
    have a1 : p₂.natDegree = Module.finrank K.E B₂.A := by
      rw [← natDegree_map_eq_of_injective hinj p₂, hp₂]; exact LinearMap.charpoly_natDegree _
    have a2 : r₂.natDegree = @Module.finrank K'.E B₂.A _ _ ψ₂.toAlgebra.toModule := by
      rw [← natDegree_map_eq_of_injective hinj' r₂, hr₂]; exact LinearMap.charpoly_natDegree _
    rw [a1, a2, ← hU.2.2.2.2]
    letI : Algebra K.E K'.E := φ.toAlgebra
    letI : Algebra K'.E B₂.A := ψ₂.toAlgebra
    haveI : IsScalarTower K.E K'.E B₂.A := IsScalarTower.of_algebraMap_eq fun e => (h₂ e).symm
    exact (Module.finrank_mul_finrank K.E K'.E B₂.A).symm
  have hmap : p₂.map (φ.comp (algebraMap K.O K.E)) = (r₂ * c₂).map (algebraMap K'.O K'.E) := by
    rw [← hfrc, Polynomial.map_map, hφc]
  have hnr := res_mult K K' d φ hU s hgen p₂ r₂ c₂ hp₂m hr₂m hr₂r hdeg hmap
  have hu : IsUnit (resultant c₂ r₁) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← resultant_map_map, hr₁r,
      resultant_X_sub_C_pow_right _ _ _ _ natDegree_map_le]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ hnr)
  obtain ⟨k₁, hk₁⟩ := norm_res B₁.g B₂.P (LinearMap.charpoly_monic _)
  have hk₁' : Algebra.norm K.E (aeval B₁.g B₂.P) = (-1) ^ k₁ * resultant B₂.P B₁.P := hk₁
  obtain ⟨k₂, hk₂⟩ := norm_res (E := K'.E) (A := B₁'.A) B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) (hfm.map _)
  have e : (aeval B₁'.g ((p₂.map φO).map (algebraMap K'.O K'.E)) : B₁.A) = aeval B₁.g B₂.P := by
    change eval₂ ψ₁ B₁.g ((p₂.map φO).map (algebraMap K'.O K'.E)) = _
    rw [Polynomial.map_map, eval₂_map, ← hp₂, aeval_map_algebraMap, aeval_def, ← RingHom.comp_assoc,
      hcomp B₁.A ψ₁ h₁]
  have hk₂' : @Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P) =
      (-1) ^ k₂ * resultant (B₂'.P * c₂.map (algebraMap K'.O K'.E)) B₁'.P := by
    rw [← e, hc₂, ← hc']; exact hk₂
  have hmul := resultant_mul_left B₂'.P (c₂.map (algebraMap K'.O K'.E)) B₁'.P B₁'.P.natDegree le_rfl
  rw [← hPm₂.natDegree_mul (by rw [hc₂]; exact hc'm)] at hmul
  have hcu : resultant (c₂.map (algebraMap K'.O K'.E)) B₁'.P = algebraMap K'.O K'.E (resultant c₂ r₁) := by
    rw [← hr₁, natDegree_map_eq_of_injective hinj', natDegree_map_eq_of_injective hinj', resultant_map_map]
  calc val K.O (resultant B₁.P B₂.P) = val K.O (resultant B₂.P B₁.P) := by
        rw [resultant_comm, val_neg_one_pow]
    _ = val K.O (Algebra.norm K.E (aeval B₁.g B₂.P)) := by rw [hk₁', val_neg_one_pow]
    _ = d * val K'.O (@Algebra.norm K'.E B₁.A _ _ ψ₁.toAlgebra (aeval B₁.g B₂.P)) := by
        rw [norm_tower φ B₁ ψ₁ h₁, val_norm K K' d φ hU]
    _ = d * val K'.O (resultant B₂'.P B₁'.P) := by
        rw [hk₂', val_neg_one_pow, hmul, hcu, val_mul_unit _ _ hu]
    _ = d * val K'.O (resultant B₁'.P B₂'.P) := by
        rw [resultant_comm B₂'.P, val_neg_one_pow]

end GlobalTheory.UnitLemma.Unr.ResVal
