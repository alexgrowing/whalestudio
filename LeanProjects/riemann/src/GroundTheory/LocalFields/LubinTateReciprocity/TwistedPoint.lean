import Mathlib
import GroundTheory.LocalFields.LubinTateReciprocity.RootEval
import GroundTheory.LocalFields.FormalGroups.OverUnramified
import GroundTheory.LocalFields.LubinTateTorsion

noncomputable section

open PowerSeries IsLocalRing ValuativeRel GroundTheory.LocalField.FormalGroup

namespace GroundTheory.LocalField

section Series

variable {R : Type*} [CommRing R]

theorem coe_comp_eq_subst (p q : Polynomial R) (hq : q.coeff 0 = 0) :
    ((p.comp q : Polynomial R) : R⟦X⟧) = subst (q : R⟦X⟧) (p : R⟦X⟧) := by
  rw [subst_coe (HasSubst.of_constantCoeff_zero' (by rw [Polynomial.constantCoeff_coe, hq])),
    Polynomial.comp_eq_aeval]
  have h := Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom R) q p
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.algebraMap_self, map_id] at h
  exact h.symm

theorem map_coe_polynomial {S : Type*} [CommRing S] (φ : R →+* S) (p : Polynomial R) :
    PowerSeries.map φ (p : R⟦X⟧) = ((p.map φ : Polynomial S) : S⟦X⟧) := by
  ext n
  simp

theorem constantCoeff_subst_of_constantCoeff_eq_zero {G : R⟦X⟧} (hG : constantCoeff G = 0)
    (F : R⟦X⟧) : constantCoeff (subst G F : R⟦X⟧) = constantCoeff F := by
  have hs := HasSubst.of_constantCoeff_zero' hG
  conv_lhs => rw [F.eq_X_mul_shift_add_const]
  rw [← coe_substAlgHom hs, map_add, map_mul, coe_substAlgHom hs, subst_X hs, subst_C]
  change constantCoeff (G * _ + PowerSeries.C _) = _
  rw [map_add, map_mul, hG, zero_mul, zero_add, constantCoeff_C]

theorem exists_subst_eq_mul {G W : R⟦X⟧} (hG : constantCoeff G = 0) (hW : constantCoeff W = 0) :
    ∃ V : R⟦X⟧, (subst G W : R⟦X⟧) = G * V ∧ constantCoeff V = coeff 1 W := by
  obtain ⟨W', rfl⟩ := PowerSeries.X_dvd_iff.mpr hW
  have hs := HasSubst.of_constantCoeff_zero' hG
  refine ⟨subst G W', ?_, ?_⟩
  · rw [← coe_substAlgHom hs, map_mul, coe_substAlgHom hs, subst_X hs]
  · rw [constantCoeff_subst_of_constantCoeff_eq_zero hG, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_succ_X_mul]

end Series

section Iterates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

theorem ltPolyIter_succ_eq_mul (π : 𝒪[K]) (k : ℕ) :
    ltPolyIter π (k + 1) = ltPolyIter π k * ltEisenstein π k := by
  have hq := one_lt_card_residueField' K
  rw [ltPolyIter_succ, ltPoly, ltEisenstein, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.X_pow_comp, mul_add, ← pow_succ',
    Nat.sub_add_cancel hq.le]
  ring

variable (hπ : Irreducible π)

theorem coe_ltPolyIter (k : ℕ) :
    ((ltPolyIter π k : Polynomial 𝒪[K]) : 𝒪[K]⟦X⟧) =
      (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (π ^ k)).toPowerSeries := by
  induction k with
  | zero =>
    rw [pow_zero, lubinTateHom_self_one, Hom.toPowerSeries_id, ltPolyIter_zero, Polynomial.coe_X]
  | succ k ih =>
    rw [ltPolyIter_succ, coe_comp_eq_subst _ _ (coeff_zero_ltPolyIter π k), ih, pow_succ',
      lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
        (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp, lubinTateHom_self_uniformizer]

variable (B : Type*) [CommRing B] [Algebra 𝒪[K] B]

def ltSeries (a : 𝒪[K]) : B⟦X⟧ :=
  PowerSeries.map (algebraMap 𝒪[K] B)
    (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π) a).toPowerSeries

variable {B}

theorem constantCoeff_ltSeries (a : 𝒪[K]) : constantCoeff (ltSeries hπ B a) = 0 := by
  rw [ltSeries, powerSeries_constantCoeff_map, Hom.constantCoeff_eq_zero, map_zero]

theorem coeff_one_ltSeries (a : 𝒪[K]) : coeff 1 (ltSeries hπ B a) = algebraMap 𝒪[K] B a := by
  rw [ltSeries, coeff_map, coeff_one_lubinTateHom]

theorem subst_ltSeries (a b : 𝒪[K]) :
    (subst (ltSeries hπ B b) (ltSeries hπ B a) : B⟦X⟧) = ltSeries hπ B (a * b) := by
  rw [ltSeries, ltSeries, ltSeries, lubinTateHom_mul hπ (isLubinTateSeries_ltPoly π)
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π), Hom.toPowerSeries_comp]
  exact (map_subst (HasSubst.of_constantCoeff_zero' (Hom.constantCoeff_eq_zero _)) _).symm

theorem map_ltSeries (φ : B →ₐ[𝒪[K]] B) (a : 𝒪[K]) :
    PowerSeries.map (φ : B →+* B) (ltSeries hπ B a) = ltSeries hπ B a :=
  powerSeries_map_sigma_map_algebraMap φ _

theorem ltSeries_one : ltSeries hπ B 1 = X := by
  rw [ltSeries, lubinTateHom_self_one, Hom.toPowerSeries_id, map_X]

theorem ltSeries_uniformizer_pow (k : ℕ) :
    ltSeries hπ B (π ^ k) = (((ltPolyIter π k).map (algebraMap 𝒪[K] B) : Polynomial B) : B⟦X⟧) := by
  rw [ltSeries, ← coe_ltPolyIter hπ, map_coe_polynomial]

end Iterates

section Root

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B)

variable (π B) in

abbrev ltEisB (m : ℕ) : Polynomial B :=
  (ltEisenstein π m).map (algebraMap 𝒪[K] B)

variable (π B) in
omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem monic_ltEisB (m : ℕ) : (ltEisB π B m).Monic :=
  (ltEisenstein_monic π m).1.map _

omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem ltEisB_eq (m : ℕ) :
    ltEisB π B m = Polynomial.C (algebraMap 𝒪[K] B π) +
      ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) := by
  rw [ltEisB, ltEisenstein, Polynomial.map_add, Polynomial.map_C, Polynomial.map_pow]

include hπ hunr in

theorem isDistinguishedAt_ltEisB (m : ℕ) : (ltEisB π B m).IsDistinguishedAt (maximalIdeal B) := by
  have hmon := (ltEisenstein_monic π m).1
  refine ⟨⟨fun {n} hn => ?_⟩, hmon.map _⟩
  rw [hmon.natDegree_map] at hn
  rw [Polynomial.coeff_map, ← hunr]
  exact Ideal.mem_map_of_mem _ ((isEisensteinAt_ltEisenstein hπ m).mem hn)

include hπ hunr in

theorem algebraMap_uniformizer_mul_eq_zero {c : B} (h : algebraMap 𝒪[K] B π * c = 0) : c = 0 := by
  have hπB := irreducible_algebraMap hunr hπ
  exact (mul_eq_zero.mp h).resolve_left hπB.ne_zero

end Root

section Coordinates

variable {B : Type*} [CommRing B] {P : Polynomial B}

theorem repr_ringHom_eq (T : AdjoinRoot P →+* AdjoinRoot P) (ψ : B → B)
    (hof : ∀ b : B, T (AdjoinRoot.of P b) = AdjoinRoot.of P (ψ b))
    (hroot : T (AdjoinRoot.root P) = AdjoinRoot.root P) (pb : PowerBasis B (AdjoinRoot P))
    (hgen : pb.gen = AdjoinRoot.root P) (z : AdjoinRoot P) (i : Fin pb.dim) :
    pb.basis.repr (T z) i = ψ (pb.basis.repr z i) := by
  have hTz : T z = ∑ j, ψ (pb.basis.repr z j) • pb.basis j := by
    conv_lhs => rw [← pb.basis.sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerBasis.coe_basis, map_pow, hgen,
      AdjoinRoot.algebraMap_eq, hof, hroot]
  rw [hTz, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Coordinates

section Twist

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)

include hπ hunr

theorem rootEval_subst_ltSeries_uniformizer_pow_succ {F : B⟦X⟧} (hF : constantCoeff F = 0) :
    rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ (m + 1))) F) = 0 := by
  obtain ⟨V, hV, -⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ (m + 1))) hF
  rw [hV, map_mul, ltSeries_uniformizer_pow, ltPolyIter_succ_eq_mul, Polynomial.map_mul,
    Polynomial.coe_mul, map_mul, rootEval_self, mul_zero, zero_mul]

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem aeval_root_ltPolyIter_pow :
    Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1) =
      AdjoinRoot.of (ltEisB π B m) (-algebraMap 𝒪[K] B π) := by
  have h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m))
      (Polynomial.C (algebraMap 𝒪[K] B π) +
        ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) ^ (Nat.card 𝓀[K] - 1)) = 0 := by
    rw [← ltEisB_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [map_add, Polynomial.aeval_C, map_pow] at h
  rw [map_neg, eq_neg_of_add_eq_zero_right h]
  rfl

omit [IsAdicComplete (maximalIdeal B) B] in

theorem eq_zero_of_aeval_root_ltPolyIter_mul {z : AdjoinRoot (ltEisB π B m)}
    (h : Polynomial.aeval (AdjoinRoot.root (ltEisB π B m)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) * z = 0) : z = 0 := by
  have hq := one_lt_card_residueField' K
  refine eq_zero_of_mul_eq_zero_of_pow_eq (monic_ltEisB π B m)
    (b := -algebraMap 𝒪[K] B π) (fun c hc => ?_) (by omega)
    (aeval_root_ltPolyIter_pow m) h
  rw [neg_mul, neg_eq_zero] at hc
  exact algebraMap_uniformizer_mul_eq_zero hπ hunr hc

theorem eq_zero_of_rootEval_subst_mul {W : B⟦X⟧} (hW : constantCoeff W = 0)
    (hW1 : IsUnit (coeff 1 W)) {z : AdjoinRoot (ltEisB π B m)}
    (h : rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) W) * z = 0) : z = 0 := by
  obtain ⟨V, hV, hV0⟩ := exists_subst_eq_mul (constantCoeff_ltSeries hπ (π ^ m)) hW
  rw [hV, map_mul, ltSeries_uniformizer_pow, rootEval_coe, ← AdjoinRoot.aeval_eq] at h
  have hu : IsUnit (rootEval (isDistinguishedAt_ltEisB hπ hunr m) V) := isUnit_rootEval _ (hV0 ▸ hW1)
  have h' := eq_zero_of_aeval_root_ltPolyIter_mul hπ hunr m (z := rootEval (isDistinguishedAt_ltEisB hπ hunr m) V * z) (by rw [← mul_assoc, h])
  exact (hu.mul_right_eq_zero).mp h'

theorem aeval_rootEval_ltSeries_eq_zero {a : 𝒪[K]} (ha : IsUnit a) :
    Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) (ltEisB π B m) = 0 := by
  have hs := constantCoeff_ltSeries (B := B) hπ a
  have h1 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a))
      ((ltPolyIter π (m + 1)).map (algebraMap 𝒪[K] B)) = 0 := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, mul_comm,
      ← subst_ltSeries]
    exact rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m hs
  have h2 : Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B a)) ((ltPolyIter π m).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B (π ^ m)) (ltSeries hπ B a)) := by
    rw [← rootEval_subst_coe _ hs, ← ltSeries_uniformizer_pow hπ, subst_ltSeries, subst_ltSeries,
      mul_comm]
  rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, h2] at h1
  exact eq_zero_of_rootEval_subst_mul hπ hunr m (constantCoeff_ltSeries hπ a)
    (by rw [coeff_one_ltSeries]; exact ha.map _) h1

omit hπ hunr [IsDomain B] [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] in

theorem map_map_ltEisB (φ : B →ₐ[𝒪[K]] B) :
    (ltEisB π B m).map (φ : B →+* B) = ltEisB π B m := by
  rw [ltEisB, Polynomial.map_map, AlgHom.comp_algebraMap_of_tower]

variable (φ : B →ₐ[𝒪[K]] B) (u : 𝒪[K]ˣ)

def twistFrob : AdjoinRoot (ltEisB π B m) →+* AdjoinRoot (ltEisB π B m) :=
  AdjoinRoot.lift ((AdjoinRoot.of (ltEisB π B m)).comp (φ : B →+* B)) (rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])))
    (by
      rw [← Polynomial.eval₂_map, map_map_ltEisB (K := K) (π := π) m φ]
      exact aeval_rootEval_ltSeries_eq_zero hπ hunr m (Units.isUnit _))

theorem twistFrob_of (b : B) :
    twistFrob hπ hunr m φ u (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) (φ b) :=
  AdjoinRoot.lift_of _

theorem twistFrob_root :
    twistFrob hπ hunr m φ u (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) :=
  AdjoinRoot.lift_root _

theorem twistFrob_rootEval (F : B⟦X⟧) :
    twistFrob hπ hunr m φ u (rootEval (isDistinguishedAt_ltEisB hπ hunr m) F) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m) (subst (ltSeries hπ B ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K])) (PowerSeries.map (φ : B →+* B) F)) := by
  have hs := HasSubst.of_constantCoeff_zero'
    (constantCoeff_ltSeries (B := B) hπ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]))
  have key : (twistFrob hπ hunr m φ u).comp (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom =
      (rootEval (isDistinguishedAt_ltEisB hπ hunr m) : B⟦X⟧ →ₐ[B] AdjoinRoot (ltEisB π B m)).toRingHom.comp
        ((substAlgHom hs : B⟦X⟧ →ₐ[B] B⟦X⟧).toRingHom.comp (PowerSeries.map (φ : B →+* B))) := by
    refine rootEval_ringHom_ext (isDistinguishedAt_ltEisB hπ hunr m)
      (fun b => ?_) ?_ ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_C,
        twistFrob_of, map_C, coe_substAlgHom, subst_C]
      exact (rootEval_C _ (φ b)).symm
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root, map_X, coe_substAlgHom, subst_X hs]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rootEval_X,
        twistFrob_root]
      exact rootEval_mem_span_root _ (constantCoeff_ltSeries hπ _)
  have := congrArg (fun Φ : B⟦X⟧ →+* AdjoinRoot (ltEisB π B m) => Φ F) key
  simpa [coe_substAlgHom] using this

theorem twistFrob_iterate_root (k : ℕ) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.root (ltEisB π B m)) = rootEval (isDistinguishedAt_ltEisB hπ hunr m) (ltSeries hπ B (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ^ k)) := by
  induction k with
  | zero => rw [Function.iterate_zero, id, pow_zero, ltSeries_one, rootEval_X]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, twistFrob_rootEval, map_ltSeries, subst_ltSeries,
      pow_succ]

theorem twistFrob_iterate_of (k : ℕ) (b : B) :
    (twistFrob hπ hunr m φ u)^[k] (AdjoinRoot.of (ltEisB π B m) b) = AdjoinRoot.of (ltEisB π B m) ((⇑φ)^[k] b) := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, twistFrob_of, ih, ← Function.iterate_succ_apply]

theorem repr_twistFrob_iterate {N : ℕ} (hN : (twistFrob hπ hunr m φ u)^[N] (AdjoinRoot.root (ltEisB π B m)) =
      AdjoinRoot.root (ltEisB π B m))
    (z : AdjoinRoot (ltEisB π B m)) (i : Fin (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).dim) :
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr
        ((twistFrob hπ hunr m φ u)^[N] z) i =
      (⇑φ)^[N] ((AdjoinRoot.powerBasis' (monic_ltEisB π B m)).basis.repr z i) := by
  have hTc : ⇑(twistFrob hπ hunr m φ u ^ N) = (twistFrob hπ hunr m φ u)^[N] := RingHom.coe_pow _ N
  have h := repr_ringHom_eq (twistFrob hπ hunr m φ u ^ N) ((⇑φ)^[N])
    (fun b => by rw [hTc, twistFrob_iterate_of]) (by rw [hTc, hN])
    (AdjoinRoot.powerBasis' (monic_ltEisB π B m)) (AdjoinRoot.powerBasis'_gen _) z i
  rwa [hTc] at h

end Twist

section Theta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π)
  {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (maximalIdeal B) B] [IsAlgClosed (ResidueField B)]
  (hunr : (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] B) = maximalIdeal B) (m : ℕ)
  (φ : B →ₐ[𝒪[K]] B) (hφ : ∀ x : B, residue B (φ x) = residue B x ^ Nat.card 𝓀[K])
  (u : 𝒪[K]ˣ)

include hφ in

theorem exists_twistFrob_fixed_root :
    ∃ x : AdjoinRoot (ltEisB π B m), twistFrob hπ hunr m φ u x = x ∧
      Polynomial.aeval x (ltEisB ((u : 𝒪[K]) * π) B m) = 0 := by
  have hπ' : Irreducible ((u : 𝒪[K]) * π) := (irreducible_units_mul u).2 hπ
  obtain ⟨θ, hθ1, -, hθφ, hθcomm, -⟩ := exists_iso_lubinTateFormalGroup hunr φ hφ hπ u
    (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly ((u : 𝒪[K]) * π))
  set t := θ.hom.toPowerSeries with ht
  have ht0 : constantCoeff t = 0 := θ.hom.constantCoeff_eq_zero
  have hmap : PowerSeries.map (φ : B →+* B) t = subst (ltSeries hπ B (u : 𝒪[K])) t := hθφ
  have hcomm : ∀ a : 𝒪[K], (subst (ltSeries hπ B a) t : B⟦X⟧) = subst t (ltSeries hπ' B a) :=
    fun a => congrArg Hom.toPowerSeries (hθcomm a)
  have hs : ∀ a : 𝒪[K], HasSubst (ltSeries hπ B a) := fun a =>
    HasSubst.of_constantCoeff_zero' (constantCoeff_ltSeries hπ a)
  have hsub0 : ∀ a : 𝒪[K], constantCoeff (subst (ltSeries hπ B a) t : B⟦X⟧) = 0 := fun a => by
    rw [constantCoeff_subst_of_constantCoeff_eq_zero (constantCoeff_ltSeries hπ a), ht0]

  have hval : ∀ k : ℕ, Polynomial.aeval (rootEval (isDistinguishedAt_ltEisB hπ hunr m) t)
      ((ltPolyIter ((u : 𝒪[K]) * π) k).map (algebraMap 𝒪[K] B)) =
      rootEval (isDistinguishedAt_ltEisB hπ hunr m)
        (subst (ltSeries hπ B (π ^ k)) (subst (ltSeries hπ B ((u : 𝒪[K]) ^ k)) t)) := by
    intro k
    rw [← rootEval_subst_coe _ ht0, ← ltSeries_uniformizer_pow hπ', ← hcomm, mul_pow,
      ← subst_ltSeries, subst_comp_subst_apply (hs _) (hs _)]
  refine ⟨rootEval (isDistinguishedAt_ltEisB hπ hunr m) t, ?_, ?_⟩
  · rw [twistFrob_rootEval, hmap, subst_comp_subst_apply (hs _) (hs _), subst_ltSeries,
      Units.mul_inv, ltSeries_one, X_subst]
  · have h1 := hval (m + 1)
    rw [rootEval_subst_ltSeries_uniformizer_pow_succ hπ hunr m (hsub0 _), ltPolyIter_succ_eq_mul,
      Polynomial.map_mul, map_mul, hval m] at h1
    refine eq_zero_of_rootEval_subst_mul hπ hunr m (hsub0 _) ?_ h1
    rw [coeff_one_subst ht0 (constantCoeff_ltSeries hπ _), coeff_one_ltSeries]
    exact hθ1.mul ((u.isUnit.pow m).map _)

end Theta

end GroundTheory.LocalField
