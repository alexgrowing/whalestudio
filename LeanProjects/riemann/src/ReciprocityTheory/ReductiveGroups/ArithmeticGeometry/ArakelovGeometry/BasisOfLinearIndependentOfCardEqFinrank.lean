import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjectiveFrameCoordNeZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem closure_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (m : Ω)
    (hm : m ∈ Submonoid.closure (Set.range fun i => x i / x (e 0))) :
    ∃ d, ∃ s ∈ sec ℤ x d, m = s / x (e 0) ^ d := by
  induction hm using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨1, x i, ?_, by rw [pow_one]⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨MvPolynomial.X i,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X ℤ i), by simp⟩
  | one =>
    refine ⟨0, 1, ?_, by simp⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨1,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_one κ ℤ), by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨d1, s1, hs1, rfl⟩ := ha
    obtain ⟨d2, s2, hs2, rfl⟩ := hb
    unfold sec at hs1 hs2
    obtain ⟨p1, hp1, rfl⟩ := Submodule.mem_map.1 hs1
    obtain ⟨p2, hp2, rfl⟩ := Submodule.mem_map.1 hs2
    refine ⟨d1 + d2, (MvPolynomial.aeval x).toLinearMap (p1 * p2), ?_, ?_⟩
    · unfold sec
      exact Submodule.mem_map.2 ⟨p1 * p2, (MvPolynomial.mem_homogeneousSubmodule _ _).2
        (((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp1).mul
          ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp2)), rfl⟩
    · simp only [AlgHom.toLinearMap_apply, map_mul]
      rw [div_mul_div_comm, pow_add]

private theorem gens_lemma_2 [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    (∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0))) ∧
      IntermediateField.extendScalars (fnField_comp_le' x e) =
        IntermediateField.adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  classical
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk
  have hgen : ∀ k, x (e k) / x (e 0) ∈ fnField (x ∘ e) := fun k => div_mem_fnField (x ∘ e) k 0
  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℚ,
      Polynomial.evalRingHom (x (e 0))⁻¹ (coneMap ℚ (x ∘ e) q) ∈ fnField (x ∘ e) := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C]
      first
        | (rw [Polynomial.algebraMap_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
           exact IntermediateField.algebraMap_mem _ a)
        | simpa using IntermediateField.algebraMap_mem (fnField (x ∘ e)) a
    next p1 p2 h1 h2 =>
      rw [map_add, map_add]
      exact add_mem h1 h2
    next p1 k h1 =>
      rw [map_mul, map_mul]
      refine mul_mem h1 ?_
      unfold coneMap
      rw [MvPolynomial.aeval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Function.comp_apply]
      rw [← div_eq_mul_inv]
      exact hgen k
  have hmem : ∀ v : coneRing ℚ (x ∘ e),
      ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom) v ∈
        fnField (x ∘ e) := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℚ (x ∘ e) →+* fnField (x ∘ e) :=
    ((Polynomial.evalRingHom (x (e 0))⁻¹).comp (coneRing ℚ (x ∘ e)).val.toRingHom).codRestrict
      (fnField (x ∘ e)) hmem
  have hint : ∀ i, IsIntegral (fnField (x ∘ e)) (x i / x (e 0)) := by
    intro i
    obtain ⟨p, hm, hp⟩ := h.integral i
    refine ⟨p.map φ, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (fnField (x ∘ e)) Ω).comp φ =
        (Polynomial.evalRingHom (x (e 0))⁻¹).comp
          (algebraMap (coneRing ℚ (x ∘ e)) (Polynomial Ω)) := RingHom.ext fun _ => rfl
    have hpt : x i / x (e 0) =
        Polynomial.evalRingHom (x (e 0))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
      simp [div_eq_mul_inv]
    rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]
  let S : Set Ω := Set.range fun i => x i / x (e 0)
  have heq : IntermediateField.extendScalars (fnField_comp_le' x e) =
      IntermediateField.adjoin (fnField (x ∘ e)) S := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ fnField x := (IntermediateField.mem_extendScalars _).1 hz
      have hle : IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j} ≤
          (IntermediateField.adjoin (fnField (x ∘ e)) S).restrictScalars ℚ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨i, j, rfl⟩
        have h3 : x i / x j = x i / x (e 0) / (x j / x (e 0)) := by
          first
            | rw [div_div_div_cancel_right₀ hne]
            | field_simp
        show x i / x j ∈ IntermediateField.adjoin (fnField (x ∘ e)) S
        rw [h3]
        have hi : x i / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
        have hj : x j / x (e 0) ∈ IntermediateField.adjoin (fnField (x ∘ e)) S :=
          IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
        exact div_mem hi hj
      exact hle hz'
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact (IntermediateField.mem_extendScalars _).2 (div_mem_fnField x i (e 0))
  exact ⟨hint, heq⟩

private theorem finrat_lemma [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  rw [heq]
  exact IntermediateField.finiteDimensional_adjoin fun z hz => by
    obtain ⟨i, rfl⟩ := hz
    exact hint i

theorem exists_indep_sections' [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ)
    (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  classical
  obtain ⟨hint, heq⟩ := gens_lemma_2 x e h
  haveI := finrat_lemma x e h
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk

  let T : Set Ω := Submonoid.closure (Set.range fun i => x i / x (e 0))
  have hTL : ∀ z ∈ T, z ∈ IntermediateField.extendScalars (fnField_comp_le' x e) := by
    intro z hz
    obtain ⟨d, σ, hσ, rfl⟩ := closure_mem x e z hz
    exact sec_div_mem x (e 0) hσ
  let s : Set (IntermediateField.extendScalars (fnField_comp_le' x e)) := {z | (z : Ω) ∈ T}
  have hspanΩ : ∀ z ∈ IntermediateField.extendScalars (fnField_comp_le' x e),
      z ∈ Submodule.span (fnField (x ∘ e)) T := by
    intro z hz
    rw [heq] at hz
    have h1 : z ∈ (IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))).toSubalgebra := hz
    have hSi : ∀ w ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) w := by
      rintro w ⟨i, rfl⟩
      exact hint i
    first
      | rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_toSubalgebra_of_isIntegral hSi] at h1
      | rw [IntermediateField.adjoin_algebraic_toSubalgebra (fun w hw => (hSi w hw).isAlgebraic)] at h1
      | rw [IntermediateField.adjoin_integral_toSubalgebra hSi] at h1
    have h2 : z ∈ Subalgebra.toSubmodule (Algebra.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))) := h1
    rwa [Algebra.adjoin_eq_span] at h2
  have hspan : Submodule.span (fnField (x ∘ e)) s = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have h1 := hspanΩ z z.2
    have h2 : Submodule.span (fnField (x ∘ e)) T = (Submodule.span (fnField (x ∘ e)) s).map
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext w
      constructor
      · intro hw
        exact ⟨⟨w, hTL w hw⟩, hw, rfl⟩
      · rintro ⟨w', hw', rfl⟩
        exact hw'
    rw [h2] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    have hwz' : w = z := Subtype.ext hwz
    rwa [← hwz']
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (fnField (x ∘ e)) s
  have hbtop : ⊤ ≤ Submodule.span (fnField (x ∘ e))
      (Set.range (Subtype.val : b → IntermediateField.extendScalars (fnField_comp_le' x e))) := by
    first
      | rw [Subtype.range_coe, hbspan, hspan]
      | rw [Subtype.range_val, hbspan, hspan]
  let B := Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis B
  haveI : Fintype b := Fintype.ofFinite b
  have hpd : projDeg x e = Module.finrank (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    unfold projDeg
    first
      | exact IntermediateField.relfinrank_eq_finrank_of_le (fnField_comp_le' x e)
      | rfl
  have hcard : Fintype.card b = projDeg x e := by
    rw [hpd, Module.finrank_eq_card_basis B]
  let eqv : Fin (projDeg x e) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hdec : ∀ j, ∃ d, ∃ σ ∈ sec ℤ x d, (((eqv j : b) : IntermediateField.extendScalars
      (fnField_comp_le' x e)) : Ω) = σ / x (e 0) ^ d :=
    fun j => closure_mem x e _ (hbs (eqv j).2)
  choose d σ hσ hdeq using hdec
  obtain ⟨k, hk⟩ : ∃ k, k = Finset.univ.sup d := ⟨_, rfl⟩
  have hdk : ∀ j, d j ≤ k := fun j => hk ▸ Finset.le_sup (Finset.mem_univ j)
  refine ⟨k, fun j => σ j * x (e 0) ^ (k - d j), fun j => ?_, ?_⟩
  · obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 (hσ j)
    refine Submodule.mem_map.2 ⟨p * MvPolynomial.X (e 0) ^ (k - d j), ?_, ?_⟩
    · have h3 := ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp).mul
        ((MvPolynomial.isHomogeneous_X ℤ (e 0)).pow (k - d j))
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [Nat.add_sub_of_le (hdk j)] using h3
    · show (MvPolynomial.aeval x).toLinearMap (p * MvPolynomial.X (e 0) ^ (k - d j)) =
        σ j * x (e 0) ^ (k - d j)
      rw [← hps]
      simp
  · have hli1 : LinearIndependent (fnField (x ∘ e))
        (fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) :=
      (hbli.comp eqv eqv.injective).map'
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    have hli2 := hli1.map' (LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (pow_ne_zero k hne)))
    have hfun : (⇑(LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k)) ∘
        fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) =
        fun j => σ j * x (e 0) ^ (k - d j) := by
      funext j
      simp only [Function.comp_apply, LinearMap.mulRight_apply, hdeq j]
      have hk' : x (e 0) ^ k = x (e 0) ^ d j * x (e 0) ^ (k - d j) := by
        rw [← pow_add, Nat.add_sub_of_le (hdk j)]
      rw [hk']
      have hc := pow_ne_zero (d j) hne
      field_simp
      try ring
    rw [hfun] at hli2
    exact hli2

theorem eq_zero_of_trace [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε)
    (t : IntermediateField.extendScalars (fnField_comp_le' x e))
    (h0 : ∀ l, Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      (t * ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩) = 0) : t = 0 := by
  classical
  haveI := finrat_lemma x e h
  have hne : x (e 0) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X 0 ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero 0 hk
  let b : Fin (projDeg x e) → IntermediateField.extendScalars (fnField_comp_le' x e) :=
    fun j => ⟨ε j / x (e 0) ^ k, sec_div_mem x (e 0) (hε j)⟩
  have hb : LinearIndependent (fnField (x ∘ e)) b := by
    apply LinearIndependent.of_comp (IntermediateField.val _).toLinearMap
    have h2 := hli.map' (LinearMap.mulRight (fnField (x ∘ e)) ((x (e 0) ^ k)⁻¹))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero (pow_ne_zero k hne))))
    have h3 : (⇑(IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap ∘ b) =
        ⇑(LinearMap.mulRight (fnField (x ∘ e)) ((x (e 0) ^ k)⁻¹)) ∘ ε := by
      funext j
      exact div_eq_mul_inv _ _
    rw [h3]
    exact h2
  have hrank : Fintype.card (Fin (projDeg x e)) = Module.finrank (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    rw [Fintype.card_fin]
    unfold projDeg
    first
      | exact IntermediateField.relfinrank_eq_finrank_of_le (fnField_comp_le' x e)
      | rfl
  haveI : Nonempty (Fin (projDeg x e)) := ⟨⟨0, by
    have h4 := hrank
    rw [Fintype.card_fin] at h4
    rw [h4]
    first
      | exact Module.finrank_pos
      | exact FiniteDimensional.finrank_pos⟩⟩
  obtain ⟨B, hB⟩ : ∃ B : Basis (Fin (projDeg x e)) (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)),
      ∀ j, B j = ⟨ε j / x (e 0) ^ k, sec_div_mem x (e 0) (hε j)⟩ :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hb hrank, fun j => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩
  have hnd : (Algebra.traceForm (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))).Nondegenerate := by
    first
      | exact traceForm_nondegenerate _ _
      | exact Algebra.traceForm_nondegenerate _ _
  have key : ∀ n, Algebra.traceForm (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e)) t n = 0 := by
    intro n
    rw [Algebra.traceForm_apply, ← B.sum_repr n, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, hB j, h0 j, smul_zero]
  first
    | exact hnd t key
    | exact hnd.1 t key
    | exact hnd.1.1 t key
    | (unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate LinearMap.SeparatingLeft at hnd
       exact hnd.1 t key)

theorem isRat_of_isProj (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    IsRatProjFrame x e := by
  refine ⟨h.inj, h.free, fun i => ?_⟩
  have hmem : ∀ v ∈ coneRing ℤ (x ∘ e), v ∈ coneRing ℚ (x ∘ e) := by
    rintro v ⟨q, rfl⟩
    refine ⟨MvPolynomial.map (algebraMap ℤ ℚ) q, ?_⟩
    unfold coneMap
    exact MvPolynomial.aeval_map_algebraMap ℚ _ _
  let φ : coneRing ℤ (x ∘ e) →+* coneRing ℚ (x ∘ e) :=
    { toFun := fun s => ⟨s.1, hmem s.1 s.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  obtain ⟨p, hm, hp⟩ := h.integral i
  refine ⟨p.map φ, hm.map _, ?_⟩
  have hc : (algebraMap (coneRing ℚ (x ∘ e)) (Polynomial Ω)).comp φ =
      algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω) := RingHom.ext fun _ => rfl
  rw [Polynomial.eval₂_map, hc]
  exact hp

def chartGen (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (k : {k // k ≠ l}) :
    fnField (x ∘ e) :=
  ⟨x (e k) / x (e l), div_mem_fnField (x ∘ e) k l⟩

def chartRing (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) : Subalgebra ℤ (fnField (x ∘ e)) :=
  Algebra.adjoin ℤ (Set.range (chartGen x e l))

theorem chartGen_indep (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : AlgebraicIndependent ℤ (chartGen x e l) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk

  have hdehom : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) F =
        MvPolynomial.aeval (x ∘ e) F / x (e l) ^ n := by
    intro F n hF
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]

  have hform : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      coneMap ℤ (x ∘ e) F = Polynomial.C (MvPolynomial.aeval (x ∘ e) F) * Polynomial.X ^ n := by
    intro F n hF
    unfold coneMap
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hF (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [← hdeg]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast, map_mul,
      map_prod, map_pow, map_intCast]
    ring
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have hPΩ : MvPolynomial.aeval (fun k : {k // k ≠ l} => x (e k) / x (e l)) P = 0 := by
    have h1 := congrArg ((fnField (x ∘ e)).val.restrictScalars ℤ) hP
    rw [map_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    exact h1
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = MvPolynomial.rename (Subtype.val : {k // k ≠ l} → Fin (D + 1)) P :=
    ⟨_, rfl⟩

  obtain ⟨H, hH⟩ : ∃ H : MvPolynomial (Fin (D + 1)) ℤ, H = ∑ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.homogeneousComponent n Q * MvPolynomial.X l ^ (Q.totalDegree - n) := ⟨_, rfl⟩
  have hHhom : H.IsHomogeneous Q.totalDegree := by
    rw [hH]
    apply MvPolynomial.IsHomogeneous.sum
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have h2 := (MvPolynomial.homogeneousComponent_isHomogeneous n Q).mul
      ((MvPolynomial.isHomogeneous_X ℤ l).pow (Q.totalDegree - n))
    simpa [Nat.add_sub_of_le hn'] using h2
  have hterm : ∀ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.aeval (x ∘ e) (MvPolynomial.homogeneousComponent n Q *
        MvPolynomial.X l ^ (Q.totalDegree - n)) =
      x (e l) ^ Q.totalDegree *
        MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) (MvPolynomial.homogeneousComponent n Q) := by
    intro n hn
    have hn' : n ≤ Q.totalDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [map_mul, map_pow, MvPolynomial.aeval_X,
      hdehom _ n (MvPolynomial.homogeneousComponent_isHomogeneous n Q)]
    conv_rhs => rw [← Nat.add_sub_of_le hn', pow_add]
    have hc := pow_ne_zero n hne
    simp only [Function.comp_apply]
    field_simp
    try ring
  have hHy : MvPolynomial.aeval (x ∘ e) H = 0 := by
    rw [hH, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      MvPolynomial.sum_homogeneousComponent, hQ, MvPolynomial.aeval_rename]
    have h3 : MvPolynomial.aeval ((fun i => (x ∘ e) i / x (e l)) ∘ Subtype.val) P = 0 := hPΩ
    rw [h3, mul_zero]
  have hH0 : H = 0 := by
    have hc : coneMap ℤ (x ∘ e) H = 0 := by
      rw [hform H _ hHhom, hHy, map_zero, zero_mul]
    have hk : H ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      exact hc
    rw [hfree, Ideal.mem_bot] at hk
    exact hk

  have hψ : (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k).comp (MvPolynomial.rename Subtype.val) =
      MvPolynomial.rename (R := ℤ) (Subtype.val : {k // k ≠ l} → Fin (D + 1)) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp [k.2]
  have hQ0 : Q = 0 := by
    have h4 := congrArg (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k) hH0
    rw [hH, map_sum, map_zero] at h4
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, ↓reduceIte, one_pow, mul_one] at h4
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hQ, ← AlgHom.comp_apply, hψ] at h4
    rw [hQ]
    exact h4
  rw [hQ] at hQ0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (hQ0.trans (map_zero _).symm)

theorem chartRing_closed (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsIntegrallyClosed (chartRing x e l) := by
  unfold chartRing
  haveI : UniqueFactorizationMonoid (Algebra.adjoin ℤ (Set.range (chartGen x e l))) :=
    (chartGen_indep x e hfree l).aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsFractionRing (chartRing x e l) (fnField (x ∘ e)) := by
  classical

  have hne : ∀ i, x (e i) ≠ 0 := by
    intro i hi
    have hk : MvPolynomial.X i ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [hfree, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero i hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hR : ∀ w ∈ R, ∃ a : chartRing x e l, ((a : fnField (x ∘ e)) : Ω) = w := by
    rintro w ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  let T : Set Ω := Set.range fun k : {k // k ≠ l} => x (e k) / x (e l)
  have hTR : Subring.closure T ≤ R := by
    rw [Subring.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨chartGen x e l k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩
  let F : IntermediateField ℚ Ω := (Subfield.closure T).toIntermediateField (fun q => by
    rw [eq_ratCast]
    exact SubfieldClass.ratCast_mem _ q)
  have hgen : ∀ i, x (e i) / x (e l) ∈ Subfield.closure T := by
    intro i
    by_cases h : i = l
    · subst h
      rw [div_self (hne i)]
      exact one_mem _
    · exact Subfield.subset_closure ⟨⟨i, h⟩, rfl⟩
  have hle : fnField (x ∘ e) ≤ F := by
    unfold fnField
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, j, rfl⟩
    have h3 : (x ∘ e) i / (x ∘ e) j = x (e i) / x (e l) / (x (e j) / x (e l)) := by
      simp only [Function.comp_apply]
      first
        | rw [div_div_div_cancel_right₀ (hne l)]
        | field_simp
    show _ ∈ Subfield.closure T
    rw [h3]
    exact div_mem (hgen i) (hgen j)
  have hsurj : ∀ z : fnField (x ∘ e), ∃ a b : chartRing x e l, b ≠ 0 ∧
      z * (b : fnField (x ∘ e)) = a := by
    intro z
    have hz : (z : Ω) ∈ Subfield.closure T := hle z.2
    obtain ⟨p, hp, q, hq, hpq⟩ := Subfield.mem_closure_iff.1 hz
    obtain ⟨a, ha⟩ := hR p (hTR hp)
    obtain ⟨b, hb⟩ := hR q (hTR hq)
    by_cases hq0 : q = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      apply Subtype.ext
      simp [← hpq, hq0]
    · refine ⟨a, b, ?_, ?_⟩
      · intro hb0
        apply hq0
        simp [← hb, hb0]
      · apply Subtype.ext
        show (z : Ω) * ((b : fnField (x ∘ e)) : Ω) = ((a : fnField (x ∘ e)) : Ω)
        rw [ha, hb, ← hpq, div_mul_cancel₀ _ hq0]
  have hinj : Function.Injective (algebraMap (chartRing x e l) (fnField (x ∘ e))) :=
    Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb))
  · intro z
    obtain ⟨a, b, hb, h⟩ := hsurj z
    exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩⟩, h⟩
  · intro a b h
    exact ⟨1, by simp [hinj h]⟩

theorem coord_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (i : κ) : IsIntegral (chartRing x e l) (x i / x (e l)) := by
  classical
  have hne : x (e l) ≠ 0 := by
    intro hi
    have hk : MvPolynomial.X l ∈ coordIdeal ℤ (x ∘ e) := by
      unfold coordIdeal
      rw [RingHom.mem_ker]
      unfold coneMap
      simp [hi]
    rw [h.free, Ideal.mem_bot] at hk
    exact MvPolynomial.X_ne_zero l hk
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  have hgen : ∀ k, x (e k) / x (e l) ∈ R := by
    intro k
    by_cases hk : k = l
    · subst hk
      rw [div_self hne]
      exact one_mem _
    · exact ⟨chartGen x e l ⟨k, hk⟩, Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩, rfl⟩

  have hcone : ∀ q : MvPolynomial (Fin (D + 1)) ℤ,
      Polynomial.evalRingHom (x (e l))⁻¹ (coneMap ℤ (x ∘ e) q) ∈ R := by
    intro q
    induction q using MvPolynomial.induction_on
    next a =>
      unfold coneMap
      rw [MvPolynomial.aeval_C, eq_intCast, map_intCast]
      exact intCast_mem R a
    next p1 p2 h1 h2 =>
      rw [map_add, map_add]
      exact add_mem h1 h2
    next p1 k h1 =>
      rw [map_mul, map_mul]
      refine mul_mem h1 ?_
      unfold coneMap
      rw [MvPolynomial.aeval_X]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Function.comp_apply]
      rw [← div_eq_mul_inv]
      exact hgen k
  have hmem : ∀ v : coneRing ℤ (x ∘ e),
      ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom) v ∈ R := by
    rintro ⟨v, q, rfl⟩
    exact hcone q
  let φ : coneRing ℤ (x ∘ e) →+* R :=
    ((Polynomial.evalRingHom (x (e l))⁻¹).comp (coneRing ℤ (x ∘ e)).val.toRingHom).codRestrict R hmem
  let eqv : (chartRing x e l).toSubring ≃+* R :=
    Subring.equivMapOfInjective _ _ (fun a b hab => Subtype.ext hab)
  let ψ : R →+* chartRing x e l := eqv.symm.toRingHom
  obtain ⟨p, hm, hp⟩ := h.integral i
  refine ⟨(p.map φ).map ψ, (hm.map _).map _, ?_⟩
  rw [Polynomial.eval₂_map, Polynomial.eval₂_map]
  have hcomp : ((algebraMap (chartRing x e l) Ω).comp ψ).comp φ =
      (Polynomial.evalRingHom (x (e l))⁻¹).comp (algebraMap (coneRing ℤ (x ∘ e)) (Polynomial Ω)) := by
    refine RingHom.ext fun v => ?_
    have h2 := congrArg Subtype.val (eqv.apply_symm_apply (φ v))
    first
      | exact h2
      | (simp only [eqv, Subring.coe_equivMapOfInjective_apply] at h2; exact h2)
  have hpt : x i / x (e l) = Polynomial.evalRingHom (x (e l))⁻¹ (Polynomial.C (x i) * Polynomial.X) := by
    simp [div_eq_mul_inv]
  rw [hcomp, hpt, ← Polynomial.hom_eval₂, hp, map_zero]

theorem sec_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) [Fintype κ] (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    IsIntegral (chartRing x e l) (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ :
      IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  classical
  obtain ⟨p, hp, hps⟩ := Submodule.mem_map.1 hs
  have hph : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).1 hp

  have hhom : MvPolynomial.aeval (fun i => x i / x (e l)) p = s / x (e l) ^ n := by
    rw [← hps]
    show MvPolynomial.aeval (fun i => x i / x (e l)) p = MvPolynomial.aeval x p / x (e l) ^ n
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', Finset.sum_div]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := hph (MvPolynomial.mem_support_iff.1 hd)
    have hdeg : ∑ i, d i = n := by
      rw [← h1]
      first
        | simp [Finsupp.weight_apply, Finsupp.sum_fintype]
        | simp [Finsupp.degree_eq_sum]
        | exact (Finsupp.sum_fintype _ _ (by simp)).symm
        | simp [Finsupp.degree, Finsupp.sum_fintype]
    rw [mul_div_assoc]
    congr 1
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  have hΩ : IsIntegral (chartRing x e l) (s / x (e l) ^ n) := by
    let S := (integralClosure (chartRing x e l) Ω).restrictScalars ℤ
    have hy : ∀ i, x i / x (e l) ∈ S := fun i => coord_div_isIntegral x e h l i
    let y' : κ → S := fun i => ⟨x i / x (e l), hy i⟩
    have hS : MvPolynomial.aeval (fun i => x i / x (e l)) p = S.val (MvPolynomial.aeval y' p) := by
      first
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl)
        | (rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval])
        | exact (DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℤ) S.val) p).symm
    rw [← hhom, hS]
    exact (MvPolynomial.aeval y' p).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (chartRing x e l)
    (IntermediateField.extendScalars (fnField_comp_le' x e)) Ω)
    (fun a b hab => Subtype.ext hab)).1 hΩ

theorem trace_mem_chart [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ ∈ chartRing x e l := by
  have hi := sec_div_isIntegral x e h l n hs
  haveI := chartRing_frac x e h.free l
  haveI := chartRing_closed x e h.free l
  by_cases hfd : FiniteDimensional (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
  · haveI := hfd
    have ht := Algebra.isIntegral_trace (L := fnField (x ∘ e)) hi
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := fnField (x ∘ e))).1 ht
    rw [← hy]
    exact y.2
  · have hnb : ¬∃ s : Finset (IntermediateField.extendScalars (fnField_comp_le' x e)),
        Nonempty (Basis s (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))) := by
      rintro ⟨s, ⟨b⟩⟩
      first
        | exact hfd (FiniteDimensional.of_fintype_basis b)
        | exact hfd (Module.Finite.of_basis b)
    have h0 : Algebra.trace (fnField (x ∘ e))
        (IntermediateField.extendScalars (fnField_comp_le' x e)) = 0 := by
      first
        | exact Algebra.trace_eq_zero_of_not_exists_basis _ hnb
        | exact Algebra.trace_eq_zero_of_not_exists_basis hnb
    rw [h0, LinearMap.zero_apply]
    exact zero_mem _

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
