import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private theorem norm_one {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have := (Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le
  have h2 := (Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge
  exact le_antisymm this h2

private theorem fin_supp (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (norm_one (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

private theorem absF_mul (y z : (Af F)ˣ) : absF (y * z) = absF y * absF z := by
  unfold absF
  rw [← finprod_mul_distrib (fin_supp y) (fin_supp z)]
  simp

private theorem absF_pos (y : (Af F)ˣ) : 0 < absF y :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w =>
    norm_pos_iff.2 (y.isUnit.map (pLoc F w)).ne_zero

private theorem ordI_mul (v : Pl F) {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : ordI v (I * J) = ordI v I + ordI v J := by
  unfold ordI
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.2 hI) (Associates.mk_ne_zero.2 hJ) v.associates_irreducible]

private theorem ordI_self (w : Pl F) : ordI w w.asIdeal = 1 := Associates.count_self w.associates_irreducible

private theorem ordI_ne {v w : Pl F} (h : v ≠ w) : ordI v w.asIdeal = 0 :=
  Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible fun e =>
    h (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))

private theorem ordI_inj {I J : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (h : ∀ v : Pl F, ordI v I = ordI v J) : I = J := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI, ← Ideal.finprod_heightOneSpectrum_factorization hJ]
  exact finprod_congr fun v => congrArg (v.asIdeal ^ ·) (h v)

private theorem genD_uniq {y : Af F} {I J : Ideal (𝓞 F)} (hI : GenD y I) (hJ : GenD y J) : I = J :=
  ordI_inj hI.1 hJ.1 fun v => by
    have := WithZero.exp_inj.1 ((hI.2 v).symm.trans (hJ.2 v))
    omega

private theorem coefAt_eq (c : Ideal (𝓞 F) → ℂ) {y : Af F} {I : Ideal (𝓞 F)} (h : GenD y I) : coefAt c y = c I := by
  have e : ∃ 𝔪, GenD y 𝔪 := ⟨I, h⟩
  rw [coefAt, dif_pos e, genD_uniq e.choose_spec h]

private theorem genD_shift {w : Pl F} {u : Af F} (hu : ∀ v, Valued.v (pLoc F v u) = WithZero.exp (ordI v w.asIdeal : ℤ))
    (y : Af F) (I : Ideal (𝓞 F)) : GenD (y * u) I ↔ GenD y (w.asIdeal * I) := by
  by_cases hI : I = ⊥
  · simp [GenD, hI]
  refine and_congr (by simp [hI, w.ne_bot]) (forall_congr' fun v => ?_)
  rw [map_mul, map_mul, hu, ordI_mul v w.ne_bot hI, ← eq_div_iff WithZero.exp_ne_zero, ← WithZero.exp_sub]
  push_cast
  ring_nf

private theorem coefAt_shift {w : Pl F} {u : Af F} (hu : ∀ v, Valued.v (pLoc F v u) = WithZero.exp (ordI v w.asIdeal : ℤ))
    (a : Ideal (𝓞 F) → ℂ) (y : Af F) : coefAt (coefDiv a w.asIdeal) y = coefAt a (y * u) := by
  by_cases h : ∃ I, GenD (y * u) I
  · obtain ⟨I, hI⟩ := h
    have e : ∃ 𝔫, w.asIdeal * I = w.asIdeal * 𝔫 := ⟨I, rfl⟩
    rw [coefAt_eq a hI, coefAt_eq _ ((genD_shift hu y I).1 hI), coefDiv, dif_pos e,
      ← mul_left_cancel₀ w.ne_bot e.choose_spec]
  · rw [coefAt.eq_1 a, dif_neg h]
    by_cases h' : ∃ J, GenD y J
    · obtain ⟨J, hJ⟩ := h'
      rw [coefAt_eq _ hJ, coefDiv, dif_neg]
      rintro ⟨I, rfl⟩
      exact h ⟨I, (genD_shift hu y I).2 hJ⟩
    · rw [coefAt, dif_neg h']

private theorem max_eq {w : Pl F} (π : w.adicCompletionIntegers F)
    (hπ : Valued.v (π : w.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) = Ideal.span {π} := by
  ext y
  rw [Ideal.mem_span_singleton, (HeightOneSpectrum.adicCompletionIntegers.integers F w).dvd_iff_le,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion F) = 1 ↔ Valued.v (y : w.adicCompletion F) ≤ Valued.v (π : w.adicCompletion F)
  rw [hπ]
  have hy : Valued.v (y : w.adicCompletion F) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion F) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega

private theorem mem_mirab_quot {R : Type} [CommRing R] (I : Ideal R) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g ∈ mirab (R ⧸ I) ↔ g 1 0 ∈ I ∧ g 1 1 - 1 ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq]
  change _ = _ ↔ _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct]

private theorem K1_conj (w : Pl F) (c : ℕ) (ϖ : (w.adicCompletion F)ˣ) (hϖ : IsUnifAt w ϖ)
    {k : GL (Fin 2) (w.adicCompletion F)} (hk : k ∈ K1 w (c + 1)) :
    ∃ k' ∈ K1 w c, k * aff ϖ⁻¹ 0 = aff ϖ⁻¹ 0 * k' := by
  obtain ⟨g, hg, rfl⟩ := hk
  have hϖ' : Valued.v (ϖ : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := hϖ
  let π : w.adicCompletionIntegers F := ⟨ϖ, by
    change Valued.v (ϖ : w.adicCompletion F) ≤ 1
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; omega⟩
  have hm := max_eq π hϖ'
  obtain ⟨h0, h1⟩ := (mem_mirab_quot _ g).1 hg
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h0
  obtain ⟨e, he⟩ := h0
  have hd : IsUnit (!![g 0 0, π * g 0 1; π ^ c * e, g 1 1] : Matrix (Fin 2) (Fin 2) _).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two_of]
    convert this using 2
    rw [he]; ring
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.mk'' _ hd, (mem_mirab_quot _ _).2 ⟨?_, Ideal.pow_le_pow_right (Nat.le_succ c) h1⟩, rfl⟩, ?_⟩
  · rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨e, rfl⟩
  · have he' : ((g 1 0 : w.adicCompletionIntegers F) : w.adicCompletion F) = ϖ ^ (c + 1) * e := by rw [he]; rfl
    ext i j : 2
    fin_cases i <;> fin_cases j <;>
      simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, he', π]
    · ring
    · field_simp
      ring

private theorem gl_ext' {g h : GL (Fin 2) (Af F)}
    (e : ∀ w, Matrix.GeneralLinearGroup.map (pLoc F w) g = Matrix.GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin 2) (w.adicCompletion F) => x i j) (e w)

private theorem locGL_comm {v w : Pl F} (h : v ≠ w) (g : GL (Fin 2) (v.adicCompletion F)) (k : GL (Fin 2) (w.adicCompletion F)) :
    locGL F 2 v g * locGL F 2 w k = locGL F 2 w k * locGL F 2 v g := by
  refine gl_ext' fun x => ?_
  rw [map_mul, map_mul]
  by_cases hx : x = v
  · subst hx; rw [pLoc_locGL_of_ne h, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hx, mul_one, one_mul]

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (aff y 0) = aff (Units.map f.toMonoidHom y) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) : aff y (0 : R) * aff z 0 = aff (y * z) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem exists_idele (w : Pl F) (x : (w.adicCompletion F)ˣ) : ∃ u : (Af F)ˣ, pLoc F w u = x ∧
    (∀ v, v ≠ w → pLoc F v u = 1) ∧ locGL F 2 w (aff x 0) = aff u 0 := by
  classical
  let u : (Af F)ˣ := Units.map (corner (sLoc F w)) x
  have h1 : pLoc F w u = x := by
    have h : ∀ y, pLoc F w (sLoc F w y) = y := fun y =>
      Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w y
    change pLoc F w (1 - sLoc F w 1 + sLoc F w x) = x
    simp [h]
  have h2 : ∀ v, v ≠ w → pLoc F v u = 1 := fun v hv => by
    have h : ∀ y, pLoc F v (sLoc F w y) = 0 := fun y =>
      Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) hv y
    change pLoc F v (1 - sLoc F w 1 + sLoc F w x) = 1
    simp [h]
  refine ⟨u, h1, h2, gl_ext' fun v => ?_⟩
  rw [map_aff]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL]
    congr 1
    exact Units.ext h1.symm
  · rw [pLoc_locGL_of_ne hv, ← aff_one]
    congr 1
    exact Units.ext (h2 v hv).symm

variable [IsTotallyReal F]

private theorem lie_fin (X : TR.Lie F 2) (t : GL (Fin 2) (Af F)) (φ : TR.Sm F 2) :
    TR.lie F 2 X (TR.finRep F 2 t φ) = TR.finRep F 2 t (TR.lie F 2 X φ) :=
  LinearMap.congr_fun (TR.lie_rt_fin X t) φ

private theorem zalg_comm (t : GL (Fin 2) (Af F)) {z : Module.End ℂ (TR.Sm F 2)} (hz : z ∈ TR.Zalg F 2) :
    TR.finRep F 2 t * z = z * TR.finRep F 2 t := by
  let S : Subalgebra ℂ (Module.End ℂ (TR.Sm F 2)) := Subalgebra.centralizer ℂ {TR.finRep F 2 t}
  have hE : ∀ τ i j, TR.Eop τ i j ∈ S := fun τ i j => (Subalgebra.mem_centralizer_iff ℂ).2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact (TR.lie_rt_fin _ t).symm
  refine (Subalgebra.mem_centralizer_iff ℂ).1 ((Algebra.adjoin_le (S := S) ?_) hz) _ rfl
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

private theorem aut_fin {φ : TR.Sm F 2} (h : TR.IsAutForm φ) (t : GL (Fin 2) (Af F)) {s : ℂ} (hs : s ≠ 0) :
    TR.IsAutForm (s • TR.finRep F 2 t φ) := by
  have hv : ∀ g, (s • TR.finRep F 2 t φ).1 g = s * φ.1 (g * finGL F 2 t) := fun _ => rfl
  refine ⟨fun γ g => by rw [hv, hv, mul_assoc, h.left], ?_, ?_, ?_, fun g => ?_⟩
  · have e : {k | TR.finRep F 2 k (s • TR.finRep F 2 t φ) = s • TR.finRep F 2 t φ} =
        (fun k => t⁻¹ * k * t) ⁻¹' {k | TR.finRep F 2 k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_smul, map_mul, Module.End.mul_apply]
      rw [(smul_right_injective _ hs).eq_iff]
      constructor
      · intro hk
        rw [hk, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro hk
        conv_rhs => rw [← hk]
        rw [← Module.End.mul_apply (TR.finRep F 2 t), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e]
    exact h.level.preimage (by fun_prop)
  · haveI := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ)).map
      (s • TR.finRep F 2 t)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun g => ?_)⟩
    change s * φ.1 (g * finGL F 2 t * TR.infGL F 2 _) = s * φ.1 (g * TR.infGL F 2 _ * finGL F 2 t)
    rw [mul_assoc, mul_assoc, TR.infGL_comm]
  · haveI := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F 2) => z φ) '' TR.Zalg F 2)).map
      (s • TR.finRep F 2 t)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, map_smul]
    exact congrArg (s • ·) (LinearMap.congr_fun (zalg_comm t hz) φ)
  · obtain ⟨C, N, hC⟩ := h.growth (g * finGL F 2 t)
    refine ⟨‖s‖ * C, N, fun y => ?_⟩
    rw [hv, norm_mul, mul_assoc g, TR.infGL_comm, ← mul_assoc, mul_assoc ‖s‖]
    exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holB :
    UpperTheory.V.Sd.HolB := by
  intro F _ _ _ k c ω φ c₀ a w hφ hE
  classical
  have hϖ := unif_spec w
  set ϖ := atFin w (unif w)
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_idele w ϖ⁻¹
  have hu : ∀ v, Valued.v (pLoc F v (u : Af F)) = WithZero.exp (ordI v w.asIdeal : ℤ) := fun v => by
    by_cases hv : v = w
    · subst hv
      rw [hu1, ordI_self, Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (ϖ : v.adicCompletion F) = _ from hϖ,
        ← WithZero.exp_neg]
      rfl
    · rw [hu2 v hv, ordI_ne hv, map_one]; rfl
  have hp : 0 < absF u ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos (absF_pos u) _
  have hp' : ((absF u ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp.ne'
  set s : ℂ := ((absF u ^ ((k : ℝ) / 2) : ℝ) : ℂ)⁻¹ with hs
  have hv : ∀ g, (s • TR.finRep F 2 (aff u 0) φ).1 g = s * φ.1 (g * finGL F 2 (aff u 0)) := fun _ => rfl
  refine ⟨s • TR.finRep F 2 (aff u 0) φ, u, ⟨aut_fin hφ.aut _ (inv_ne_zero hp'), fun v => ?_, fun z g => ?_, fun v => ?_,
    fun v => ?_⟩, fun x y hy yf => ?_⟩
  · refine Submodule.smul_mem _ _ fun g hg => ?_
    change TR.finRep F 2 (locGL F 2 v g) _ = _
    rw [← Module.End.mul_apply, ← map_mul, ← hu3]
    by_cases hvw : v = w
    · subst hvw
      rw [Function.update_self] at hg
      obtain ⟨g', hg', e⟩ := K1_conj v _ ϖ hϖ hg
      rw [← map_mul, e, map_mul, map_mul, Module.End.mul_apply]
      exact congrArg _ (hφ.level v g' hg')
    · rw [Function.update_of_ne hvw] at hg
      rw [locGL_comm hvw, map_mul, Module.End.mul_apply]
      exact congrArg _ (hφ.level v g hg)
  · rw [hv, hv, mul_assoc, hφ.cent]; ring
  · have := hφ.wt v
    simp only [TR.Eop, map_smul, lie_fin] at this ⊢
    rw [← smul_sub, ← map_sub, this, map_smul, smul_comm]
  · have := hφ.low v
    simp only [TR.Eop, map_smul, lie_fin] at this ⊢
    rw [← smul_sub, ← map_sub, this, map_smul, smul_comm, ← smul_add, ← map_add]
  · have h := hE x y hy (yf * u)
    have hy' : 0 < ∏ v, y.val v := Finset.prod_pos fun v _ => hy v
    convert h using 2
    · rw [coefAt_shift hu, Units.val_mul, mul_assoc (algebraMap F (Af F) _)]
    · rw [hv, mul_assoc, ← map_mul, aff_mul, absF_mul, ← mul_assoc,
        Real.mul_rpow (mul_pos hy' (absF_pos yf)).le (absF_pos u).le, Complex.ofReal_mul, hs]
      rw [mul_comm _ (φ.1 _), ← div_eq_mul_inv, div_div, mul_comm (_ : ℂ)]
