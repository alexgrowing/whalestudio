import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre

noncomputable section

open NumberField MeasureTheory Matrix Polynomial Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspRep.Central
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def HasCuspImage (f : Sm E a) : Prop :=
  ∃ (W : Submodule ℂ (Sm E a)) (τ : CuspSub E a) (p : Sm E a →ₗ[ℂ] τ.V),
    f ∈ W ∧ IsStable W ∧ p f ≠ 0 ∧ ∀ (o : Op E a), ∀ g ∈ W, p (act o g) = τ.op o (p g)

theorem HasCuspImage.of_commute {Q : Module.End ℂ (Sm E a)} (hQ : ∀ o, Commute Q (act o)) {f : Sm E a}
    (h : HasCuspImage (Q f)) : HasCuspImage f := by
  obtain ⟨W, τ, p, h1, h2, h3, h4⟩ := h
  have e : ∀ o g, Q (act o g) = act o (Q g) := fun o g => LinearMap.congr_fun (hQ o).eq g
  refine ⟨W.comap Q, τ, p ∘ₗ Q, h1, fun o g hg => ?_, h3, fun o g hg => ?_⟩
  · change Q _ ∈ W
    rw [e]; exact h2 o _ hg
  · change p (Q _) = _
    rw [e]; exact h4 o _ hg

theorem HasCuspImage.mulChi {f : Sm E a} (h : HasCuspImage f) (χ : HChar E) : HasCuspImage (mulChi a χ f) := by
  obtain ⟨W, τ, p, h1, h2, h3, h4⟩ := h
  refine ⟨W.map (CuspRep.mulChi a χ).toLinearMap, τ.twist χ,
    (τ.toTwist χ).toLinearMap ∘ₗ p ∘ₗ (CuspRep.mulChi a χ).symm.toLinearMap, ⟨f, h1, rfl⟩, ?_, ?_, ?_⟩
  · rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (W.smul_mem _ (h2 o φ hφ)) (W.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  · simpa using h3
  · rintro o _ ⟨φ, hφ, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearMap.comp_apply, act_mulChi, LinearEquiv.symm_apply_apply,
      CuspSub.op_toTwist, map_add p, map_smul p, h4 o φ hφ]

theorem commute_Zalg {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X)) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem isCuspForm_rs_sub {f : Sm E a} (h : IsCuspForm f) (z : (Ad E)ˣ) (c : ℂ) :
    IsCuspForm ((rs a z - algebraMap ℂ _ c) f) := by
  set Q : Module.End ℂ (Sm E a) := rs a z - algebraMap ℂ _ c
  have hQ : ∀ o, Commute Q (act o) := fun o => (rs_act z o).sub_left (Algebra.commutes c _)
  have ev : ∀ g, (Q f).1 g = f.1 (g * GeneralLinearGroup.scalar (Fin a) z) - c * f.1 g := fun g => rfl
  have hc := ContAut.continuous_of_isOpen_stab E a f h.1.level
  refine ⟨⟨fun γ g => by rw [ev, ev, mul_assoc, h.1.left, h.1.left], ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.1.level.mem_nhds (by simp)) fun k hk => ?_)
    exact (LinearMap.congr_fun (hQ (.fin k)).eq f).symm.trans (congrArg Q hk)
  · have := h.1.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k f)).map Q)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, LinearMap.congr_fun (hQ (.cpt k)).eq f⟩
  · have := h.1.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) ''
      Zalg E a)).map Q) (Submodule.span_le.2 ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨y, hy, rfl⟩, LinearMap.congr_fun (commute_Zalg (fun X => hQ (.lie X)) hy).eq f⟩
  · obtain ⟨C, N, h1⟩ := h.1.growth (g * GeneralLinearGroup.scalar (Fin a) z)
    obtain ⟨C', N', h2⟩ := h.1.growth g
    refine ⟨|C| + ‖c‖ * |C'|, N + N', fun y => ?_⟩
    have h0 := one_le_height y
    have e1 : ‖f.1 (g * infGL E a y * GeneralLinearGroup.scalar (Fin a) z)‖ ≤ |C| * height y ^ (N + N') := by
      rw [mul_assoc, ← CuspRep.scalar_comm, ← mul_assoc]
      exact (h1 y).trans (mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h0 (by omega)) (by positivity) (abs_nonneg _))
    have e2 : ‖f.1 (g * infGL E a y)‖ ≤ |C'| * height y ^ (N + N') :=
      (h2 y).trans (mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h0 (by omega)) (by positivity) (abs_nonneg _))
    rw [ev, add_mul, mul_assoc ‖c‖]
    refine (norm_sub_le _ _).trans (add_le_add e1 ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
  · intro r h0 h1 _ _ ν 𝓕 hν h𝓕 g
    simp only [ev, mul_assoc]
    rw [integral_sub (integrableOn_unip hc h.1.left ν h𝓕 _) ((integrableOn_unip hc h.1.left ν h𝓕 _).const_mul c),
      integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕, h.2 r h0 h1 ν 𝓕 hν h𝓕, mul_zero, sub_zero]

abbrev dSplit (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) : Module.End ℂ (Sm E a) :=
  lie E a (scL a 1)

theorem exists_aeval_eq_zero {f : Sm E a} (h : IsAutForm f) : ∃ p : ℂ[X], p ≠ 0 ∧ aeval (dSplit E a) p f = 0 := by
  have := h.zfin
  let L : ℂ[X] →ₗ[ℂ] Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) '' Zalg E a) :=
    LinearMap.codRestrict _ (LinearMap.applyₗ f ∘ₗ (aeval (dSplit E a)).toLinearMap) fun p =>
      Submodule.subset_span ⟨_, (Algebra.adjoin_le (S := Zalg E a) (Set.singleton_subset_iff.2 (lie_mem_Zalg 1)))
        (Polynomial.aeval_mem_adjoin_singleton ℂ _), rfl⟩
  by_contra! hc
  have hi : Function.Injective L := (injective_iff_map_eq_zero L).2 fun p hp => by
    by_contra h0
    exact hc p h0 (congrArg Subtype.val hp)
  exact Polynomial.not_finite (Module.Finite.of_injective L hi)

theorem hasCuspImage_of_eigen (H : ∀ (f : Sm E a) (c : ℂ), IsCuspForm f → f ≠ 0 →
    (∀ (t : ℝ) g, f.1 (splitCentre E a t * g) = Complex.exp (c * t) * f.1 g) → HasCuspImage f)
    {f : Sm E a} (h : IsCuspForm f) (h0 : f ≠ 0) : HasCuspImage f := by
  obtain ⟨p, hp, hf⟩ := exists_aeval_eq_zero h.1
  induction hn : p.natDegree generalizing p f with
  | zero =>
    rw [eq_C_of_natDegree_eq_zero hn] at hp hf
    exact absurd (by simpa using hf) (not_or.2 ⟨by simpa using hp, h0⟩)
  | succ n ih =>
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hc
    have hq : q ≠ 0 := right_ne_zero_of_mul hp
    have hqn : q.natDegree = n := by
      rw [natDegree_mul (X_sub_C_ne_zero c) hq, natDegree_X_sub_C] at hn; omega
    have e1 : dSplit E a (aeval (dSplit E a) q f) = c • aeval (dSplit E a) q f := by
      rw [map_mul, Module.End.mul_apply] at hf
      simpa [sub_eq_zero] using hf
    let Q : ℝ → Module.End ℂ (Sm E a) := fun t =>
      rs a (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) - algebraMap ℂ _ (Complex.exp (c * t))
    have hQ : ∀ t o, Commute (Q t) (act o) := fun t o => (rs_act _ o).sub_left (Algebra.commutes _ _)
    by_cases hz : ∀ t, Q t f = 0
    · refine H f c h h0 fun t g => ?_
      rw [splitCentre_comm, splitCentre_eq_scalar]
      exact sub_eq_zero.1 (congrFun (congrArg Subtype.val (hz t)) g)
    · obtain ⟨t, ht⟩ := not_forall.1 hz
      refine HasCuspImage.of_commute (hQ t) (ih (f := Q t f) (isCuspForm_rs_sub h _ _) ht q hq ?_ hqn)
      have e2 : Commute (Q t) (aeval (dSplit E a) q) := by
        refine commute_Zalg (fun X => hQ t (.lie X)) ?_
        exact (Algebra.adjoin_le (S := Zalg E a) (Set.singleton_subset_iff.2 (lie_mem_Zalg 1)))
          (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      rw [← Module.End.mul_apply, ← e2.eq, Module.End.mul_apply]
      have e3 : scL a (fun _ : InfinitePlace E => (t : ℂ)) = t • scL (E := E) a 1 := by
        ext i j w
        by_cases hij : i = j <;> simp [hij]
      have := rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) (aeval (dSplit E a) q f) (by
        rw [e3, map_smul, LinearMap.smul_apply, e1, mul_comm, mul_smul, Complex.coe_smul])
      exact sub_eq_zero.2 this

variable (E) in

def cpowChar (s : ℂ) : HChar E :=
  ⟨MonoidHom.toHomUnits
      { toFun := fun x => Complex.exp (s * Real.log (ideleNorm (E := E) x))
        map_one' := by simp
        map_mul' := fun x y => by
          rw [map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _), ← Complex.exp_add]
          push_cast; ring_nf },
    Units.isEmbedding_val₀.continuous_iff.2 (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ideleNorm.log fun _ => ideleNorm_ne_zero _)))),
    fun k => Units.ext (by
      have h := ideleNorm_principalIdele (E := E) k
      exact (congrArg (fun r : ℝ => Complex.exp (s * Real.log r)) h).trans (by simp))⟩

theorem exists_chiDet_splitCentre (ha : 0 < a) (c : ℂ) :
    ∃ χ : HChar E, ∀ t : ℝ, ((chiDet a χ (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (c * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨cpowChar E (c / D 1), fun t => ?_⟩
  change Complex.exp (c / D 1 * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

theorem hasCuspImage_of_invariant (H : ∀ f : Sm E a, IsCuspForm f → f ≠ 0 →
    (∀ (t : ℝ) g, f.1 (splitCentre E a t * g) = f.1 g) → HasCuspImage f)
    {f : Sm E a} (h : IsCuspForm f) (h0 : f ≠ 0) : HasCuspImage f := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact H f h h0 fun t g => congrArg f.1 (Subsingleton.elim _ _)
  refine hasCuspImage_of_eigen (fun f c h h0 hc => ?_) h h0
  obtain ⟨χ, hχ⟩ := exists_chiDet_splitCentre (E := E) ha (-c)
  have := (H _ (h.mulChi χ) ((map_ne_zero_iff _ (mulChi a χ).injective).2 h0) fun t g => by
    rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hc, mul_mul_mul_comm, ← Complex.exp_add]
    simp).mulChi χ⁻¹
  rwa [← mulChi_mul, mul_inv_cancel, mulChi_one] at this

end GlobalTheory.CuspQuot

end
