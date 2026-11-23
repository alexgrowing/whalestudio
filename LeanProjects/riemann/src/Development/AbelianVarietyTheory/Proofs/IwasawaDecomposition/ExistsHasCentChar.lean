import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep.Central

theorem trace_mem {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (S : Submodule ℂ A)
    (h1 : (1 : A) ∈ S) (h : ∀ u, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  rcases n with _ | n
  · simp
  by_contra hc
  obtain ⟨f, hf, hS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
  have hf0 : ∀ x ∈ S, f x = 0 := fun x hx => (Submodule.eq_bot_iff _).1 hS _ ⟨x, hx, rfl⟩
  let p : Finset (Fin (n + 1)) → Polynomial ℂ := fun T => ∏ k ∈ Tᶜ, (Polynomial.X - Polynomial.C (k : ℂ))
  have hdeg : ∀ T, (p T).natDegree = n + 1 - T.card := fun T => by
    rw [show (p T).natDegree = Tᶜ.card from Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _, Finset.card_compl,
      Fintype.card_fin]
  have hP : ∑ T, f (CapelliTop.subdet X T) • p T = 0 := Polynomial.funext fun u => by
    have h2 := hf0 _ (h u)
    rw [CapelliTop.qdet_expand, map_sum] at h2
    rw [Polynomial.eval_zero, ← h2, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [p, Polynomial.eval_prod, mul_comm]
  have h3 := congrArg (fun q => Polynomial.coeff q n) hP
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_zero, smul_eq_mul] at h3
  have hz : ∀ T : Finset (Fin (n + 1)), 2 ≤ T.card → (p T).coeff n = 0 := fun T hT =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have : T.card ≤ n + 1 := by simpa using Finset.card_le_univ T
      rw [hdeg]; omega)
  have ho : ∀ i, (p {i}).coeff n = 1 := fun i => by
    have h4 : (p {i}).Monic := Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
    have h5 := h4.coeff_natDegree
    rwa [hdeg, Finset.card_singleton, Nat.add_sub_cancel] at h5
  rw [CapelliTop.sum_split, CapelliTop.subdet_empty, hf0 1 h1, zero_mul, zero_add,
    Finset.sum_eq_zero (s := Finset.univ.filter _) (fun T hT => by
      rw [hz T (by have := (Finset.mem_filter.1 hT).2; omega), mul_zero]), add_zero,
    Finset.sum_eq_zero (f := fun i => ∑ j ∈ _, _) (fun i _ => Finset.sum_eq_zero fun j hj => by
      rw [hz _ (Finset.card_pair (Finset.mem_filter.1 hj).2.ne).ge, mul_zero]), add_zero] at h3
  simp only [ho, CapelliTop.subdet_single, mul_one] at h3
  exact hf ((map_sum f _ _).trans h3)

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

abbrev scL (a : ℕ) (z : Cinf E) : Lie E a := toL (Matrix.diagonal fun _ => z)

theorem lie_mem_Zalg (x : Cinf E) : lie E a (scL a x) ∈ Zalg E a := by
  classical
  have hE : ∀ τ : E →+* ℂ, ∑ i, Eop τ i i ∈ Zalg E a := fun τ =>
    trace_mem (Eop τ) (Subalgebra.toSubmodule (Zalg E a)) (one_mem (Zalg E a)) fun u =>
      Algebra.subset_adjoin (R := ℂ) (s := {z | ∃ τ u, z = cap (a := a) τ u})
        ⟨τ, u - ((a : ℂ) - 1) / 2, by rw [cap, sub_add_cancel]⟩
  have h1 : ∀ (τ : E →+* ℂ) (z : ℂ), ∑ i, lieS E a i i (atEmb τ z) ∈ Zalg E a := fun τ z => by
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
      rw [atEmb_eq]; simp
    have e2 : ∀ i, lieS E a i i (atEmb τ z) =
        z • Eop τ i i + starRingEnd ℂ z • Eop (ComplexEmbedding.conjugate τ) i i := fun i => by
      rw [atEmb_eq, map_add, map_smul, map_smul]
      simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, ← Complex.coe_smul]
      match_scalars
      · rw [Complex.re_eq_add_conj]; ring
      · rw [Complex.im_eq_sub_conj]; field_simp; ring_nf; simp; ring
    simp only [e2, Finset.sum_add_distrib, ← Finset.smul_sum]
    exact add_mem (Subalgebra.smul_mem _ (hE _) _) (Subalgebra.smul_mem _ (hE _) _)
  have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    have : ∀ w : InfinitePlace E, atEmb w.embedding (x w) = Pi.single w (x w) := fun w => by
      unfold atEmb
      simp only [InfinitePlace.mk_embedding, if_true]
    simp [this, Finset.univ_sum_single]
  have e2 : lie E a (scL a x) = ∑ i, lieS E a i i x := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg (lie E a) (Matrix.sum_single_eq_diagonal (fun _ : Fin a => x)).symm
  rw [e2, e]
  simp only [map_sum]
  rw [Finset.sum_comm]
  exact sum_mem fun w _ => h1 _ _

abbrev rs (a : ℕ) (z : Ideles E) : Module.End ℂ (Sm E a) := rt E a (GeneralLinearGroup.scalar (Fin a) z)

theorem rs_act (z : Ideles E) (o : Op E a) : Commute (rs a z) (act o) := by
  have h : ∀ g, Commute (rs a z) (rt E a g) := fun g => by
    change _ * _ = _ * _
    rw [← map_mul, ← map_mul, scalar_comm]
  cases o with
  | fin k => exact h _
  | cpt k => exact h _
  | lie X =>
    refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
    have e : chart (fun x => φ.1 (x * GeneralLinearGroup.scalar (Fin a) z)) g =
        chart φ.1 (g * GeneralLinearGroup.scalar (Fin a) z) := by
      funext x
      simp only [chart, mul_assoc, scalar_comm z]
    exact (congrArg (fun f => fderiv ℝ f (oneL E a) X) e).symm

theorem hasDerivAt_scalar (z : Cinf E) (ψ : Sm E a) (g : GA E a) :
    HasDerivAt (fun t : ℝ => ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z)))))
      (lieD (scL a z) ψ.1 g) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toL (GeneralLinearGroup.scalar (Fin a) (expU (t • z))).val) (scL a z) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    change HasDerivAt (fun t : ℝ => Matrix.diagonal (fun _ => (expU (t • z)).val) i j) (Matrix.diagonal (fun _ => z) i j) 0
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      refine hasDerivAt_pi.2 fun w => ?_
      change HasDerivAt (fun t : ℝ => Complex.exp (t * z w)) _ 0
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (z w)).cexp
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact hasDerivAt_const _ _
  have h := hasDerivAt_curve ψ g (fun t => GeneralLinearGroup.scalar (Fin a) (expU (t • z))) _ (by simp [expU_zero]) hc
  simpa only [infGL, cornerGL_scalar, infId] using h

theorem lie_act (z : Cinf E) (o : Op E a) : Commute (lie E a (scL a z)) (act o) := by
  have h : ∀ k, Commute (lie E a (scL a z)) (rt E a k) := fun k =>
    LinearMap.ext fun φ => Subtype.ext <| funext fun g => by
      have h1 := hasDerivAt_scalar z (rt E a k φ) g
      simp only [rt_apply, mul_assoc, scalar_comm _ k] at h1
      simp only [← mul_assoc] at h1
      exact h1.unique (hasDerivAt_scalar z φ (g * k))
  cases o with
  | fin k => exact h _
  | cpt k => exact h _
  | lie Y =>
    have e : Matrix.of (scL a z) * Matrix.of Y = Matrix.of Y * Matrix.of (scL a z) :=
      (Matrix.scalar_commute z (fun _ => Commute.all _ _) (Matrix.of Y)).eq
    have h := lie_comm (scL a z) Y
    rw [e, sub_self, sub_eq_zero] at h
    exact h

theorem lie_scalar (π : CuspSub E a) (z : Cinf E) : ∃ c : ℂ, ∀ ψ ∈ π.V, lie E a (scL a z) ψ = c • ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have := (π.cusp φ hφ).1.zfin
  exact RankOne.scalar_of_finite π _ (lie_act z) (π.stable (.lie _)) hφ h0
    (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) fun i =>
      Submodule.subset_span ⟨_, pow_mem (lie_mem_Zalg z) i, rfl⟩

theorem rs_exp (z : Cinf E) (c : ℂ) (ψ : Sm E a) (h : lie E a (scL a z) ψ = c • ψ) :
    rs a (infId E (expU z)) ψ = Complex.exp c • ψ := by
  refine Subtype.ext <| funext fun g => ?_
  let f : ℝ → ℂ := fun t => ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))
  have hf : ∀ s, HasDerivAt f (c * f s) s := fun s => by
    have h1 := hasDerivAt_scalar z ψ (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (s • z))))
    have h2 : lieD (scL a z) ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (s • z)))) = c * f s :=
      congrFun (congrArg Subtype.val h) _
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const s s ((sub_self s).symm ▸ h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [f, mul_assoc, ← map_mul, ← expU_add, ← add_smul, add_sub_cancel]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(t * c)) * f t) 0 s := fun s => by
    have h1 := (((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const c).neg.cexp).mul (hf s)
    refine h1.congr_deriv ?_
    simp; ring
  have h2 := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) 1 0
  simp only [f, zero_smul, expU_zero, one_smul, map_one, mul_one, Complex.ofReal_one, one_mul, Complex.ofReal_zero,
    zero_mul, neg_zero, Complex.exp_zero] at h2
  change ψ.1 (g * _) = Complex.exp c * ψ.1 g
  rw [← h2, ← mul_assoc, ← Complex.exp_add]
  simp

def scal (π : CuspSub E a) : Submonoid (Ideles E) where
  carrier := {z | ∃ c : ℂ, ∀ ψ ∈ π.V, rs a z ψ = c • ψ}
  one_mem' := ⟨1, fun ψ _ => by rw [rs, map_one, map_one, one_smul]; rfl⟩
  mul_mem' := by
    rintro h h' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c' * c, fun ψ hψ => by
      rw [rs, map_mul, map_mul, Module.End.mul_apply, hc' ψ hψ, map_smul, hc ψ hψ, smul_smul]⟩

theorem infId_mem (π : CuspSub E a) (y : (Cinf E)ˣ) : infId E y ∈ scal π := by
  rw [← expU_log y]
  obtain ⟨c, hc⟩ := lie_scalar π fun i => Complex.log (y.val i)
  exact ⟨_, fun ψ hψ => rs_exp _ c ψ (hc ψ hψ)⟩

theorem rs_diag (π : CuspSub E a) (γ : Eˣ) {ψ : Sm E a} (hψ : ψ ∈ π.V) : rs a (diagUnits E γ) ψ = ψ :=
  Subtype.ext <| funext fun g => by
    have e : GeneralLinearGroup.scalar (Fin a) (diagUnits E γ) = ratGL E a (GeneralLinearGroup.scalar (Fin a) γ) :=
      (map_scalar _ γ).symm
    rw [rt_apply, ← scalar_comm, e, (π.cusp ψ hψ).1.left]

theorem rs_finId (k : (Af E)ˣ) : rs a (finId E k) = finRep E a (GeneralLinearGroup.scalar (Fin a) k) :=
  congrArg (rt E a) (cornerGL_scalar (sFin E) k).symm

theorem finId_mem_of_pow (π : CuspSub E a) (k : (Af E)ˣ) {n : ℕ} (hn : 0 < n)
    (h : finId E k ^ n ∈ scal π) : finId E k ∈ scal π := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨c, hc⟩ := h
  have hV : ∀ ψ ∈ π.V, rs a (finId E k) ψ ∈ π.V := rs_finId (a := a) k ▸ π.stable (.fin _)
  have hn' : (rs a (finId E k) ^ n) φ = c • φ := by rw [← map_pow, ← map_pow]; exact hc φ hφ
  set T := rs a (finId E k)
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : Fin n => (T ^ (i : ℕ)) φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine RankOne.scalar_of_finite π T (rs_act _) hV hφ h0
    (Submodule.span ℂ (Set.range fun i : Fin n => (T ^ (i : ℕ)) φ)) fun i => ?_
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases lt_or_ge i n with hi | hi
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
      rw [pow_add, Module.End.mul_apply, hn', map_smul]
      exact Submodule.smul_mem _ _ (ih j (by omega))

theorem continuous_scalar {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (GeneralLinearGroup.scalar (Fin a) : Rˣ → GL (Fin a) R) :=
  Continuous.units_map _ (continuous_pi fun _ => continuous_id).matrix_diagonal

theorem exists_open (π : CuspSub E a) : ∃ U : Subgroup (Af E)ˣ, IsOpen (U : Set (Af E)ˣ) ∧
    ∀ k ∈ U, ∀ ψ ∈ π.V, rs a (finId E k) ψ = ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨(π.finPart.comp (GeneralLinearGroup.scalar (Fin a))).ker, Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset (((π.cusp φ hφ).1.level.preimage continuous_scalar).mem_nhds (by simp)) fun k hk => ?_),
    fun k hk ψ hψ => ?_⟩
  · refine LinearMap.ext fun ψ => Subtype.ext ?_
    have h1 := RankOne.scalar_of_eigen π _ (rs_act (finId E k)) hφ h0 (c := 1)
      (by rw [rs_finId, one_smul]; exact hk) ψ.1 ψ.2
    rw [rs_finId, one_smul] at h1
    exact h1
  · rw [rs_finId]
    exact congrArg Subtype.val (LinearMap.congr_fun hk ⟨ψ, hψ⟩)

theorem finId_mem_of_int (π : CuspSub E a) (k : GL (Fin 1) (Af E))
    (hk : k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)) : finId E (GeneralLinearGroup.det k) ∈ scal π := by
  obtain ⟨U₀, hU₀, h⟩ := exists_open π
  let U : Subgroup (GL (Fin 1) (Af E)) := U₀.comap GeneralLinearGroup.det
  have hU : IsOpen (U : Set (GL (Fin 1) (Af E))) := hU₀.preimage GeneralLinearGroup.continuous_det
  have : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  set K : Subgroup (GL (Fin 1) (Af E)) := GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)
  have : CompactSpace K := isCompact_iff_compactSpace.1
    (GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E))
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have hi := (Subgroup.finiteIndex_of_finite_quotient (H := U.subgroupOf K)).index_ne_zero
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi ⟨k, hk⟩
  refine finId_mem_of_pow π _ hn ⟨1, fun ψ hψ => ?_⟩
  rw [← map_pow, ← map_pow, one_smul]
  exact h _ h1 ψ hψ

theorem mem_scal (π : CuspSub E a) (z : Ideles E) : z ∈ scal π := by
  rw [← infId_mul_finId z]
  refine mul_mem (infId_mem π _) ?_
  set k := Units.map (pFin E).toMonoidHom z
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E).index_ne_zero (finId E k)
  refine finId_mem_of_pow π k hn ?_
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, e⟩ := Subgroup.mem_sup.1 h1
  rw [← e]
  refine mul_mem ?_ ⟨1, fun ψ hψ => (rs_diag π γ hψ).trans (one_smul _ _).symm⟩
  rw [← infId_mul_finId u]
  refine mul_mem (infId_mem π _) ?_
  have key : ∀ u ∈ GlobalTheory.Mem.Chr.unitIdl E, ∀ i j, (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)).val i j ∈
      GlobalTheory.GLIntegral.intSubring E := fun u hu i j v => by
    rw [RankOne.obo_apply]
    exact (hu v).le
  have h2 := finId_mem_of_int π (RankOne.obo _ (Units.map (pFin E).toMonoidHom u))
    ⟨key u hu, by rw [← map_inv, ← map_inv]; exact key _ (inv_mem hu)⟩
  rwa [show GeneralLinearGroup.det (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)) = _ from CG.det_oneByOne _] at h2

theorem continuous_char (π : CuspSub E a) (ω : Ideles E →* ℂˣ) (h : ∀ z, ∀ ψ ∈ π.V, rs a z ψ = ((ω z : ℂˣ) : ℂ) • ψ) :
    Continuous ω := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Subtype.ext (funext hc))
  have hinf : Continuous fun y => ω (infId E y) := by
    refine Units.isEmbedding_val₀.continuous_iff.2 ?_
    have e : (Units.val ∘ fun y => ω (infId E y)) =
        fun y => chart φ.1 g₀ (toL (GeneralLinearGroup.scalar (Fin a) y).val) / φ.1 g₀ := by
      funext y
      rw [chart_val, eq_div_iff hg₀, infGL, cornerGL_scalar]
      exact (congrFun (congrArg Subtype.val (h (infId E y) φ hφ)) g₀).symm
    rw [e]
    exact ((φ.2 g₀).continuousOn.comp_continuous
      (f := fun y : (Cinf E)ˣ => toL (GeneralLinearGroup.scalar (Fin a) y).val)
      (continuous_pi fun _ => Units.continuous_val).matrix_diagonal fun y => val_mem_invSet _).div_const _
  have hfin : Continuous fun k => ω (finId E k) := by
    obtain ⟨U, hU, hU'⟩ := exists_open π
    refine continuous_of_continuousAt_one (ω.comp (finId E)) (ContinuousAt.congr (f := fun _ => 1) continuousAt_const ?_)
    filter_upwards [hU.mem_nhds U.one_mem] with k hk
    refine Units.ext (smul_left_injective ℂ h0 ?_)
    exact (one_smul _ _).trans ((hU' k hk φ hφ).symm.trans (h _ φ hφ))
  have e : (ω : Ideles E → ℂˣ) = fun z => ω (infId E (Units.map (pInf E).toMonoidHom z)) *
      ω (finId E (Units.map (pFin E).toMonoidHom z)) := by
    funext g
    rw [← map_mul, infId_mul_finId]
  rw [e]
  exact (hinf.comp (Continuous.units_map _ RankOne.continuous_pInf)).mul
    (hfin.comp (Continuous.units_map _ continuous_snd))

theorem exists_hasCentral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a), ∃ ω : Formalism.L2.Host.HChar E, π.HasCentral ω := by
  intro E _ _ _ a π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  choose c hc using mem_scal π
  let ω : Ideles E →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ h0 (by beta_reduce; rw [← hc 1 φ hφ, rs, map_one, map_one, one_smul]; rfl)
      map_mul' := fun g h => smul_left_injective ℂ h0 (by
        beta_reduce
        rw [← hc _ φ hφ, rs, map_mul, map_mul, Module.End.mul_apply, hc h φ hφ, map_smul, hc g φ hφ, smul_smul,
          mul_comm]) }
  refine ⟨⟨ω.toHomUnits, continuous_char π _ hc, fun γ => Units.ext (smul_left_injective ℂ h0 ?_)⟩, hc⟩
  exact (hc _ φ hφ).symm.trans ((rs_diag π γ hφ).trans (one_smul _ _).symm)

theorem exists_hasCentChar (π : CG E a) : ∃ ω : HChar E, π.HasCentChar ω := by
  induction π using Quotient.inductionOn with
  | _ π => exact (exists_hasCentral E a π).imp fun _ h => CuspSub.hasCentral_iff.1 h

end GlobalTheory.CuspRep.Central
