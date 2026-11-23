import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.RankOne

theorem gl_comm {R : Type} [CommRing R] (g h : GL (Fin 1) R) : g * h = h * g := by
  ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]

def obo (R : Type) [CommRing R] : Rˣ →* GL (Fin 1) R := Units.map (Matrix.scalar (Fin 1)).toMonoidHom

theorem obo_det {R : Type} [CommRing R] (g : GL (Fin 1) R) : obo R (GeneralLinearGroup.det g) = g := by
  ext i j
  simp [obo, Subsingleton.elim i 0, Subsingleton.elim j 0]

theorem obo_apply {R : Type} [CommRing R] (u : Rˣ) (i j : Fin 1) : (obo R u).val i j = u := by
  simp [obo, Subsingleton.elim i 0, Subsingleton.elim j 0]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem lie_rt (X : Lie E 1) (h : GA E 1) : Commute (rt E 1 h) (lie E 1 X) :=
  LinearMap.ext fun φ => Subtype.ext <| funext fun g => by
    have e : chart (fun x => φ.1 (x * h)) g = chart φ.1 (g * h) := by
      funext x
      simp only [chart, mul_assoc, gl_comm h]
    exact (congrArg (fun f => fderiv ℝ f (oneL E 1) X) e).symm

theorem rt_rt (h h' : GA E 1) : Commute (rt E 1 h) (rt E 1 h') := by
  change _ * _ = _ * _
  rw [← map_mul, ← map_mul, gl_comm]

theorem lie_lie (X Y : Lie E 1) : Commute (lie E 1 X) (lie E 1 Y) := by
  have e : Matrix.of X * Matrix.of Y = Matrix.of Y * Matrix.of X := by
    ext i j : 1
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
  have h := lie_comm X Y
  rw [e, sub_self, sub_eq_zero] at h
  exact h

theorem rt_act (h : GA E 1) (o : Op E 1) : Commute (rt E 1 h) (act o) := by
  cases o with
  | fin k => exact rt_rt _ _
  | cpt k => exact rt_rt _ _
  | lie X => exact lie_rt _ _

theorem lie_act (X : Lie E 1) (o : Op E 1) : Commute (lie E 1 X) (act o) := by
  cases o with
  | fin k => exact (lie_rt _ _).symm
  | cpt k => exact (lie_rt _ _).symm
  | lie Y => exact lie_lie _ _

theorem scalar_of_eigen {a : ℕ} (π : CuspSub E a) (T : Module.End ℂ (Sm E a)) (hT : ∀ o, Commute T (act o))
    {φ : Sm E a} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) {c : ℂ} (h : T φ = c • φ) : ∀ ψ ∈ π.V, T ψ = c • ψ := by
  have hs : IsStable (π.V ⊓ T.eigenspace c) := fun o ψ hψ =>
    ⟨π.stable o ψ hψ.1, Module.End.mem_eigenspace_iff.2 (by
      have h1 : T (act o ψ) = act o (T ψ) := LinearMap.congr_fun (hT o).eq ψ
      rw [h1, Module.End.mem_eigenspace_iff.1 hψ.2, map_smul])⟩
  rcases π.irred _ inf_le_left hs with h1 | h1
  · exact absurd (h1 ▸ (⟨hφ, Module.End.mem_eigenspace_iff.2 h⟩ : φ ∈ π.V ⊓ T.eigenspace c) : φ ∈ (⊥ : Submodule ℂ _)) h0
  · intro ψ hψ
    exact Module.End.mem_eigenspace_iff.1 (h1.ge hψ).2

theorem scalar_of_finite {a : ℕ} (π : CuspSub E a) (T : Module.End ℂ (Sm E a)) (hT : ∀ o, Commute T (act o))
    (hV : ∀ ψ ∈ π.V, T ψ ∈ π.V) {φ : Sm E a} (hφ : φ ∈ π.V) (h0 : φ ≠ 0) (S : Submodule ℂ (Sm E a))
    [FiniteDimensional ℂ S] (hS : ∀ i : ℕ, (T ^ i) φ ∈ S) : ∃ c : ℂ, ∀ ψ ∈ π.V, T ψ = c • ψ := by
  let W := Submodule.span ℂ (Set.range fun i : ℕ => (T ^ i) φ)
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (S₂ := S)
    (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hS i))
  have hWV : W ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨i, rfl⟩
    induction i with
    | zero => exact hφ
    | succ i ih =>
      have h1 := hV _ ih
      rw [← Module.End.mul_apply, ← pow_succ'] at h1
      exact h1)
  have hW : ∀ ψ ∈ W, T ψ ∈ W := fun ψ hψ =>
    (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i + 1, by simp only [pow_succ', Module.End.mul_apply]⟩) : W ≤ W.comap T) hψ
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2
    ((Submodule.ne_bot_iff _).2 ⟨φ, Submodule.subset_span ⟨0, rfl⟩, h0⟩)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hW)
  obtain ⟨ψ, hψ⟩ := hc.exists_hasEigenvector
  exact ⟨c, scalar_of_eigen π T hT (hWV ψ.2) (fun h => hψ.2 (Subtype.ext h))
    (congrArg Subtype.val hψ.apply_eq_smul)⟩

theorem cap_zero (τ : E →+* ℂ) : cap (a := 1) τ 0 = Eop τ 0 0 := by
  simp [cap, Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm]

theorem lie_mem_Zalg (X : Lie E 1) : lie E 1 X ∈ Zalg E 1 := by
  classical
  have hE : ∀ τ : E →+* ℂ, Eop τ 0 0 ∈ Zalg E 1 := fun τ => Algebra.subset_adjoin ⟨τ, 0, (cap_zero τ).symm⟩
  have h1 : ∀ (τ : E →+* ℂ) (z : ℂ), lieS E 1 0 0 (atEmb τ z) ∈ Zalg E 1 := fun τ z => by
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
      rw [atEmb_eq]; simp
    have e2 : lieS E 1 0 0 (atEmb τ z) =
        z • Eop τ 0 0 + starRingEnd ℂ z • Eop (ComplexEmbedding.conjugate τ) 0 0 := by
      rw [atEmb_eq, map_add, map_smul, map_smul]
      simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, ← Complex.coe_smul]
      match_scalars
      · rw [Complex.re_eq_add_conj]; ring
      · rw [Complex.im_eq_sub_conj]; field_simp; ring_nf; simp; ring
    rw [e2]
    exact add_mem (Subalgebra.smul_mem _ (hE _) _) (Subalgebra.smul_mem _ (hE _) _)
  have e : X = toL (Matrix.single 0 0 (∑ w : InfinitePlace E, atEmb w.embedding (X 0 0 w))) := by
    funext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    have : ∀ w : InfinitePlace E, atEmb w.embedding (X 0 0 w) = Pi.single w (X 0 0 w) := fun w => by
      unfold atEmb
      simp only [InfinitePlace.mk_embedding, if_true]
    simp [this, Finset.univ_sum_single]
  rw [e, ← lieS_apply, map_sum]
  exact sum_mem fun w _ => h1 _ _

theorem lie_scalar (π : CuspSub E 1) (X : Lie E 1) : ∃ c : ℂ, ∀ ψ ∈ π.V, lie E 1 X ψ = c • ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have := (π.cusp φ hφ).1.zfin
  exact scalar_of_finite π _ (lie_act X) (π.stable (.lie X)) hφ h0
    (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E 1) => z φ) '' Zalg E 1)) fun i =>
      Submodule.subset_span ⟨_, pow_mem (lie_mem_Zalg X) i, rfl⟩

theorem rt_exp (z : Cinf E) (c : ℂ) (ψ : Sm E 1) (h : lie E 1 (fun _ _ => z) ψ = c • ψ) :
    rt E 1 (infGL E 1 (obo _ (expU z))) ψ = Complex.exp c • ψ := by
  refine Subtype.ext <| funext fun g => ?_
  let γ : ℝ → GL (Fin 1) (Cinf E) := fun t => obo _ (expU (t • z))
  have h0 : γ 0 = 1 := by simp [γ, expU_zero]
  have hadd : ∀ s t, γ (s + t) = γ s * γ t := fun s t => by simp only [γ, add_smul, expU_add, map_mul]
  have hc : HasDerivAt (fun t => toL (γ t).val) (fun _ _ => z) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
    have e : (fun t : ℝ => toL (γ t).val i j w) = fun t : ℝ => Complex.exp (t * z w) := by
      funext t
      exact congrFun (obo_apply (expU (t • z)) i j) w
    rw [e]
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (z w)).cexp
  let f : ℝ → ℂ := fun t => ψ.1 (g * infGL E 1 (γ t))
  have hf : ∀ s, HasDerivAt f (c * f s) s := fun s => by
    have h1 := hasDerivAt_curve ψ (g * infGL E 1 (γ s)) γ _ h0 hc
    have h2 : lieD (fun _ _ => z) ψ.1 (g * infGL E 1 (γ s)) = c * f s :=
      congrFun (congrArg Subtype.val h) _
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const s s ((sub_self s).symm ▸ h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [f, mul_assoc, ← map_mul, ← hadd, add_sub_cancel]
  have hg : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(t * c)) * f t) 0 s := fun s => by
    have h1 := (((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const c).neg.cexp).mul (hf s)
    refine h1.congr_deriv ?_
    simp; ring
  have h2 := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) 1 0
  simp only [f, h0, γ, one_smul, map_one, mul_one, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero] at h2
  change ψ.1 (g * _) = Complex.exp c * ψ.1 g
  rw [← h2, ← mul_assoc, ← Complex.exp_add]
  simp

def scal (π : CuspSub E 1) : Submonoid (GA E 1) where
  carrier := {h | ∃ c : ℂ, ∀ ψ ∈ π.V, rt E 1 h ψ = c • ψ}
  one_mem' := ⟨1, fun ψ _ => by simp⟩
  mul_mem' := by
    rintro h h' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c' * c, fun ψ hψ => by rw [map_mul, Module.End.mul_apply, hc' ψ hψ, map_smul, hc ψ hψ, smul_smul]⟩

theorem infGL_mem (π : CuspSub E 1) (y : GL (Fin 1) (Cinf E)) : infGL E 1 y ∈ scal π := by
  rw [← obo_det y, ← expU_log (GeneralLinearGroup.det y)]
  obtain ⟨c, hc⟩ := lie_scalar π fun _ _ i => Complex.log ((GeneralLinearGroup.det y : (Cinf E)ˣ).val i)
  exact ⟨_, fun ψ hψ => rt_exp _ c ψ (hc ψ hψ)⟩

theorem rt_ratGL (π : CuspSub E 1) (γ : GL (Fin 1) E) {ψ : Sm E 1} (hψ : ψ ∈ π.V) : rt E 1 (ratGL E 1 γ) ψ = ψ :=
  Subtype.ext <| funext fun g => by rw [rt_apply, gl_comm, (π.cusp ψ hψ).1.left]

theorem finGL_mem_of_pow (π : CuspSub E 1) (k : GL (Fin 1) (Af E)) {n : ℕ} (hn : 0 < n)
    (h : finGL E 1 k ^ n ∈ scal π) : finGL E 1 k ∈ scal π := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨c, hc⟩ := h
  set T := rt E 1 (finGL E 1 k)
  have hV : ∀ ψ ∈ π.V, T ψ ∈ π.V := π.stable (.fin k)
  have hn' : (T ^ n) φ = c • φ := by rw [← map_pow]; exact hc φ hφ
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : Fin n => (T ^ (i : ℕ)) φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine scalar_of_finite π T (rt_act _) hV hφ h0 (Submodule.span ℂ (Set.range fun i : Fin n => (T ^ (i : ℕ)) φ)) fun i => ?_
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases lt_or_ge i n with hi | hi
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
      rw [pow_add, Module.End.mul_apply, hn', map_smul]
      exact Submodule.smul_mem _ _ (ih j (by omega))

theorem exists_open (π : CuspSub E 1) : ∃ U : Subgroup (GL (Fin 1) (Af E)), IsOpen (U : Set (GL (Fin 1) (Af E))) ∧
    ∀ k ∈ U, ∀ ψ ∈ π.V, rt E 1 (finGL E 1 k) ψ = ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨π.finPart.ker, Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((π.cusp φ hφ).1.level.mem_nhds (by simp)) fun k hk => ?_), fun k hk ψ hψ => ?_⟩
  · refine LinearMap.ext fun ψ => Subtype.ext ?_
    exact (scalar_of_eigen π _ (rt_act (finGL E 1 k)) hφ h0 (c := 1) (hk.trans (one_smul _ _).symm) ψ.1 ψ.2).trans
      (one_smul _ _)
  · exact congrArg Subtype.val (LinearMap.congr_fun hk ⟨ψ, hψ⟩)

theorem finGL_mem_of_int (π : CuspSub E 1) (k : GL (Fin 1) (Af E))
    (hk : k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)) : finGL E 1 k ∈ scal π := by
  obtain ⟨U, hU, h⟩ := exists_open π
  have : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  set K : Subgroup (GL (Fin 1) (Af E)) := GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)
  have : CompactSpace K := isCompact_iff_compactSpace.1
    (GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E))
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have hi := (Subgroup.finiteIndex_of_finite_quotient (H := U.subgroupOf K)).index_ne_zero
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi ⟨k, hk⟩
  refine finGL_mem_of_pow π k hn ⟨1, fun ψ hψ => ?_⟩
  rw [← map_pow, one_smul]
  exact h _ h1 ψ hψ

theorem mem_scal (π : CuspSub E 1) (g : GA E 1) : g ∈ scal π := by
  rw [← infGL_mul_finGL g]
  refine mul_mem (infGL_mem π _) ?_
  set k := GeneralLinearGroup.map (pFin E) g
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E).index_ne_zero (GeneralLinearGroup.det (finGL E 1 k))
  refine finGL_mem_of_pow π k hn ?_
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, e⟩ := Subgroup.mem_sup.1 h1
  rw [← obo_det (_ ^ n), map_pow, ← e, map_mul]
  refine mul_mem ?_ ⟨1, fun ψ hψ => ?_⟩
  · rw [← infGL_mul_finGL (obo _ u)]
    refine mul_mem (infGL_mem π _) (finGL_mem_of_int π _ ?_)
    have key : ∀ u ∈ GlobalTheory.Mem.Chr.unitIdl E, ∀ i j, (GeneralLinearGroup.map (pFin E) (obo _ u)).val i j ∈
        GlobalTheory.GLIntegral.intSubring E := fun u hu i j v => by
      change pFin E ((obo _ u).val i j) v ∈ _
      rw [obo_apply]
      exact (hu v).le
    exact ⟨key u hu, by rw [← map_inv, ← map_inv]; exact key _ (inv_mem hu)⟩
  · have e2 : obo _ (diagUnits E γ) = ratGL E 1 (obo _ γ) := by
      ext i j : 2
      change _ = algebraMap E (Ad E) ((obo _ γ).val i j)
      rw [obo_apply, obo_apply]
      rfl
    rw [e2, one_smul]
    exact rt_ratGL π _ hψ

theorem exists_char (π : CuspSub E 1) : ∃ ω : GA E 1 →* ℂˣ, ∀ g, ∀ ψ ∈ π.V, rt E 1 g ψ = ((ω g : ℂˣ) : ℂ) • ψ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  choose c hc using mem_scal π
  let ω : GA E 1 →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ h0 (by beta_reduce; rw [← hc 1 φ hφ]; simp)
      map_mul' := fun g h => smul_left_injective ℂ h0 (by
        beta_reduce
        rw [← hc _ φ hφ, map_mul, Module.End.mul_apply, hc h φ hφ, map_smul, hc g φ hφ, smul_smul, mul_comm]) }
  exact ⟨ω.toHomUnits, hc⟩

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w) : Continuous (infEq E).symm).comp continuous_fst

theorem continuous_char (π : CuspSub E 1) (ω : GA E 1 →* ℂˣ) (h : ∀ g, ∀ ψ ∈ π.V, rt E 1 g ψ = ((ω g : ℂˣ) : ℂ) • ψ) :
    Continuous ω := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (Subtype.ext (funext hc))
  have hinf : Continuous fun y => ω (infGL E 1 y) := by
    refine Units.isEmbedding_val₀.continuous_iff.2 ?_
    have e : (Units.val ∘ fun y => ω (infGL E 1 y)) = fun y => chart φ.1 g₀ (toL y.val) / φ.1 g₀ := by
      funext y
      rw [chart_val, eq_div_iff hg₀]
      exact (congrFun (congrArg Subtype.val (h (infGL E 1 y) φ hφ)) g₀).symm
    rw [e]
    exact ((φ.2 g₀).continuousOn.comp_continuous (f := fun y : GL (Fin 1) (Cinf E) => toL y.val)
      (Units.continuous_val (M := Matrix (Fin 1) (Fin 1) (Cinf E))) val_mem_invSet).div_const _
  have hfin : Continuous fun k => ω (finGL E 1 k) := by
    obtain ⟨U, hU, hU'⟩ := exists_open π
    refine continuous_of_continuousAt_one (ω.comp (finGL E 1)) (ContinuousAt.congr (f := fun _ => 1) continuousAt_const ?_)
    filter_upwards [hU.mem_nhds U.one_mem] with k hk
    refine Units.ext (smul_left_injective ℂ h0 ?_)
    exact (one_smul _ _).trans ((hU' k hk φ hφ).symm.trans (h _ φ hφ))
  have e : (ω : GA E 1 → ℂˣ) = fun g => ω (infGL E 1 (GeneralLinearGroup.map (pInf E) g)) *
      ω (finGL E 1 (GeneralLinearGroup.map (pFin E) g)) := by
    funext g
    rw [← map_mul, infGL_mul_finGL]
  rw [e]
  exact (hinf.comp (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf))).mul
    (hfin.comp (Continuous.units_map _ (continuous_id.matrix_map continuous_snd)))

theorem exists_eq_twist (π : CuspSub E 1) : ∃ χ : HChar E, (CuspSub.triv E le_rfl).twist χ = π := by
  obtain ⟨ω, h⟩ := exists_char π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hc : Continuous (obo (Ad E)) := Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j => by
    simpa [Subsingleton.elim i 0, Subsingleton.elim j 0] using continuous_id')
  let χ : HChar E := ⟨ω.comp (obo _), (continuous_char π ω h).comp hc, fun γ => by
    have e2 : obo _ (diagUnits E γ) = ratGL E 1 (obo _ γ) := by
      ext i j : 2
      change _ = algebraMap E (Ad E) ((obo _ γ).val i j)
      rw [obo_apply, obo_apply]
      rfl
    refine Units.ext (smul_left_injective ℂ h0 ?_)
    change ((ω (obo _ (diagUnits E γ)) : ℂˣ) : ℂ) • φ = (1 : ℂ) • φ
    rw [← h _ φ hφ, e2, one_smul]
    exact rt_ratGL π _ hφ⟩
  have hle : π.V ≤ ((CuspSub.triv E le_rfl).twist χ).V := fun ψ hψ =>
    ⟨ψ.1 1 • oneFn E 1, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), Subtype.ext <| funext fun g => by
      have h1 : ψ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * ψ.1 1 := congrFun (congrArg Subtype.val (h g ψ hψ)) 1
      change ψ.1 1 * 1 * ((ω (obo _ (GeneralLinearGroup.det g)) : ℂˣ) : ℂ) = ψ.1 g
      rw [obo_det, mul_one, mul_comm, ← h1, one_mul]⟩
  exact ⟨χ, CuspSub.ext ((((CuspSub.triv E le_rfl).twist χ).irred _ hle π.stable).resolve_left π.ne_bot).symm⟩

theorem ofChar_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E],
    Function.Bijective (CG.ofChar : HChar E → CG E 1) := by
  intro E _ _ _
  refine ⟨CG.ofChar_injective, fun σ => ?_⟩
  induction σ using Quotient.inductionOn with
  | h π =>
    obtain ⟨χ, h⟩ := exists_eq_twist π
    exact ⟨χ, congrArg CG.mk h⟩

end GlobalTheory.CuspRep.RankOne
