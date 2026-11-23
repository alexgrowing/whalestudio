import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.AdelicGluing.ExistsOpenSubgroupRightInvariantFiniteAdelicGL
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem isCompact_compSet {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] (n : ℕ) (C : ∀ i, Set (GL (Fin n) (R i))) (hC : ∀ i, IsCompact (C i)) :
    IsCompact {g : GL (Fin n) (∀ i, R i) | ∀ i, mapGL n (Pi.evalRingHom R i) g ∈ C i} := by
  have key : ∀ (p : ∀ i, GL (Fin n) (R i)) (s t : ∀ i, GL (Fin n) (R i)), (∀ i, s i * t i = 1) →
      (Matrix.of fun a b i => (s i : Matrix (Fin n) (Fin n) (R i)) a b) *
        (Matrix.of fun a b i => (t i : Matrix (Fin n) (Fin n) (R i)) a b) =
        (1 : Matrix (Fin n) (Fin n) (∀ i, R i)) := by
    intro _ s t h
    refine Matrix.ext fun a b => funext fun i => ?_
    have h1 : (s i : Matrix (Fin n) (Fin n) (R i)) * (t i : Matrix (Fin n) (Fin n) (R i)) = 1 := by
      rw [← Units.val_mul, h i, Units.val_one]
    have h2 := congr_fun (congr_fun h1 a) b
    rw [Matrix.mul_apply] at h2
    rw [Matrix.mul_apply, Finset.sum_apply]
    simp only [Matrix.of_apply, Pi.mul_apply]
    rw [h2]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.one_apply_ne hab]
  let Ψ : (∀ i, GL (Fin n) (R i)) → GL (Fin n) (∀ i, R i) := fun p =>
    { val := Matrix.of fun a b i => (p i : Matrix (Fin n) (Fin n) (R i)) a b
      inv := Matrix.of fun a b i => (((p i)⁻¹ : GL (Fin n) (R i)) : Matrix (Fin n) (Fin n) (R i)) a b
      val_inv := key p p (fun i => (p i)⁻¹) fun i => mul_inv_cancel _
      inv_val := key p (fun i => (p i)⁻¹) p fun i => inv_mul_cancel _ }
  have hΨ : Continuous Ψ := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => continuous_pi fun i => ?_
      exact (Units.continuous_val.matrix_elem a b).comp (continuous_apply i)
    · refine continuous_matrix fun a b => continuous_pi fun i => ?_
      exact (Units.continuous_val.matrix_elem a b).comp (continuous_inv.comp (continuous_apply i))
  convert (isCompact_univ_pi hC).image hΨ using 1
  ext g
  constructor
  · intro hg
    refine ⟨fun i => mapGL n (Pi.evalRingHom R i) g, fun i _ => hg i, ?_⟩
    refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
    rfl
  · rintro ⟨p, hp, rfl⟩ i
    have : mapGL n (Pi.evalRingHom R i) (Ψ p) = p i := Units.ext (Matrix.ext fun a b => rfl)
    rw [this]
    exact hp i trivial

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem entry_snd (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    cmp w (pv v x) = cf w.1 x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [entry_snd]
  rfl

private theorem gl_ext {v : Pl F} {g g' : GL (Fin n) (CompletionsOver E v)}
    (h : ∀ w : PlacesOver E v, cmp w g = cmp w g') : g = g' := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  exact congrArg (fun t : GL (Fin n) (w.1.adicCompletion E) => t.1 a b) (h w)

private theorem cf_mul (w : Pl E) (x y : AdelicGLn.FiniteAdelicGL E n) : cf w (x * y) = cf w x * cf w y := by
  simp only [cf]
  rw [map_mul, finAt_mul]

private def iwSet (E : Type) [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : Pl F) :
    Set (GL (Fin n) (CompletionsOver E q)) :=
  {g | ∀ w : PlacesOver E q, cmp w g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n}

private theorem iwCoset_zero' (w : Pl E) :
    iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

private theorem iwFn_zero {q : Pl F} (w₀ : PlacesOver E q) :
    iwFn w₀ (0 : Fin n → ℤ) = (iwSet E n q).indicator 1 := by
  classical
  funext g
  have : Fintype (PlacesOver E q) := Fintype.ofFinite _
  simp only [iwFn, prodFn, ite_self, iwCoset_zero']
  rw [finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ iwSet E n q
  · rw [Set.indicator_of_mem hg, Pi.one_apply]
    exact Finset.prod_eq_one fun w _ => by rw [Set.indicator_of_mem (hg w), Pi.one_apply]
  · rw [Set.indicator_of_notMem hg]
    simp only [iwSet, Set.mem_setOf_eq, not_forall] at hg
    obtain ⟨w, hw⟩ := hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

private theorem continuous_cmp' {v : Pl F} (w : PlacesOver E v) : Continuous (cmp (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

private theorem isCompact_iwSet (q : Pl F) : IsCompact (iwSet E n q) :=
  isCompact_compSet (R := fun w : PlacesOver E q => w.1.adicCompletion E) n
    (fun w => (GLnLocal.iwahori (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))))
    fun w => GLnLocal.isCompact_iwahori _ n

private theorem isOpen_iwSet (q : Pl F) : IsOpen (iwSet E n q) := by
  simp only [iwSet, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun w =>
    (GLnLocal.isOpen_iwahori (w.1.adicCompletion E) n).preimage (continuous_cmp' w)

private theorem isClosed_iwSet (q : Pl F) : IsClosed (iwSet E n q) := by
  simp only [iwSet, Set.setOf_forall]
  exact isClosed_iInter fun w =>
    (GLnLocal.isCompact_iwahori (w.1.adicCompletion E) n).isClosed.preimage (continuous_cmp' w)

private theorem iwSet_test (q : Pl F) :
    IsLocallyConstant ((iwSet E n q).indicator (1 : GL (Fin n) (CompletionsOver E q) → ℂ)) ∧
      HasCompactSupport ((iwSet E n q).indicator (1 : GL (Fin n) (CompletionsOver E q) → ℂ)) := by
  constructor
  · rw [← LocallyConstant.coe_charFn ℂ ⟨isClosed_iwSet q, isOpen_iwSet q⟩]
    exact LocallyConstant.isLocallyConstant _
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_iwSet q) fun g hg => ?_
    by_contra h
    exact hg (Set.indicator_of_notMem h _)

private theorem mulSupport_finite (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hφ : ∀ v ∉ S, φ v = (unitSet E n v).indicator 1) (x : AdelicGLn.FiniteAdelicGL E n) :
    (Function.mulSupport fun v => φ v (pv v x)).Finite := by
  have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
      GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
    Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
  refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
  by_cases hvS : v ∈ S
  · exact Or.inl hvS
  · right
    have hnot : pv v x ∉ unitSet E n v := by
      intro h
      refine hv ?_
      change φ v (pv v x) = 1
      rw [hφ v hvS, Set.indicator_of_mem h, Pi.one_apply]
    simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
    obtain ⟨w', hw'⟩ := hnot
    refine ⟨w'.1, ?_, under_eq w'⟩
    intro h
    refine hw' ?_
    have : cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
      rw [cmp_pv]
      exact h
    exact this

end

theorem UpperTheory.exists_iwahori_factorizable_finite_vector_of_average :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (q : Pl F) (w₀ : PlacesOver E q) (L : Loc σ n q w₀) (β : TI E n),
          ∃ e : TF E n, (∀ x, tens β e x = avg (tensE (onInf β) L.φ) x) ∧
            (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL E n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL E n)) ∧ ∀ u ∈ U, ∀ h, e (h * u) = e h) ∧
            ∀ w : PlacesOver E q, ∃ r : AdelicGLn.FiniteAdelicGL E n → ℂ, Free w.1 r ∧
              ∀ x, e x = r x * (GLnLocal.iwahori (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))).indicator 1 (cf w.1 x) := by
  classical
  intro F E _ _ _ _ _ _ σ n hn q w₀ L β
  have hφq : L.φ q = (iwSet E n q).indicator 1 := by rw [L.at_q.1, iwFn_zero]
  have hoff : ∀ v ∉ insert q L.S, L.φ v = (unitSet E n v).indicator 1 := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    exact (L.off v hv.2 hv.1).1
  have htest : ∀ v ∈ insert q L.S, IsLocallyConstant (L.φ v) ∧ HasCompactSupport (L.φ v) := by
    intro v hv
    rcases Finset.mem_insert.1 hv with h | hv
    · rw [h, hφq]
      exact iwSet_test q
    · exact ⟨(L.test v hv).1, (L.test v hv).2.1⟩
  obtain ⟨e, hlc, hform, hten⟩ := UpperTheory.ConvolutionTheory.GM.avgE F E n hn (insert q L.S) β L.φ htest hoff
  have hform' : ∀ x, e x = ∏ᶠ v, L.φ v (pv v x) := hform
  obtain ⟨W, hWo, hW⟩ := UpperTheory.exists_open_subgroup_rightInvariant_finiteAdelicGL E n e hlc
  refine ⟨e, hten, ⟨W, hWo, hW⟩, fun w => ?_⟩
  obtain ⟨-, hself, hother, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb E n w.1
  refine ⟨fun x => e (AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹ * x), ?_, fun x => ?_⟩
  · intro y x
    have h1 : cf w.1 (AdelicGLn.localEmbedding w.1 y * x) = y * cf w.1 x := by
      rw [cf_mul]
      congr 1
      exact hself y
    change e (AdelicGLn.localEmbedding w.1 (cf w.1 (AdelicGLn.localEmbedding w.1 y * x))⁻¹ * (AdelicGLn.localEmbedding w.1 y * x)) =
      e (AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹ * x)
    have h2 : AdelicGLn.localEmbedding w.1 ((cf w.1 x)⁻¹ * y⁻¹) * (AdelicGLn.localEmbedding w.1 y * x) =
        AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹ * x := by
      rw [map_mul (AdelicGLn.localEmbedding w.1), map_inv (AdelicGLn.localEmbedding w.1) y]
      group
    rw [h1, mul_inv_rev, h2]
  · by_cases hx : cf w.1 x ∈ GLnLocal.iwahori (w.1.adicCompletion E) n
    · rw [Set.indicator_of_mem (show cf w.1 x ∈ (GLnLocal.iwahori (w.1.adicCompletion E) n : Set _) from hx), Pi.one_apply, mul_one]
      change e x = e (AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹ * x)
      generalize hx' : AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹ * x = x'
      have hc : ∀ u : Pl E, u ≠ w.1 → cf u x' = cf u x := by
        intro u hu
        rw [← hx', cf_mul]
        have : cf u (AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹) = 1 := hother u hu _
        rw [this, one_mul]
      have hw : cf w.1 x' = 1 := by
        rw [← hx', cf_mul]
        have : cf w.1 (AdelicGLn.localEmbedding w.1 (cf w.1 x)⁻¹) = (cf w.1 x)⁻¹ := hself _
        rw [this, inv_mul_cancel]
      have hq : pv q x ∈ iwSet E n q ↔ pv q x' ∈ iwSet E n q := by
        refine forall_congr' fun u => ?_
        rw [cmp_pv, cmp_pv]
        by_cases hu : u = w
        · subst hu
          rw [hw]
          exact ⟨fun _ => one_mem _, fun _ => hx⟩
        · rw [hc u.1 fun h => hu (Subtype.ext h)]
      rw [hform', hform']
      refine finprod_congr fun v => ?_
      by_cases hv : v = q
      · rw [hv, hφq]
        by_cases h : pv q x ∈ iwSet E n q
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hq.1 h), Pi.one_apply, Pi.one_apply]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hq.2 h)]
      · have : pv v x = pv v x' := gl_ext fun u => by
          rw [cmp_pv, cmp_pv, hc u.1 fun h => hv ?_]
          rw [← under_eq u, h, under_eq w]
        rw [this]
    · rw [Set.indicator_of_notMem (show cf w.1 x ∉ (GLnLocal.iwahori (w.1.adicCompletion E) n : Set _) from hx), mul_zero, hform']
      refine finprod_eq_zero _ q ?_ (mulSupport_finite _ L.φ hoff x)
      rw [hφq]
      refine Set.indicator_of_notMem (fun h => hx ?_) _
      have := h w
      rwa [cmp_pv] at this
