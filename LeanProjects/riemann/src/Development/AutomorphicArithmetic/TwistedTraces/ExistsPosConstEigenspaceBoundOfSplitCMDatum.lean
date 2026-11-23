import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundDimSimultaneousLocalEigenspaceOfOpenC
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

noncomputable section

namespace UpperTheory.EigenspaceProjectionTraces

private theorem ops_key {M : Type*} [Monoid M] (b₁ b₂ P Q O : M) (habs : b₁ = b₁ * P) (hc : b₂ * P = P * b₂)
    (hO : P * Q = O) : b₁ * (b₂ * O) = b₁ * b₂ * Q := by
  subst hO
  rw [← mul_assoc b₂, hc, mul_assoc P, ← mul_assoc b₁, ← habs, mul_assoc]

section Hil
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem V.topologicalClosure v
  rwa [hc] at h

private theorem prj_inner {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v w : H) (hw : w ∈ V) :
    ⟪v - prj V v, w⟫_ℂ = 0 := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  exact Submodule.starProjection_inner_eq_zero v w (hc.symm ▸ hw)

private theorem prj_eq_of {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (x y : H) (hy : y ∈ V)
    (h : ∀ w ∈ V, ⟪x - y, w⟫_ℂ = 0) : prj V x = y := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  show V.topologicalClosure.starProjection x = y
  have hy' : y ∈ V.topologicalClosure := by rw [hc]; exact hy
  have h' : ∀ w ∈ V.topologicalClosure, ⟪x - y, w⟫_ℂ = 0 := fun w hw => h w (by rwa [hc] at hw)
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy' h'

private theorem prj_comp_of_commute {E G : Submodule ℂ H} (hE : IsClosed (E : Set H)) (hG : IsClosed (G : Set H))
    (hc : Commute (prj E) (prj G)) : prj E ∘L prj G = prj (E ⊓ G) := by
  have hEG : IsClosed ((E ⊓ G : Submodule ℂ H) : Set H) := by
    rw [Submodule.coe_inf]; exact hE.inter hG
  refine ContinuousLinearMap.ext fun x => ?_
  symm
  refine prj_eq_of hEG x _ ⟨prj_mem hE _, ?_⟩ fun w hw => ?_
  · have : (prj E * prj G) x = (prj G * prj E) x := by rw [hc.eq]
    show prj E (prj G x) ∈ G
    have h2 : prj E (prj G x) = prj G (prj E x) := this
    rw [h2]; exact prj_mem hG _
  · have h1 := prj_inner hG x w hw.2
    have h2 := prj_inner hE (prj G x) w hw.1
    have : x - (prj E ∘L prj G) x = (x - prj G x) + (prj G x - prj E (prj G x)) := by
      simp
    rw [this, inner_add_left, h1, h2, add_zero]

private theorem prj_commute {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) : Commute T (prj V) := by
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine prj_eq_of hV _ _ (h1 _ (prj_mem hV v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact prj_inner hV v _ (h2 w hw)

end Hil

section Alg
variable {M : Type*} [Monoid M]

private theorem ofFn_absorb : ∀ (r : ℕ) (T P : Fin r → M), (∀ i j, i ≠ j → Commute (T i) (P j)) → (∀ i, T i * P i = T i) →
    (List.ofFn T).prod = (List.ofFn T).prod * (List.ofFn P).prod := by
  intro r
  induction r with
  | zero => intro T P _ _; simp
  | succ r ih =>
    intro T P h1 h2
    have h3 := ih (fun i => T i.succ) (fun i => P i.succ)
      (fun i j hij => h1 _ _ fun h => hij (Fin.succ_injective _ h)) fun i => h2 _
    have h4 : Commute (List.ofFn fun i : Fin r => T i.succ).prod (P 0) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h1 _ _ (Fin.succ_ne_zero i)
    simp only [List.ofFn_succ, List.prod_cons]
    calc T 0 * (List.ofFn fun i : Fin r => T i.succ).prod
        = (T 0 * P 0) * ((List.ofFn fun i : Fin r => T i.succ).prod * (List.ofFn fun i : Fin r => P i.succ).prod) := by
          rw [← h3, h2]
      _ = _ := by
          rw [mul_assoc, mul_assoc, ← mul_assoc (P 0), ← h4.eq, mul_assoc]

end Alg

section Loc
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1 (AdelicGLn.localEmbedding w g) (AdelicGLn.localEmbedding w h)
  simpa only [rhoL, map_mul] using this

private theorem rhoL_adj (w : Pl K) (g : Gw n w) : ContinuousLinearMap.adjoint (rhoL μ w g) = rhoL μ w g⁻¹ := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.2.1 (AdelicGLn.localEmbedding w g)
  simpa only [rhoL, map_inv] using this

private theorem rhoL_comm {v w : Pl K} (h : v ≠ w) (g : Gw n v) (x : Gw n w) :
    rhoL μ v g ∘L rhoL μ w x = rhoL μ w x ∘L rhoL μ v g := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.2.1 w h.symm g x
  simp only [rhoL]
  rw [← hm, ← hm, hc]

private def GAx (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (A : Set (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ u ∈ A, eigL μ u (J u) (χ u)

variable {J : ∀ w : Pl K, Subgroup (Gw n w)} {χ : ∀ w : Pl K, Gw n w → ℂ}

private theorem GA_closed (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) (A : Set (Pl K)) :
    IsClosed (GAx μ J χ A : Set (LL μ)) := by
  simp only [GAx, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    (eigBasic K n μ u (J u) (χ u) (hco u).1 (hco u).2).1

private theorem mem_eigL {w : Pl K} {J' : Subgroup (Gw n w)} {χ' : Gw n w → ℂ} {x : LL μ} :
    x ∈ eigL μ w J' χ' ↔ ∀ y ∈ J', rhoL μ w y x = χ' y • x := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem GA_stable {A : Set (Pl K)} {v : Pl K} (hv : v ∉ A) (g : Gw n v) (x : LL μ) (hx : x ∈ GAx μ J χ A) :
    rhoL μ v g x ∈ GAx μ J χ A := by
  simp only [GAx, Submodule.mem_iInf] at hx ⊢
  intro u hu
  refine (mem_eigL μ).2 fun y hy => ?_
  have hne : u ≠ v := fun h => hv (h ▸ hu)
  have h1 := congrArg (· x) (rhoL_comm μ hne y g)
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [h1, (mem_eigL μ).1 (hx u hu) y hy, map_smul]

private theorem GA_commute (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) {A : Set (Pl K)} {v : Pl K} (hv : v ∉ A) (g : Gw n v) :
    Commute (rhoL μ v g) (prj (GAx μ J χ A)) := by
  refine prj_commute (GA_closed μ hco A) _ (GA_stable μ hv g) fun x hx => ?_
  rw [rhoL_adj]
  exact GA_stable μ hv _ x hx

private theorem list_prj (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) (L : List (Pl K)) :
    L.Nodup → ∀ (A : Set (Pl K)), (∀ v ∈ L, v ∉ A) →
    (L.map fun v => prj (eigL μ v (J v) (χ v))).prod ∘L prj (GAx μ J χ A) = prj (GAx μ J χ (A ∪ {v | v ∈ L})) := by
  induction L with
  | nil => intro _ A _; simp; rfl
  | cons v L ih =>
    intro hn A hA
    have hn' := List.nodup_cons.1 hn
    have h1 := ih hn'.2 A fun u hu => hA u (List.mem_cons_of_mem _ hu)
    have hv : v ∉ A ∪ {v | v ∈ L} := fun h => h.elim (hA v List.mem_cons_self) hn'.1
    obtain ⟨hcl, -, -, hcm⟩ := eigBasic K n μ v (J v) (χ v) (hco v).1 (hco v).2
    have hc : Commute (prj (eigL μ v (J v) (χ v))) (prj (GAx μ J χ (A ∪ {v | v ∈ L}))) :=
      (hcm _ fun x _ => (GA_commute μ hco hv x).symm).symm
    have hs : A ∪ {u | u ∈ v :: L} = insert v (A ∪ {v | v ∈ L}) := by
      ext u; simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]; tauto
    have hG : GAx μ J χ (insert v (A ∪ {v | v ∈ L})) = eigL μ v (J v) (χ v) ⊓ GAx μ J χ (A ∪ {v | v ∈ L}) := by
      simp only [GAx]; rw [iInf_insert]
    rw [List.map_cons, List.prod_cons, hs, hG, ← prj_comp_of_commute hcl (GA_closed μ hco _) hc, ← h1]
    rfl

end Loc

section Haar

private theorem haar_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure]
    (J : Subgroup G) (hJ : CO J) (u : G) (hu : u ∈ J) : MeasurePreserving (· * u) m m := by
  refine ⟨measurable_mul_const u, ?_⟩
  have hpre : ∀ S : Set G, (· * u) ⁻¹' S = (· * u⁻¹) '' S := fun S => by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    exact ⟨fun h => ⟨_, h, by simp⟩, by rintro ⟨y, hy, rfl⟩; simpa using hy⟩
  haveI : (Measure.map (· * u) m).IsMulLeftInvariant := ⟨fun g => by
    rw [Measure.map_map (measurable_const_mul g) (measurable_mul_const u)]
    have : (g * ·) ∘ (· * u) = (· * u) ∘ (g * ·) := by ext; simp [mul_assoc]
    rw [this, ← Measure.map_map (measurable_mul_const u) (measurable_const_mul g), map_mul_left_eq_self]⟩
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * u) m) := ⟨fun C hC => by
    rw [Measure.map_apply (measurable_mul_const u) hC.measurableSet, hpre]
    exact (hC.image (continuous_mul_right _)).measure_lt_top⟩
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * u) m) m
  generalize Measure.haarScalarFactor (Measure.map (· * u) m) m = a at e
  have hJm : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have h1 : (· * u) ⁻¹' (J : Set G) = J := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right J hu
  have h2 : m J = a * m J := by
    have := congrArg (· (J : Set G)) e
    simp only [Measure.map_apply (measurable_mul_const u) hJm, h1] at this
    simpa [Measure.smul_apply] using this
  have h3 : m (J : Set G) ≠ 0 := (hJ.2.measure_pos m ⟨1, J.one_mem⟩).ne'
  have h4 : m (J : Set G) ≠ ⊤ := hJ.1.measure_lt_top.ne
  have ha : (a : ENNReal) = 1 := by
    have h5 : (a : ENNReal) * m J = 1 * m J := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj h3 h4).1 h5
  have ha' : a = 1 := by exact_mod_cast ha
  rw [e, ha', one_smul]

end Haar

section BernoulliSumsFrobeniusOrbits
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem oloc_commute {w v : Pl K} (h : v ≠ w) [MeasurableSpace (Gw n w)] (m : Measure (Gw n w)) (φ : Gw n w → ℂ)
    (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ w m φ T) (x : Gw n v) : Commute T (rhoL μ v x) := by
  refine ContinuousLinearMap.ext fun b => ext_inner_left ℂ fun a => ?_
  show ⟪a, T (rhoL μ v x b)⟫_ℂ = ⟪a, rhoL μ v x (T b)⟫_ℂ
  rw [hT, ← ContinuousLinearMap.adjoint_inner_left, hT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have h1 := congrArg (· b) (rhoL_comm μ h x g)
  simp only [ContinuousLinearMap.comp_apply] at h1
  simp only
  rw [ContinuousLinearMap.adjoint_inner_left, h1]

private theorem oloc_right (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] (m : Measure (Gw n v))
    [m.IsHaarMeasure] {J : Subgroup (Gw n v)} (hJ : CO J) {χ : Gw n v → ℂ} (hχ : IsChr J χ) (ψ : Gw n v → ℂ)
    (hψ : ∀ u ∈ J, ∀ g, ψ (g * u) = conj (χ u) * ψ g) (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ v m ψ T) (u : Gw n v) (hu : u ∈ J)
    (a b : LL μ) : ⟪a, T (rhoL μ v u b)⟫_ℂ = χ u * ⟪a, T b⟫_ℂ := by
  have hn : χ u * conj (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.2.1 u hu]; simp
  have hψ' : ∀ g, ψ (g * u⁻¹) = χ u * ψ g := fun g => by
    have := hψ u hu (g * u⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this, ← mul_assoc, hn, one_mul]
  have hmp := haar_right m J hJ u hu
  have hc := hmp.integral_comp (measurableEmbedding_mulRight u)
    (fun g => ψ (g * u⁻¹) * ⟪a, rhoL μ v g b⟫_ℂ)
  rw [hT, hT, ← integral_const_mul]
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)) (hc.trans
    (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)))
  · simp only [mul_inv_cancel_right, rhoL_mul, ContinuousLinearMap.comp_apply]
  · simp only [hψ', mul_assoc]

private theorem oloc_absorb (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] (m : Measure (Gw n v))
    [m.IsHaarMeasure] {J : Subgroup (Gw n v)} (hJ : CO J) (hm : m J = 1) {χ : Gw n v → ℂ} (hχ : IsChr J χ) (ψ : Gw n v → ℂ)
    (hψ : ∀ u ∈ J, ∀ g, ψ (g * u) = conj (χ u) * ψ g) (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ v m ψ T) :
    T * prj (eigL μ v J χ) = T := by
  obtain ⟨-, -, hP, -⟩ := eigBasic K n μ v J χ hJ hχ
  have hP' := hP m hm
  refine ContinuousLinearMap.ext fun b => ext_inner_left ℂ fun a => ?_
  show ⟪a, T (prj (eigL μ v J χ) b)⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_left, hP']
  have hJm : MeasurableSet (J : Set (Gw n v)) := hJ.2.measurableSet
  have : ∀ x, (J : Set (Gw n v)).indicator (fun x => conj (χ x)) x *
      ⟪ContinuousLinearMap.adjoint T a, rhoL μ v x b⟫_ℂ = (J : Set (Gw n v)).indicator (fun _ => ⟪a, T b⟫_ℂ) x := fun x => by
    by_cases hx : x ∈ (J : Set (Gw n v))
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ContinuousLinearMap.adjoint_inner_left,
        oloc_right μ v m hJ hχ ψ hψ T hT x hx, ← mul_assoc, mul_comm (conj (χ x)), Complex.mul_conj,
        Complex.normSq_eq_norm_sq, hχ.2.1 x hx]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp only [this]
  rw [integral_indicator_const _ hJm]
  simp [Measure.real, hm]

end BernoulliSumsFrobeniusOrbits

private noncomputable def glue {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {n : ℕ} (g : ∀ i, GL (Fin n) (R i)) :
    GL (Fin n) (∀ i, R i) where
  val := Matrix.of fun a b i => (g i : Matrix (Fin n) (Fin n) (R i)) a b
  inv := Matrix.of fun a b i => ((g i)⁻¹ : GL (Fin n) (R i)) a b
  val_inv := by
    ext a b i
    have := congrFun (congrFun (g i).mul_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl
  inv_val := by
    ext a b i
    have := congrFun (congrFun (g i).inv_mul a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl

private theorem glue_cont {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] {n : ℕ} :
    Continuous (glue : (∀ i, GL (Fin n) (R i)) → GL (Fin n) (∀ i, R i)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_coe_inv.comp (continuous_apply i)).matrix_elem a b

private theorem exists_ext {ι A : Type*} {X : A → Type*} (wi : ι → A) (hw : Function.Injective wi)
    (ψ : ∀ i, X (wi i)) (d : ∀ a, X a) :
    ∃ h : ∀ a, X a, (∀ i, h (wi i) = ψ i) ∧ ∀ a, a ∉ Set.range wi → h a = d a := by
  refine ⟨fun a => if ha : ∃ i, wi i = a then ha.choose_spec ▸ ψ ha.choose else d a, fun i => ?_,
    fun a ha => dif_neg ha⟩
  have key : ∀ j (hj : wi j = wi i), (hj ▸ ψ j : X (wi i)) = ψ i := by
    intro j hj
    obtain rfl := hw hj
    rfl
  have ha : ∃ j, wi j = wi i := ⟨i, rfl⟩
  simp only [dif_pos ha]
  exact key _ _

private theorem finprod_split {A M : Type*} [CommMonoid M] {r : ℕ} (wi : Fin r → A) (hw : Function.Injective wi)
    (X : A → M) (hX : (Function.mulSupport X).Finite) :
    ∏ᶠ u, X u = (∏ i, X (wi i)) * ∏ᶠ (u) (_ : u ∉ Set.range wi), X u := by
  have h := finprod_mem_inter_mul_diff' (f := X) (s := Set.univ) (Set.range wi)
    (hX.subset Set.inter_subset_right)
  rw [Set.univ_inter, finprod_mem_univ, finprod_mem_range hw, finprod_eq_prod_of_fintype] at h
  rw [← h]
  congr 1
  refine finprod_congr fun u => ?_
  simp only [Set.mem_diff, Set.mem_univ, true_and]

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem cmp_cont {v : Pl F} (w : PlacesOver E v) : Continuous (GM.cmp (n := n) w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem a b)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_coe_inv.matrix_elem a b)

private theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

private theorem iwCoset_zero (w : Pl E) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w)) := by
  have hd : Cartan.diagPow (w.adicCompletion E) n (0 : Fin n → ℤ) = 1 := by
    apply Units.ext
    rw [Cartan.coe_diagPow]
    simp
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [hd, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [hd, mul_one, mul_one]⟩

private theorem iw_test (w : Pl E) :
    IsLocallyConstant (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) ∧
      HasCompactSupport (((GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))).indicator (1 : Gw n w → ℂ)) := by
  have ho := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hc := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ (GLnLocal.iwahori (w.adicCompletion E) n : Set (Gw n w))
  · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem prodFn_eq {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    [Fintype (PlacesOver E v)] : GM.prodFn h = fun g => ∏ w, h w (GM.cmp w g) :=
  funext fun _ => finprod_eq_prod_of_fintype _

private theorem prodFn_test {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    (hc : ∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) :
    IsLocallyConstant (GM.prodFn h) ∧ HasCompactSupport (GM.prodFn h) := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  rw [prodFn_eq]
  constructor
  · have key : ∀ T : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ T, h w (GM.cmp w g) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hc a).1.comp_continuous (cmp_cont a)).mul ih
    exact key _
  · haveI : T2Space (CompletionsOver E v) := Pi.t2Space
    haveI : T2Space (GL (Fin n) (CompletionsOver E v)) := Units.instT2Space
    haveI : R1Space (GL (Fin n) (CompletionsOver E v)) := T2Space.r1Space
    refine HasCompactSupport.intro ((isCompact_univ_pi fun w => (hc w).2.isCompact).image glue_cont) fun g hg => ?_
    by_contra hne
    refine hg ⟨fun w => GM.cmp w g, fun w _ => subset_tsupport _ ?_, ?_⟩
    · exact fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    · exact Units.ext (Matrix.ext fun a b => rfl)

private theorem unit_prod (v : Pl F) :
    (GM.prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  funext g
  rw [GM.prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hg w) _
  · rw [Set.indicator_of_notMem hg]
    obtain ⟨w, hw⟩ := not_forall.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

private theorem iwFn_test {q : Pl F} (w₀ : PlacesOver E q) :
    IsLocallyConstant (GM.iwFn w₀ (0 : Fin n → ℤ)) ∧ HasCompactSupport (GM.iwFn w₀ (0 : Fin n → ℤ)) := by
  refine prodFn_test _ fun w => ?_
  rw [ite_self, iwCoset_zero]
  exact iw_test w.1

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private noncomputable def dflt (T : Ty σ n q w₀) (w : Pl E) : Gw n w → ℂ :=
  (T.J w : Set (Gw n w)).indicator fun x => conj (T.χ w x)

private theorem dflt_of_triv (T : Ty σ n q w₀) (w : Pl E) (h : T.χ w = 1) :
    dflt T w = (T.J w : Set (Gw n w)).indicator 1 := by
  unfold dflt
  rw [h]
  funext x
  by_cases hx : x ∈ (T.J w : Set (Gw n w))
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

private theorem phi_eq (T : Ty σ n q w₀) (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ)
    (hF : FitsV T L ψ) (hq : GM.Split E q) (huq : ∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v)
    (h : ∀ w : Pl E, Gw n w → ℂ)
    (h1 : ∀ v ∈ T.S, h (T.mk' v).1 = ψ v)
    (h2 : ∀ w : Pl E, (∀ v ∈ T.S, w ≠ (T.mk' v).1) → h w = dflt T w) (v : Pl F) :
    L.φ v = GM.prodFn fun u : PlacesOver E v => h u.1 := by
  have hother : ∀ (u : PlacesOver E v), v ∉ T.S → h u.1 = dflt T u.1 := fun u hv => by
    refine h2 u.1 fun v' hv' e => hv ?_
    have : v' = v := by rw [← under_eq (T.mk' v'), ← e, under_eq u]
    rwa [← this]
  by_cases hS : v ∈ T.S
  · by_cases hs : GM.Split E v
    · have hsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hS, hs⟩
      rw [(hF.split v hsp).1]
      congr 1
      funext u
      by_cases hu : u = T.mk' v
      · subst hu
        rw [Function.update_self, h1 v hS]
      · rw [Function.update_of_ne hu, h2 u.1 fun v' hv' e => hu ?_,
          dflt_of_triv T u.1 (T.triv v hs u)]
        have : v' = v := by rw [← under_eq (T.mk' v'), ← e, under_eq u]
        subst this
        exact Subtype.ext e
    · have hu := huq v (Finset.mem_filter.2 ⟨hS, hs⟩)
      funext g
      rw [hF.nonsplit v hS hs g, GM.prodFn]
      letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, hu⟩
      rw [finprod_unique]
      have hd : (default : PlacesOver E v) = T.mk' v := hu _
      rw [hd, h1 v hS]
  by_cases hvq : v = q
  · subst hvq
    rw [L.at_q.1]
    unfold GM.iwFn
    congr 1
    funext u
    rw [hother u hS, dflt_of_triv T u.1 (T.triv v hq u), ite_self, iwCoset_zero, T.at_q u]
  · have hvS : v ∉ L.S := by rw [hF.S_eq]; exact hS
    rw [(L.off v hvS hvq).1, ← unit_prod v]
    congr 1
    funext u
    have hu := T.off u.1 (by rw [under_eq]; exact hS) (by rw [under_eq]; exact hvq)
    rw [hother u hS, dflt_of_triv T u.1 hu.2, hu.1]

end Main

end UpperTheory.EigenspaceProjectionTraces

set_option maxHeartbeats 2000000 in
open UpperTheory.EigenspaceProjectionTraces in
theorem UpperTheory.exists_pos_const_eigenspace_bound_of_split_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
        ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n)
          (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ T : Ty σ n q w₀,
          (∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v) →
          ∃ κ : ℝ, 0 < κ ∧ ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), FitsV T L ψ →
          ∀ (r₁ : ℕ) (p₁ : Fin r₁ → Pl F), Function.Injective p₁ → (∀ v, v ∈ T.sp ↔ v ∈ Set.range p₁) →
          ∀ (r₂ : ℕ) (p₂ : Fin r₂ → Pl F), Function.Injective p₂ → (∀ v, v ∈ nsS T ↔ v ∈ Set.range p₂) →
          ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (mm : ∀ u : Pl E, Measure (Gw n u)),
            (∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1) →
          ∀ (B₁ : Fin r₁ → LL μ →L[ℂ] LL μ) (B₂ : Fin r₂ → LL μ →L[ℂ] LL μ),
            (∀ i, IsOloc μ (T.mk' (p₁ i)).1 (mm _) (ψ (p₁ i)) (B₁ i)) → (∀ i, IsOloc μ (T.mk' (p₂ i)).1 (mm _) (ψ (p₂ i)) (B₂ i)) →
          ∀ g : TG E n, (∀ x, g x = avg (tensE (GM.onInf aE) L.φ) x) →
            Rop μ g = (κ : ℂ) • (Oinf μ νE aE ∘L (List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) := by
  intro F E _ _ _ _ _ σ n hn μ _ νE _ aE q w₀ hq T huq
  have hfin : {w : Pl E | w.under (𝓞 F) ∈ ((insert q T.S : Finset (Pl F)) : Set (Pl F))}.Finite :=
    finite_under _ (Finset.finite_toSet _)
  have hcof : ∀ᶠ w : Pl E in Filter.cofinite,
      w.under (𝓞 F) ∉ T.S ∧ w.under (𝓞 F) ≠ q := by
    refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
    simp only [Set.mem_setOf_eq, not_and_or, not_not] at hw
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    tauto
  have hco : ∀ w, CO (T.J w) ∧ IsChr (T.J w) (T.χ w) := fun w => ⟨T.co w, T.chr w⟩
  obtain ⟨κ, hκ, H⟩ := UpperTheory.exists_bound_dim_simultaneousLocalEigenspace_of_openCompact E n hn μ νE T.J T.χ hco (hcof.mono fun w hw => T.off w hw.1 hw.2)
  refine ⟨κ, hκ, ?_⟩
  intro L ψ hF r₁ p₁ hp₁ hsp₁ r₂ p₂ hp₂ hns₂ _ _ mm hmm B₁ B₂ hB₁ hB₂ g hg
  haveI hmI : ∀ u, (mm u).IsHaarMeasure := fun u => (hmm u).1
  let pp : Fin (r₁ + r₂) → Pl F := Fin.append p₁ p₂
  let B : Fin (r₁ + r₂) → LL μ →L[ℂ] LL μ := Fin.append B₁ B₂
  have hl : ∀ i, pp (Fin.castAdd r₂ i) = p₁ i := fun i => Fin.append_left _ _ _
  have hr : ∀ j, pp (Fin.natAdd r₁ j) = p₂ j := fun j => Fin.append_right _ _ _
  have hBl : ∀ i, B (Fin.castAdd r₂ i) = B₁ i := fun i => Fin.append_left _ _ _
  have hBr : ∀ j, B (Fin.natAdd r₁ j) = B₂ j := fun j => Fin.append_right _ _ _
  have h1sp : ∀ i, p₁ i ∈ T.sp := fun i => (hsp₁ _).2 ⟨i, rfl⟩
  have h2ns : ∀ j, p₂ j ∈ nsS T := fun j => (hns₂ _).2 ⟨j, rfl⟩
  have hsplit1 : ∀ i, GM.Split E (p₁ i) := fun i => (Finset.mem_filter.1 (h1sp i)).2
  have hsplit2 : ∀ j, ¬ GM.Split E (p₂ j) := fun j => (Finset.mem_filter.1 (h2ns j)).2
  have hne : ∀ i j, p₁ i ≠ p₂ j := fun i j e => hsplit2 j (e ▸ hsplit1 i)
  have hpp : Function.Injective pp := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro h
    · rw [hl, hl] at h; rw [hp₁ h]
    · rw [hl, hr] at h; exact absurd h (hne i j)
    · rw [hr, hl] at h; exact absurd h.symm (hne j i)
    · rw [hr, hr] at h; rw [hp₂ h]
  have hpS : ∀ i, pp i ∈ T.S := fun i => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [hl]; exact (Finset.mem_filter.1 (h1sp i)).1
    · rw [hr]; exact (Finset.mem_filter.1 (h2ns j)).1
  have hsurj : ∀ v ∈ T.S, ∃ i, pp i = v := fun v hv => by
    by_cases hs : GM.Split E v
    · obtain ⟨i, rfl⟩ := (hsp₁ v).1 (Finset.mem_filter.2 ⟨hv, hs⟩)
      exact ⟨_, hl i⟩
    · obtain ⟨j, rfl⟩ := (hns₂ v).1 (Finset.mem_filter.2 ⟨hv, hs⟩)
      exact ⟨_, hr j⟩
  have hOl : ∀ i, IsOloc μ (T.mk' (pp i)).1 (mm _) (ψ (pp i)) (B i) := fun i => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [hBl]
      have := hB₁ i
      rw [← hl i] at this
      exact this
    · rw [hBr]
      have := hB₂ j
      rw [← hr j] at this
      exact this
  have hwi : Function.Injective fun i => (T.mk' (pp i)).1 := fun i j e => hpp (by
    have e' : (T.mk' (pp i)).1 = (T.mk' (pp j)).1 := e
    rw [← under_eq (T.mk' (pp i)), e', under_eq])
  obtain ⟨h, hh1, hh2⟩ := exists_ext (X := fun w : Pl E => Gw n w → ℂ) (fun i => (T.mk' (pp i)).1) hwi
    (fun i => ψ (pp i)) (dflt T)
  have h1 : ∀ v ∈ T.S, h (T.mk' v).1 = ψ v := fun v hv => by
    obtain ⟨i, rfl⟩ := hsurj v hv
    exact hh1 i
  have h2 : ∀ w : Pl E, (∀ v ∈ T.S, w ≠ (T.mk' v).1) → h w = dflt T w := fun w hw =>
    hh2 w fun ⟨i, e⟩ => hw _ (hpS i) e.symm
  have hφ := phi_eq T L ψ hF hq huq h h1 h2
  have hint : ∀ᶠ w : Pl E in Filter.cofinite,
      h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator 1 := by
    refine hcof.mono fun w hw => ?_
    have hu := T.off w hw.1 hw.2
    have hne : ∀ v ∈ T.S, w ≠ (T.mk' v).1 := fun v hv e => hw.1 (by
      rw [e, under_eq]; exact hv)
    rw [h2 w hne, dflt_of_triv T w hu.2, hu.1]
  obtain ⟨e, -, he, ht⟩ := GM.avgE F E n hn (insert q L.S) aE L.φ (fun v hv => by
      rcases Finset.mem_insert.1 hv with hvq | hv
      · rw [hvq, L.at_q.1]; exact iwFn_test w₀
      · exact ⟨(L.test v hv).1, (L.test v hv).2.1⟩)
    (fun v hv => (L.off v (fun h => hv (Finset.mem_insert_of_mem h))
      (fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _))).1)
  have hgt : g = tens aE e := by
    ext x
    rw [hg, ht]
  have heform : ∀ x, e x = (∏ i, ψ (pp i) (finAt (T.mk' (pp i)).1 (finEmb E n x))) *
      ∏ᶠ u ∉ Set.range (fun i => (T.mk' (pp i)).1), (T.J u : Set (Gw n u)).indicator (fun g => conj (T.χ u g)) (finAt u (finEmb E n x)) := by
    intro x
    have e1 : e x = ∏ᶠ w, h w (finAt w (finEmb E n x)) := by
      rw [he x, ← UpperTheory.ConvolutionTheory.Tf.tensEProd F E n h hint (finEmb E n x)]
      exact finprod_congr fun v => by rw [hφ v]
    have hsupp : (Function.mulSupport fun w : Pl E => h w (finAt w (finEmb E n x))).Finite := by
      have hev : ∀ᶠ w : Pl E in Filter.cofinite, h w (finAt w (finEmb E n x)) = 1 := by
        filter_upwards [hint, AdelicGLn.eventually_mem_integralGL E n (finEmb E n x)] with w a1 a2
        rw [a1, Set.indicator_of_mem (by exact a2)]
        rfl
      exact Filter.eventually_cofinite.1 hev
    rw [e1, finprod_split _ hwi _ hsupp]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [hh1 i]
    · refine finprod_congr fun u => finprod_congr fun hu => ?_
      rw [hh2 u hu]
      rfl
  have main := H aE (r₁ + r₂) (fun i => (T.mk' (pp i)).1) hwi (fun i => mm _) (fun i => hmm _)
    (fun i => ψ (pp i)) B (fun i => ⟨hF.test _ (hpS i), hOl i⟩) e heform

  let wsp : Fin r₁ → Pl E := fun i => (T.mk' (p₁ i)).1
  have hwsp : Function.Injective wsp := fun i j e => hp₁ (by
    have e' : (T.mk' (p₁ i)).1 = (T.mk' (p₁ j)).1 := e
    rw [← under_eq (T.mk' (p₁ i)), e', under_eq])
  have hwsp_mem : ∀ i, wsp i ∈ Set.range fun i => (T.mk' (pp i)).1 := fun i =>
    ⟨Fin.castAdd r₂ i, by
      show (T.mk' (pp (Fin.castAdd r₂ i))).1 = (T.mk' (p₁ i)).1
      rw [hl]⟩
  have hlist := list_prj μ hco (List.ofFn wsp) (List.nodup_ofFn.2 hwsp)
    {u | u ∉ Set.range fun i => (T.mk' (pp i)).1} (fun v hv hc => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hv
      exact hc (hwsp_mem i))
  have hset : {u | u ∉ Set.range fun i => (T.mk' (pp i)).1} ∪ {v | v ∈ List.ofFn wsp} =
      {u : Pl E | u.under (𝓞 F) ∉ (nsS T : Set (Pl F))} := by
    ext u
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hu | hu) hn'
      · have hn2 : u.under (𝓞 F) ∈ nsS T := hn'
        refine hu ?_
        have hu' := huq _ hn2 ⟨u, liesOver_under u⟩
        obtain ⟨i, hi⟩ := hsurj _ (Finset.mem_filter.1 hn2).1
        refine ⟨i, ?_⟩
        show (T.mk' (pp i)).1 = u
        rw [hi]
        exact (congrArg Subtype.val hu').symm
      · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hu
        have hn2 : (wsp i).under (𝓞 F) ∈ nsS T := hn'
        rw [show (wsp i).under (𝓞 F) = p₁ i from under_eq _] at hn2
        exact (Finset.mem_filter.1 hn2).2 (hsplit1 i)
    · intro hu
      by_cases hr' : u ∈ Set.range fun i => (T.mk' (pp i)).1
      · right
        obtain ⟨i, rfl⟩ := hr'
        revert hu
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i
        · intro _
          refine (List.mem_ofFn' _ _).2 ⟨i, ?_⟩
          show (T.mk' (p₁ i)).1 = (T.mk' (pp (Fin.castAdd r₂ i))).1
          rw [hl]
        · intro hu
          have hin : ((T.mk' (pp (Fin.natAdd r₁ j))).1).under (𝓞 F) ∈ (nsS T : Set (Pl F)) := by
            rw [under_eq, hr]
            exact h2ns j
          exact absurd hin hu
      · exact Or.inl hr'
  have hoff : GAx μ T.J T.χ ({u | u ∉ Set.range fun i => (T.mk' (pp i)).1} ∪ {v | v ∈ List.ofFn wsp}) = offN μ T := by
    rw [hset]
    simp only [GAx, offN, Set.mem_setOf_eq]
  have hQ : GAx μ T.J T.χ {u | u ∉ Set.range fun i => (T.mk' (pp i)).1} =
      ⨅ (u : Pl E) (_ : u ∉ Set.range fun i => (T.mk' (pp i)).1), eigL μ u (T.J u) (T.χ u) := by
    simp only [GAx, Set.mem_setOf_eq]
  rw [hoff, hQ, List.map_ofFn] at hlist
  set P : LL μ →L[ℂ] LL μ := (List.ofFn fun i => prj (eigL μ (wsp i) (T.J (wsp i)) (T.χ (wsp i)))).prod with hP
  have hlist' : P * prj (⨅ (u : Pl E) (_ : u ∉ Set.range fun i => (T.mk' (pp i)).1), eigL μ u (T.J u) (T.χ u)) =
      prj (offN μ T) := hlist
  have habs : (List.ofFn B₁).prod = (List.ofFn B₁).prod * P := ofFn_absorb r₁ B₁ (fun i => prj (eigL μ (wsp i) (T.J (wsp i)) (T.χ (wsp i))))
    (fun i j hij => (eigBasic E n μ (wsp j) (T.J (wsp j)) (T.χ (wsp j)) (hco _).1 (hco _).2).2.2.2 (B₁ i)
      fun x _ => oloc_commute μ (fun e => hij (hwsp e).symm) (mm _) (ψ (p₁ i)) (B₁ i) (hB₁ i) x)
    fun i => oloc_absorb μ (wsp i) (mm _) (hco _).1 (hmm _).2 (hco _).2 (ψ (p₁ i)) (fun u hu g' => by
      rw [((hF.inv _ (h1sp i)) u hu g').2, T.triv (p₁ i) (hsplit1 i) (T.mk' (p₁ i))]
      simp) (B₁ i) (hB₁ i)
  have hcomm : Commute (List.ofFn B₂).prod P := by
    refine Commute.list_prod_left _ _ fun X hX => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hX
    refine Commute.list_prod_right _ _ fun Y hY => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hY
    refine (eigBasic E n μ (wsp i) (T.J (wsp i)) (T.χ (wsp i)) (hco _).1 (hco _).2).2.2.2 (B₂ j)
      fun x _ => oloc_commute μ (fun e => ?_) (mm _) (ψ (p₂ j)) (B₂ j) (hB₂ j) x
    have e' : (T.mk' (p₁ i)).1 = (T.mk' (p₂ j)).1 := e
    exact hne i j (by rw [← under_eq (T.mk' (p₁ i)), e', under_eq])
  have hprod : (List.ofFn B).prod = (List.ofFn B₁).prod * (List.ofFn B₂).prod := by
    show (List.ofFn (Fin.append B₁ B₂)).prod = _
    rw [List.ofFn_fin_append, List.prod_append]
  have key : (List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T) =
      ((List.ofFn B₁).prod * (List.ofFn B₂).prod) ∘L
        prj (⨅ (u : Pl E) (_ : u ∉ Set.range fun i => (T.mk' (pp i)).1), eigL μ u (T.J u) (T.χ u)) :=
    ops_key _ _ _ _ _ habs hcomm.eq hlist'
  rw [hprod] at main
  rw [hgt, key]
  exact main
