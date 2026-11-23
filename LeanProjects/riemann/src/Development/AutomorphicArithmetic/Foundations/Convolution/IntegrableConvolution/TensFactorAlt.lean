import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped ComplexConjugate InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

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

private theorem ofFn_smul {A : Type*} [Semiring A] [Algebra ℂ A] : ∀ (r : ℕ) (a : Fin r → ℂ) (X : Fin r → A),
    (List.ofFn fun i => a i • X i).prod = (∏ i, a i) • (List.ofFn X).prod := by
  intro r
  induction r with
  | zero => intro a X; simp
  | succ r ih =>
    intro a X
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ih (fun i => a i.succ) (fun i => X i.succ), smul_mul_smul_comm]

private theorem dep_extend {ι α : Type*} {β : α → Type*} (w : ι → α) (hw : Function.Injective w) (ψ : ∀ i, β (w i))
    (d : ∀ v, β v) : ∃ f : ∀ v, β v, (∀ i, f (w i) = ψ i) ∧ ∀ v, v ∉ Set.range w → f v = d v := by
  classical
  refine ⟨fun v => if h : ∃ i, w i = v then h.choose_spec ▸ ψ h.choose else d v, fun i => ?_, fun v hv => ?_⟩
  · have h : ∃ j, w j = w i := ⟨i, rfl⟩
    dsimp only
    rw [dif_pos h]
    have e : h.choose = i := hw h.choose_spec
    generalize h.choose_spec = hs
    revert hs
    rw [e]
    intro hs
    rfl
  · exact dif_neg hv

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

private def GA (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (A : Set (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ u ∈ A, eigL μ u (J u) (χ u)

variable {J : ∀ w : Pl K, Subgroup (Gw n w)} {χ : ∀ w : Pl K, Gw n w → ℂ}

private theorem GA_closed (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) (A : Set (Pl K)) :
    IsClosed (GA μ J χ A : Set (LL μ)) := by
  simp only [GA, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    (eigBasic K n μ u (J u) (χ u) (hco u).1 (hco u).2).1

private theorem mem_eigL {w : Pl K} {J' : Subgroup (Gw n w)} {χ' : Gw n w → ℂ} {x : LL μ} :
    x ∈ eigL μ w J' χ' ↔ ∀ y ∈ J', rhoL μ w y x = χ' y • x := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem GA_stable {A : Set (Pl K)} {v : Pl K} (hv : v ∉ A) (g : Gw n v) (x : LL μ) (hx : x ∈ GA μ J χ A) :
    rhoL μ v g x ∈ GA μ J χ A := by
  simp only [GA, Submodule.mem_iInf] at hx ⊢
  intro u hu
  refine (mem_eigL μ).2 fun y hy => ?_
  have hne : u ≠ v := fun h => hv (h ▸ hu)
  have h1 := congrArg (· x) (rhoL_comm μ hne y g)
  simp only [ContinuousLinearMap.comp_apply] at h1
  rw [h1, (mem_eigL μ).1 (hx u hu) y hy, map_smul]

private theorem GA_commute (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) {A : Set (Pl K)} {v : Pl K} (hv : v ∉ A) (g : Gw n v) :
    Commute (rhoL μ v g) (prj (GA μ J χ A)) := by
  refine prj_commute (GA_closed μ hco A) _ (GA_stable μ hv g) fun x hx => ?_
  rw [rhoL_adj]
  exact GA_stable μ hv _ x hx

private theorem list_prj (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) (L : List (Pl K)) :
    L.Nodup → ∀ (A : Set (Pl K)), (∀ v ∈ L, v ∉ A) →
    (L.map fun v => prj (eigL μ v (J v) (χ v))).prod ∘L prj (GA μ J χ A) = prj (GA μ J χ (A ∪ {v | v ∈ L})) := by
  induction L with
  | nil => intro _ A _; simp; rfl
  | cons v L ih =>
    intro hn A hA
    have hn' := List.nodup_cons.1 hn
    have h1 := ih hn'.2 A fun u hu => hA u (List.mem_cons_of_mem _ hu)
    have hv : v ∉ A ∪ {v | v ∈ L} := fun h => h.elim (hA v List.mem_cons_self) hn'.1
    obtain ⟨hcl, -, -, hcm⟩ := eigBasic K n μ v (J v) (χ v) (hco v).1 (hco v).2
    have hc : Commute (prj (eigL μ v (J v) (χ v))) (prj (GA μ J χ (A ∪ {v | v ∈ L}))) :=
      (hcm _ fun x _ => (GA_commute μ hco hv x).symm).symm
    have hs : A ∪ {u | u ∈ v :: L} = insert v (A ∪ {v | v ∈ L}) := by
      ext u; simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]; tauto
    have hG : GA μ J χ (insert v (A ∪ {v | v ∈ L})) = eigL μ v (J v) (χ v) ⊓ GA μ J χ (A ∪ {v | v ∈ L}) := by
      simp only [GA]; rw [iInf_insert]
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

private theorem oloc_scale (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] (m m₂ : Measure (Gw n v))
    [m.IsHaarMeasure] [m₂.IsHaarMeasure] {J : Subgroup (Gw n v)} (hJ : m J = 1) (φ : Gw n v → ℂ)
    (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ v m φ T) : IsOloc μ v m₂ φ (((m₂.real J : ℝ) : ℂ) • T) := by
  obtain ⟨a, e⟩ : ∃ a : NNReal, m₂ = a • m := ⟨_, Measure.isMulLeftInvariant_eq_smul m₂ m⟩
  subst e
  have ha : (a • m).real (J : Set (Gw n v)) = a := by
    simp [Measure.real, hJ]
  intro x y
  rw [ha, ContinuousLinearMap.smul_apply, inner_smul_right, hT, integral_smul_nnreal_measure]
  rfl

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

section SlopeTestRemainingChoices
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem finAt_eq (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
  show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2) v = _
  rw [prodEquiv_finEmb]

open scoped Classical in
private theorem mem_levOn (P : Finset (Pl K)) (h : AdelicGLn.FiniteAdelicGL K n) :
    h ∈ levOn P (fun v => (⊥ : Subgroup (Gw n v))) ↔
      h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ v ∈ P, finAt v (finEmb K n h) = 1 := by
  have e : h ∈ levOn P (fun v => (⊥ : Subgroup (Gw n v))) ↔ ∀ v, finAt v (finEmb K n h) ∈
      (if v ∈ P then (⊥ : Subgroup (Gw n v)) else GLnLocal.integralGL (v.adicCompletion K) n) := Iff.rfl
  rw [e, AdelicGLn.mem_integralFiniteGL_iff_forall]
  constructor
  · intro H
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have h1 := H v
      rw [← finAt_eq]
      split_ifs at h1 with hv
      · rw [Subgroup.mem_bot] at h1; rw [h1]; exact one_mem _
      · exact h1
    · have h1 := H v
      rw [if_pos hv] at h1
      exact Subgroup.mem_bot.1 h1
  · rintro ⟨H1, H2⟩ v
    split_ifs with hv
    · exact Subgroup.mem_bot.2 (H2 v hv)
    · rw [finAt_eq]; exact H1 v

private theorem fixL_bot (v : Pl K) : fixL μ v (⊥ : Subgroup (Gw n v)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  show x ∈ fixF μ _
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 x).2 fun u hu => ?_
  rw [Subgroup.map_bot, Subgroup.mem_bot] at hu
  subst hu
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.1]
  rfl

private theorem sph_eq {J : ∀ w : Pl K, Subgroup (Gw n w)} {χ : ∀ w : Pl K, Gw n w → ℂ}
    (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w)) (W : Finset (Pl K))
    (hW : ∀ v ∉ W, J v = GLnLocal.integralGL (v.adicCompletion K) n ∧ χ v = 1) :
    sphOff μ W = GA μ J χ {v | v ∉ W} := by
  simp only [sphOff, GA, Set.mem_setOf_eq]
  refine iInf_congr fun v => iInf_congr fun hv => ?_
  obtain ⟨h1, h2⟩ := hW v hv
  have e := (eigBasic K n μ v (J v) (χ v) (hco v).1 (hco v).2).2.1
  rw [h2, e, h1]

private theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · have hcl : IsClosed (J : Set G) := Subgroup.isClosed_of_isOpen J hJ.2
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem finprod_split {ι α : Type*} [Fintype ι] (w : ι → α) (hw : Function.Injective w) (F : α → ℂ)
    (hF : (Function.mulSupport F).Finite) : ∏ᶠ v, F v = (∏ i, F (w i)) * ∏ᶠ (u) (_ : u ∉ Set.range w), F u := by
  have h := finprod_mem_inter_mul_diff' (f := F) (s := Set.univ) (Set.range w) (hF.subset Set.inter_subset_right)
  rw [Set.univ_inter, finprod_mem_range hw, finprod_eq_prod_of_fintype, finprod_mem_univ] at h
  rw [← h]
  congr 1
  refine finprod_congr fun u => ?_
  simp [Set.mem_diff]

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

set_option maxHeartbeats 2000000 in
theorem UpperTheory.ConvolutionTheory.L1.tensFactor :
    UpperTheory.ConvolutionTheory.L1.TensFactor := by
  intro K _ _ n hn μ _ ν _ J χ hco hcof
  classical
  letI bm : ∀ v : Pl K, MeasurableSpace (Gw n v) := fun v => borel _
  haveI bs : ∀ v : Pl K, BorelSpace (Gw n v) := fun v => ⟨rfl⟩
  have hOc : ∀ v : Pl K, IsCompact ((GLnLocal.integralGL (v.adicCompletion K) n : Subgroup (Gw n v)) : Set (Gw n v)) :=
    fun v => GLnLocal.isCompact_integralGL _ n
  have hOo : ∀ v : Pl K, IsOpen ((GLnLocal.integralGL (v.adicCompletion K) n : Subgroup (Gw n v)) : Set (Gw n v)) :=
    fun v => GLnLocal.isOpen_integralGL _ n
  let KO : ∀ v : Pl K, TopologicalSpace.PositiveCompacts (Gw n v) := fun v =>
    ⟨⟨_, hOc v⟩, ⟨1, mem_interior_iff_mem_nhds.2 ((hOo v).mem_nhds (one_mem _))⟩⟩
  let KJ : ∀ v : Pl K, TopologicalSpace.PositiveCompacts (Gw n v) := fun v =>
    ⟨⟨_, (hco v).1.1⟩, ⟨1, mem_interior_iff_mem_nhds.2 ((hco v).1.2.mem_nhds (one_mem _))⟩⟩
  let mO : ∀ v : Pl K, Measure (Gw n v) := fun v => Measure.haarMeasure (KO v)
  let mJ : ∀ v : Pl K, Measure (Gw n v) := fun v => Measure.haarMeasure (KJ v)
  haveI hOH : ∀ v, (mO v).IsHaarMeasure := fun v => by dsimp only [mO]; infer_instance
  haveI hJH : ∀ v, (mJ v).IsHaarMeasure := fun v => by dsimp only [mJ]; infer_instance
  have hmO : ∀ v : Pl K, mO v (GLnLocal.integralGL (v.adicCompletion K) n : Subgroup (Gw n v)) = 1 :=
    fun v => Measure.haarMeasure_self (K₀ := KO v)
  have hmJ : ∀ v : Pl K, mJ v (J v) = 1 := fun v => Measure.haarMeasure_self (K₀ := KJ v)
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  have hBad := Filter.eventually_cofinite.1 hcof
  let c : Pl K → ℝ := fun v => (mO v).real (J v)
  have hc1 : ∀ v, v ∉ hBad.toFinset → c v = 1 := fun v hv => by
    have h : J v = GLnLocal.integralGL (v.adicCompletion K) n ∧ χ v = 1 := by
      by_contra h; exact hv (hBad.mem_toFinset.2 h)
    show (mO v).real (J v) = 1
    rw [h.1, Measure.real, hmO]; rfl
  have hc0 : ∀ v, 0 < c v := fun v =>
    ENNReal.toReal_pos ((hco v).1.2.measure_pos (mO v) ⟨1, (J v).one_mem⟩).ne' (hco v).1.1.measure_lt_top.ne
  refine ⟨m.real (AdelicGLn.integralFiniteGL K n) * ∏ v ∈ hBad.toFinset, c v, mul_pos
    (ENNReal.toReal_pos ((AdelicGLn.isOpen_integralFiniteGL K n).measure_pos m ⟨1, one_mem _⟩).ne'
      (AdelicGLn.isCompact_integralFiniteGL K n).measure_lt_top.ne) (Finset.prod_pos fun v _ => hc0 v), ?_⟩
  intro β r w hw inst bor mm hmm ψ T hT e he
  obtain rfl : inst = fun i => bm (w i) := funext fun i => (bor i).measurable_eq
  haveI hmI : ∀ i, (mm i).IsHaarMeasure := fun i => (hmm i).1

  let B0 : Finset (Pl K) := hBad.toFinset.filter (· ∉ Set.range w)
  let b : Fin B0.card → Pl K := fun j => (B0.equivFin.symm j).1
  have hbinj : Function.Injective b := fun i j h => B0.equivFin.symm.injective (Subtype.ext h)
  have hbB : ∀ j, b j ∈ B0 := fun j => (B0.equivFin.symm j).2
  have hbw : ∀ j, b j ∉ Set.range w := fun j => (Finset.mem_filter.1 (hbB j)).2
  have hbs : ∀ v ∈ B0, ∃ j, b j = v := fun v hv => ⟨B0.equivFin ⟨v, hv⟩, by simp [b]⟩
  let w' : Fin (r + B0.card) → Pl K := Fin.append w b
  have hw'l : ∀ i, w' (Fin.castAdd _ i) = w i := fun i => Fin.append_left _ _ _
  have hw'r : ∀ j, w' (Fin.natAdd _ j) = b j := fun j => Fin.append_right _ _ _
  have hw' : Function.Injective w' := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro h
    · rw [hw'l, hw'l] at h; rw [hw h]
    · rw [hw'l, hw'r] at h; exact absurd ⟨i, h⟩ (hbw j)
    · rw [hw'r, hw'l] at h; exact absurd ⟨j, h.symm⟩ (hbw i)
    · rw [hw'r, hw'r] at h; rw [hbinj h]
  have hrange : ∀ v, v ∉ Set.range w' → v ∉ Set.range w ∧ v ∉ hBad.toFinset := fun v hv => by
    have h1 : v ∉ Set.range w := fun ⟨i, hi⟩ => hv ⟨Fin.castAdd _ i, by rw [hw'l, hi]⟩
    refine ⟨h1, fun h2 => ?_⟩
    obtain ⟨j, hj⟩ := hbs v (Finset.mem_filter.2 ⟨h2, h1⟩)
    exact hv ⟨Fin.natAdd _ j, by rw [hw'r, hj]⟩
  have hgood : ∀ v, v ∉ hBad.toFinset → J v = GLnLocal.integralGL (v.adicCompletion K) n ∧ χ v = 1 := fun v hv => by
    by_contra h; exact hv (hBad.mem_toFinset.2 h)

  obtain ⟨X, hXw, hXd⟩ := dep_extend (β := fun _ : Pl K => LL μ →L[ℂ] LL μ) w hw T
    (fun v => prj (eigL μ v (J v) (χ v)))
  obtain ⟨f, hfw, hfd⟩ := dep_extend (β := fun v : Pl K => Gw n v → ℂ) w hw ψ
    (fun v => (J v : Set (Gw n v)).indicator fun g => conj (χ v g))
  have hfTest : ∀ v, Test (f v) := fun v => by
    by_cases hv : v ∈ Set.range w
    · obtain ⟨i, rfl⟩ := hv
      rw [hfw]; exact (hT i).1
    · rw [hfd v hv]; exact test_ind (hco v).1 (hco v).2
  have hfOff : ∀ v, v ∉ Set.range w' →
      f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1 := fun v hv => by
    obtain ⟨h1, h2⟩ := hrange v hv
    obtain ⟨h3, h4⟩ := hgood v h2
    rw [hfd v h1, h3, h4]
    refine Set.indicator_congr fun x _ => ?_
    simp
  have hOl : ∀ v, IsOloc μ v (mO v) (f v) (((c v : ℝ) : ℂ) • X v) := fun v => by
    by_cases hv : v ∈ Set.range w
    · obtain ⟨i, rfl⟩ := hv
      rw [hfw, hXw]
      exact oloc_scale μ (w i) (mm i) (mO (w i)) (hmm i).2 (ψ i) (T i) (hT i).2.2
    · rw [hfd v hv, hXd v hv]
      exact oloc_scale μ v (mJ v) (mO v) (hmJ v) _ _
        ((eigBasic K n μ v (J v) (χ v) (hco v).1 (hco v).2).2.2.1 (mJ v) (hmJ v))
  obtain ⟨e', he', -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.finTens K n μ m (r + B0.card) w' hw' f (fun i => hfTest _) hfOff
  have hee : e' = e := by
    refine DFunLike.ext _ _ fun x => ?_
    have hfin : (Function.mulSupport fun v => f v (finAt v (finEmb K n x))).Finite := by
      have h1 := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))
      refine ((Set.finite_range w').union h1).subset fun v hv => ?_
      by_contra hc
      simp only [Set.mem_union, not_or] at hc
      refine hv ?_
      show f v (finAt v (finEmb K n x)) = 1
      rw [hfOff v hc.1]
      have h2 : finAt v (finEmb K n x) ∈ (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)) := by
        by_contra h3; exact hc.2 h3
      rw [Set.indicator_of_mem h2]
      rfl
    rw [he', he x, finprod_split w hw _ hfin]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [hfw]
    · refine finprod_congr fun u => finprod_congr fun hu => ?_
      rw [hfd u hu]
  subst hee
  let W : Finset (Pl K) := Finset.univ.image w'
  have hWm : ∀ v, v ∉ W → v ∉ Set.range w' := fun v hv ⟨i, hi⟩ =>
    hv (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
  have h1 := hop (fun i => mO (w' i)) (fun i => hOH _) (fun i => hmO _)
    (fun i => ((c (w' i) : ℝ) : ℂ) • X (w' i)) (fun i => hOl _)
    (levOn W fun v => (⊥ : Subgroup (Gw n v))) (fun h => by
      rw [mem_levOn]
      simp only [W, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff])
  have hQ : fixF μ (levOn W fun v => (⊥ : Subgroup (Gw n v))) = GA μ J χ {v | v ∉ W} := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ W _]
    simp only [fixL_bot, iInf_top, inf_top_eq]
    exact sph_eq μ hco W fun v hv => hgood v (hrange v (hWm v hv)).2
  have hlist := list_prj μ hco (List.ofFn w') (List.nodup_ofFn.2 hw') {v | v ∉ W} (fun v hv h => h (by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hv
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
  have hU : {v | v ∉ W} ∪ {v | v ∈ List.ofFn w'} = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    by_cases hv : v ∈ W
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      exact Or.inr ((List.mem_ofFn' _ _).2 ⟨i, rfl⟩)
    · exact Or.inl hv
  have hGU : GA μ J χ Set.univ = ⨅ u, eigL μ u (J u) (χ u) := by simp [GA]
  have hXlist : (List.ofFn fun i => X (w' i)).prod =
      (List.ofFn T).prod * (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod := by
    have : (fun i => X (w' i)) = Fin.append T (fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [hw'l, Fin.append_left, hXw]
      · rw [hw'r, Fin.append_right, hXd _ (hbw j)]
    rw [this, List.ofFn_fin_append, List.prod_append]
  have hPlist : ((List.ofFn w').map fun v => prj (eigL μ v (J v) (χ v))).prod =
      (List.ofFn fun i => prj (eigL μ (w i) (J (w i)) (χ (w i)))).prod *
        (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod := by
    show ((List.ofFn (Fin.append w b)).map _).prod = _
    rw [List.ofFn_fin_append, List.map_append, List.prod_append, List.map_ofFn, List.map_ofFn]
    rfl
  have habs := ofFn_absorb r T (fun i => prj (eigL μ (w i) (J (w i)) (χ (w i))))
    (fun i j hij => (eigBasic K n μ (w j) (J (w j)) (χ (w j)) (hco _).1 (hco _).2).2.2.2 (T i)
      fun x _ => oloc_commute μ (fun h => hij (hw h).symm) (mm i) (ψ i) (T i) (hT i).2.2 x)
    fun i => oloc_absorb μ (w i) (mm i) (hco _).1 (hmm i).2 (hco _).2 (ψ i) (hT i).2.1 (T i) (hT i).2.2
  have hmain : (List.ofFn fun i => ((c (w' i) : ℝ) : ℂ) • X (w' i)).prod =
      (∏ i, ((c (w' i) : ℝ) : ℂ)) • (List.ofFn fun i => X (w' i)).prod := ofFn_smul _ _ _
  have hsub : hBad.toFinset ⊆ W := fun v hv => by
    by_contra h
    exact (hrange v (hWm v h)).2 hv
  have hprodc : ∏ i, ((c (w' i) : ℝ) : ℂ) = ((∏ v ∈ hBad.toFinset, c v : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    calc ∏ i, c (w' i) = ∏ v ∈ W, c v := (Finset.prod_image fun _ _ _ _ h => hw' h).symm
      _ = ∏ v ∈ hBad.toFinset, c v := (Finset.prod_subset hsub fun v _ hv => hc1 v hv).symm
  have key : ((List.ofFn T).prod * (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod) ∘L
      prj (GA μ J χ {v | v ∉ W}) = (List.ofFn T).prod ∘L prj (⨅ u, eigL μ u (J u) (χ u)) := by
    calc _ = ((List.ofFn T).prod * ((List.ofFn fun i => prj (eigL μ (w i) (J (w i)) (χ (w i)))).prod *
          (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod)) ∘L prj (GA μ J χ {v | v ∉ W}) := by
          rw [← mul_assoc, ← habs]
      _ = (List.ofFn T).prod ∘L (((List.ofFn w').map fun v => prj (eigL μ v (J v) (χ v))).prod ∘L
          prj (GA μ J χ {v | v ∉ W})) := by rw [hPlist]; rfl
      _ = _ := by rw [hlist, hU, hGU]
  rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC β e', h1, hmain, hXlist, hprodc, hQ,
    ContinuousLinearMap.smul_comp, key, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, smul_smul]
  push_cast
  rfl
