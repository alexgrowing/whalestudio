import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

noncomputable section

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

section BernoulliSumsFrobeniusOrbits
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

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
theorem UpperTheory.exists_bound_dim_simultaneousLocalEigenspace_of_openCompact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
        (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ),
        (∀ w, CO (J w) ∧ IsChr (J w) (χ w)) →
        (∀ᶠ w in Filter.cofinite, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) → ∃ κ : ℝ, 0 < κ ∧
        ∀ (β : TI K n) (r : ℕ) (w : Fin r → Pl K), Function.Injective w →
        ∀ [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))] (m : ∀ i, Measure (Gw n (w i))),
          (∀ i, (m i).IsHaarMeasure ∧ m i (J (w i)) = 1) → ∀ (ψ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ),
          (∀ i, Test (ψ i) ∧ IsOloc μ (w i) (m i) (ψ i) (T i)) →
          ∀ e : TF K n, (∀ x, e x = (∏ i, ψ i (finAt (w i) (finEmb K n x))) *
            ∏ᶠ u ∉ Set.range w, (J u : Set (Gw n u)).indicator (fun g => conj (χ u g)) (finAt u (finEmb K n x))) →
          RR μ (tens β e) = (κ : ℂ) • (Oinf μ ν β ∘L (List.ofFn T).prod ∘L
            prj (⨅ (u : Pl K) (_ : u ∉ Set.range w), eigL μ u (J u) (χ u))) := by
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
      exact oloc_scale μ (w i) (mm i) (mO (w i)) (hmm i).2 (ψ i) (T i) (hT i).2
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
  have hlist := list_prj μ hco (List.ofFn b) (List.nodup_ofFn.2 hbinj) {v | v ∉ W} (fun v hv h => h (by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hv
    exact Finset.mem_image.2 ⟨Fin.natAdd _ j, Finset.mem_univ _, hw'r j⟩))
  have hU : {v | v ∉ W} ∪ {v | v ∈ List.ofFn b} = {v | v ∉ Set.range w} := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hv | hv)
      · exact (hrange v (hWm v hv)).1
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hv
        exact hbw j
    · intro hv
      by_cases hvW : v ∈ W
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hvW
        refine Fin.addCases (fun i => ?_) (fun j => ?_) i hv
        · intro h
          rw [hw'l] at h
          exact absurd ⟨i, rfl⟩ h
        · intro _
          rw [hw'r]
          exact Or.inr ((List.mem_ofFn' _ _).2 ⟨j, rfl⟩)
      · exact Or.inl hvW
  have hGU : GA μ J χ {v | v ∉ Set.range w} = ⨅ (u : Pl K) (_ : u ∉ Set.range w), eigL μ u (J u) (χ u) := by
    simp only [UpperTheory.ConvolutionTheory.L1.GA, Set.mem_setOf_eq]
  have hXlist : (List.ofFn fun i => X (w' i)).prod =
      (List.ofFn T).prod * (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod := by
    have : (fun i => X (w' i)) = Fin.append T (fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [hw'l, Fin.append_left, hXw]
      · rw [hw'r, Fin.append_right, hXd _ (hbw j)]
    rw [this, List.ofFn_fin_append, List.prod_append]
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
      prj (GA μ J χ {v | v ∉ W}) =
      (List.ofFn T).prod ∘L prj (⨅ (u : Pl K) (_ : u ∉ Set.range w), eigL μ u (J u) (χ u)) := by
    have h2 : ((List.ofFn b).map fun v => prj (eigL μ v (J v) (χ v))).prod =
        (List.ofFn fun j => prj (eigL μ (b j) (J (b j)) (χ (b j)))).prod := by
      rw [List.map_ofFn]
      rfl
    rw [h2, hU, hGU] at hlist
    rw [← hlist]
    rfl
  rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC β e', h1, hmain, hXlist, hprodc, hQ,
    ContinuousLinearMap.smul_comp, key, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, smul_smul]
  push_cast
  rfl
