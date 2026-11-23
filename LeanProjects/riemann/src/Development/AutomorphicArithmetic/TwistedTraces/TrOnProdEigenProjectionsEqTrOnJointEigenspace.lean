import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma prj_mem' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) : prj M x ∈ M := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  have h2 : prj M x ∈ M.topologicalClosure := Submodule.starProjection_apply_mem M.topologicalClosure x
  rwa [h] at h2

private lemma prj_orth' (M : Submodule ℂ H) (x : H) {y : H} (hy : y ∈ M) :
    ⟪x - prj M x, y⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal' _ _).1
    (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) y
    (M.le_topologicalClosure hy)

private lemma prj_eq' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {u v : H} (hv : v ∈ M)
    (ho : ∀ y ∈ M, ⟪u - v, y⟫_ℂ = 0) : prj M u = v := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure)
    (M.le_topologicalClosure hv) fun y hy => ho y (by rwa [h] at hy)

private lemma prj_self' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {v : H} (hv : v ∈ M) :
    prj M v = v :=
  prj_eq' hM hv fun y _ => by simp

private lemma comm_of_stable {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (B B' : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) (h1 : ∀ v ∈ M, B v ∈ M) (h2 : ∀ v ∈ M, B' v ∈ M) :
    Commute B (prj M) := by
  refine ContinuousLinearMap.ext fun x => ?_
  show B (prj M x) = prj M (B x)
  refine (prj_eq' hM (h1 _ (prj_mem' hM x)) fun y hy => ?_).symm
  rw [← map_sub, hadj]
  exact prj_orth' M x (h2 y hy)

private lemma hs_prj (W : Submodule ℂ H) [FiniteDimensional ℂ W] : IsHilbertSchmidt (prj W) := by
  have hcl := Submodule.closed_of_finiteDimensional W
  let e := stdOrthonormalBasis ℂ W
  have he : Orthonormal ℂ (fun k => ((e k : W) : H)) :=
    e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  obtain ⟨s, b, hvs, hb⟩ := (he.toSubtypeRange).exists_hilbertBasis_extension
  have hbi : ∀ i, b i = (i : H) := fun i => congrFun hb i
  let f : Fin _ → s := fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩
  have hf : Function.Injective f := fun k l h => by
    have : ((e k : W) : H) = (e l : W) := congrArg (fun z : s => (z : H)) h
    exact he.linearIndependent.injective this
  have hbf : ∀ k, b (f k) = (e k : H) := fun k => hbi _
  have hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0 := fun i hi => by
    refine prj_eq' hcl W.zero_mem fun y hy => ?_
    have hy' : (y : H) = ∑ k, ⟪(e k : H), y⟫_ℂ • (e k : H) := by
      have h2 := congrArg Subtype.val (e.sum_repr' (⟨y, hy⟩ : W))
      simpa [Submodule.coe_sum] using h2.symm
    rw [sub_zero, hy', inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, ← hbf k]
    have : ⟪b i, b (f k)⟫_ℂ = 0 := b.orthonormal.2 fun h => hi ⟨k, h.symm⟩
    rw [this, mul_zero]
  rw [isHilbertSchmidt_iff b]
  have hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f := fun i hi => by
    by_contra h
    exact hi (by simp [hout i h])
  rw [← hf.tsum_eq hs, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top enorm_lt_top

private lemma pr_props (Z : Submodule ℂ H) : ∀ (r : ℕ) (E : Fin r → Submodule ℂ H),
    (∀ i, IsClosed (E i : Set H)) → (∀ i j, Commute (prj (E i)) (prj (E j))) →
    (∀ i, ∀ v ∈ Z, prj (E i) v ∈ Z) →
    (∀ u ∈ Z, (List.ofFn fun i => prj (E i)).prod u ∈ Z) ∧
    (∀ u, (List.ofFn fun i => prj (E i)).prod u ∈ ⨅ i, E i) ∧
    ∀ u, ∀ y ∈ ⨅ i, E i, ⟪u - (List.ofFn fun i => prj (E i)).prod u, y⟫_ℂ = 0 := by
  intro r
  induction r with
  | zero =>
    intro E _ _ _
    simp
  | succ r ih =>
    intro E hE hc hs
    obtain ⟨i1, i2, i3⟩ := ih (fun i => E i.succ) (fun i => hE _) (fun i j => hc _ _) (fun i => hs _)
    have hP : ∀ u, (List.ofFn fun i => prj (E i)).prod u =
        prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) := fun u => by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    refine ⟨fun u hu => ?_, fun u => ?_, fun u y hy => ?_⟩
    · rw [hP]
      exact hs 0 _ (i1 u hu)
    · rw [hP, Submodule.mem_iInf]
      refine Fin.cases (prj_mem' (hE 0) _) fun j => ?_
      have hx := Submodule.mem_iInf _ |>.1 (i2 u) j
      have h1 : prj (E j.succ) (prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) =
          prj (E 0) (prj (E j.succ) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) :=
        congrArg (fun T : H →L[ℂ] H => T ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) (hc j.succ 0).eq
      rw [prj_self' (hE _) hx] at h1
      rw [← h1]
      exact prj_mem' (hE _) _
    · rw [hP]
      have hy0 : y ∈ E 0 := (Submodule.mem_iInf _).1 hy 0
      have hys : y ∈ ⨅ i : Fin r, E i.succ := (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).1 hy j.succ
      have e : u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) =
          (u - (List.ofFn fun i : Fin r => prj (E i.succ)).prod u) +
          ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u -
            prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) := by abel
      rw [e, inner_add_left, i3 u y hys, prj_orth' _ _ hy0, add_zero]

private lemma tr_main {Z X Y : Submodule ℂ H} (Pr R : H →L[ℂ] H) [FiniteDimensional ℂ X] (hYX : Y ≤ X)
    (hXZ : X ≤ Z) (hR : ∀ v ∈ Z, R v ∈ Z) (h1 : ∀ u ∈ Z, Pr u ∈ Y)
    (h2 : ∀ u, ∀ y ∈ Y, ⟪u - Pr u, y⟫_ℂ = 0) : trOn X (Pr ∘L R) = trOn Y R := by
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYX
  have hXc := Submodule.closed_of_finiteDimensional X
  have hYc := Submodule.closed_of_finiteDimensional Y
  have e1 : prj X ∘L (Pr ∘L R) ∘L prj X = prj Y ∘L (R ∘L prj X) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hx : R (prj X v) ∈ Z := hR _ (hXZ (prj_mem' hXc v))
    show prj X (Pr (R (prj X v))) = prj Y (R (prj X v))
    rw [prj_self' hXc (hYX (h1 _ hx)), prj_eq' hYc (h1 _ hx) (h2 _)]
  have e2 : (R ∘L prj X) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj X (prj Y v)) = R (prj Y v)
    rw [prj_self' hXc (hYX (prj_mem' hYc v))]
  have e3 : (R ∘L prj Y) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj Y (prj Y v)) = R (prj Y v)
    rw [prj_self' hYc (prj_mem' hYc v)]
  have e4 : prj Y ∘L prj Y = prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self' hYc (prj_mem' hYc v)
  have hT : IsTraceClass (prj Y) := by
    have := isTraceClass_comp (hs_prj Y) (hs_prj Y)
    rwa [show (prj Y).comp (prj Y) = prj Y from e4] at this
  unfold trOn
  rw [e1]
  have a := trace_comp_comm hT (R ∘L prj X)
  have b := trace_comp_comm hT (R ∘L prj Y)
  calc trace (prj Y ∘L R ∘L prj X) = trace ((R ∘L prj X) ∘L prj Y) := a.symm
    _ = trace ((R ∘L prj Y) ∘L prj Y) := by rw [e2, e3]
    _ = trace (prj Y ∘L R ∘L prj Y) := b

end Hilbert

theorem UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (Z : Submodule ℂ (LL μ))
        (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (χ : ∀ i, Gw n (w i) → ℂ)
        (hc : ∀ i, IsChr (J i) (χ i)) (R : LL μ →L[ℂ] LL μ), (∀ i, CO (J i)) → IsClosed (Z : Set (LL μ)) →
        (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) → (∀ v ∈ Z, R v ∈ Z) →
        FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) →
        trOn (Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) ((List.ofFn fun i => prj (eigL μ (w i) (J i) (χ i))).prod ∘L R) =
          trOn (Z ⊓ ⨅ i, eigL μ (w i) (J i) (χ i)) R := by
  intro K _ _ n μ _ Z r w hw J χ hc R hCO hZ hst hR hfd
  have hB := fun i => UpperTheory.ConvolutionTheory.L1.eigBasic K n μ (w i) (J i) (χ i) (hCO i) (hc i)
  have hF := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := hF.2.2.2.2.2.1
  have hadjF : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := hF.2.2.2.2.2.2.2.1
  have hadj : ∀ (u : Pl K) g x y, ⟪rhoL μ u g x, y⟫_ℂ = ⟪x, rhoL μ u g⁻¹ y⟫_ℂ := fun u g x y => by
    have : rhoL μ u g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ u g) := by
      unfold rhoL
      rw [hadjF, map_inv]
    rw [this, ContinuousLinearMap.adjoint_inner_right]
  have hcomZ : ∀ i, Commute (prj Z) (prj (eigL μ (w i) (J i) (χ i))) := fun i =>
    (hB i).2.2.2 (prj Z) fun x _ =>
      (comm_of_stable hZ (rhoL μ (w i) x) (rhoL μ (w i) x⁻¹) (hadj _ x) (hst i x) (hst i x⁻¹)).symm
  have hs : ∀ i, ∀ v ∈ Z, prj (eigL μ (w i) (J i) (χ i)) v ∈ Z := fun i v hv => by
    have h1 : prj Z (prj (eigL μ (w i) (J i) (χ i)) v) = prj (eigL μ (w i) (J i) (χ i)) (prj Z v) :=
      congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hcomZ i).eq
    rw [prj_self' hZ hv] at h1
    rw [← h1]
    exact prj_mem' hZ _
  have hrho : ∀ i j, i ≠ j → ∀ x y, Commute (rhoL μ (w j) x) (rhoL μ (w i) y) := fun i j hij x y => by
    have hne : w i ≠ w j := fun h => hij (hw h)
    have := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w j)).2.2.2.1 (w i) hne x y
    show rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
    rw [← hmul, ← hmul, this]
  have hcom : ∀ i j, Commute (prj (eigL μ (w i) (J i) (χ i))) (prj (eigL μ (w j) (J j) (χ j))) := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hB j).2.2.2 _ fun x _ => ((hB i).2.2.2 _ fun y _ => hrho i j hij x y).symm
  obtain ⟨p1, p2, p3⟩ := pr_props Z r (fun i => eigL μ (w i) (J i) (χ i)) (fun i => (hB i).1) hcom hs
  have hle : ∀ i, eigL μ (w i) (J i) (χ i) ≤ fixL μ (w i) (kerChr (J i) (χ i) (hc i)) := fun i v hv => by
    refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : rhoL μ (w i) x v = χ i x • v := by
      simpa [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] using
        (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv x) hx.1
    have h2 : χ i x = 1 := hx.2
    rw [h2, one_smul] at h1
    exact h1
  refine tr_main (Z := Z) _ R (inf_le_inf_left Z (iInf_mono hle)) inf_le_left hR
    (fun u hu => Submodule.mem_inf.2 ⟨p1 u hu, p2 u⟩) fun u y hy => p3 u y (Submodule.mem_inf.1 hy).2
