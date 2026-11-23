import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocGalEx
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistY
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundDimSimultaneousLocalEigenspaceOfOpenC
import Development.AutomorphicArithmetic.TwistedTraces.ExistsPosConstEigenspaceBoundOfSplitCMDatum
import Development.AutomorphicArithmetic.TwistedTraces.EigenspaceFactorizationOverNonsplitPlacesCMDatum
import Development.AutomorphicArithmetic.TwistedTraces.TraceEigenspaceOfSelfAdjointInvariantSubspaces
import Development.AutomorphicArithmetic.TwistedTraces.HeckeOperatorSummandWeightCMDatum
import Development.AutomorphicArithmetic.TwistedTraces.ProdLocalOperatorsMemFixedAndOffNCMDatum
import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalEigenspaceInfFixedOffNCMDatum
import Development.AutomorphicArithmetic.TwistedTraces.GaloisTwistCommuteArchOperatorAndOffProjection
import Development.AutomorphicArithmetic.TwistedTraces.ExistsUniqueEigenlineOfRankOneOccurs
import Development.AutomorphicArithmetic.TwistedTraces.IntegralOpEigenlineScalarOfTwist
import Development.AutomorphicArithmetic.TwistedTraces.TrOnProdEigenProjectionsEqTrOnJointEigenspace
import Development.AutomorphicArithmetic.TwistedTraces.ArchimedeanBaseChangeTraceComparison

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.TraceVanishing

private theorem hasFinTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ) (hb : b ≠ 0)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

private theorem hasTw_smul {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G} {τ : SmIrr G}
    {I : τ.V ≃ₗ[ℂ] τ.V} {φ : G → ℂ} {t : ℂ} (d : ENNReal) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : HasTwTrace m τ I φ t) : HasTwTrace (d • m) τ I φ ((d.toReal : ℂ) * t) := by
  obtain ⟨B, hB, hF⟩ := h
  have hb : (d.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)
  refine ⟨(d.toReal : ℂ) • B, isInt_smul d hdt hB, ?_⟩
  have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
  rw [e]
  exact hasFinTrace_smul _ _ hb hF

private theorem exists_enum {α : Type} (A : Finset α) :
    ∃ (r : ℕ) (p : Fin r → α), Function.Injective p ∧ ∀ v, v ∈ A ↔ v ∈ Set.range p := by
  refine ⟨A.card, fun i => (A.equivFin.symm i).1, Subtype.val_injective.comp A.equivFin.symm.injective,
    fun v => ⟨fun hv => ⟨A.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (A.equivFin.symm i).2

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

private theorem ker_co {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) :
    CO (kerChr J χ h) := by
  have e : (kerChr J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

private theorem ker_inv {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ)
    (u : G) (hu : u ∈ kerChr J χ h) (g : G) :
    (J : Set G).indicator (fun x => conj (χ x)) (u * g) = (J : Set G).indicator (fun x => conj (χ x)) g := by
  obtain ⟨h1, h2⟩ : u ∈ J ∧ χ u = 1 := hu
  by_cases hg : g ∈ J
  · rw [Set.indicator_of_mem (by exact J.mul_mem h1 hg), Set.indicator_of_mem (by exact hg), h.2.2 u h1 g hg, h2, one_mul]
  · have : u * g ∉ J := fun hh => hg ((Subgroup.mul_mem_cancel_left J h1).1 hh)
    rw [Set.indicator_of_notMem (by exact this), Set.indicator_of_notMem (by exact hg)]

section Hil
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem' {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem V.topologicalClosure v
  rwa [hc] at h

private theorem prj_self' {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem mem_eigIn' {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem trOn_congr {Y : Submodule ℂ H} (hY : IsClosed (Y : Set H)) {A B : H →L[ℂ] H} (h : ∀ v ∈ Y, A v = B v) :
    trOn Y A = trOn Y B := by
  unfold trOn
  congr 1
  ext1 v
  simp only [ContinuousLinearMap.comp_apply]
  rw [h _ (prj_mem' hY v)]

end Hil

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem mem_eigL' {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL' {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem isClosed_fixL (w : Pl K) (J : Subgroup (Gw n w)) : IsClosed (fixL μ w J : Set (LL μ)) := by
  simp only [fixL, fixF, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id

private theorem eigL_comm {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} (O : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute O (rhoL μ w g)) {v : LL μ} (hv : v ∈ eigL μ w J χ) : O v ∈ eigL μ w J χ := by
  rw [mem_eigL'] at hv ⊢
  intro x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (h x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv x hx, map_smul]

private theorem fixL_comm {w : Pl K} {J : Subgroup (Gw n w)} (O : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute O (rhoL μ w g)) {v : LL μ} (hv : v ∈ fixL μ w J) : O v ∈ fixL μ w J := by
  rw [mem_fixL'] at hv ⊢
  intro x hx
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (h x).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [← this, hv x hx]

private theorem oinf_comm (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (C : LL μ →L[ℂ] LL μ)
    (h : ∀ g, Commute C (rightRegularRep (rationalGLOne K n) μ (archP K n g))) : Commute C (Oinf μ ν a) := by
  have key : C ∘L Oinf μ ν a = Oinf μ ν a ∘L C := by
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro x u
    exact DFunLike.congr_fun (h x).eq u
  exact key

private theorem oinf_congr {ν₁ ν₂ : Measure (archGroup K n)} [ν₁.IsHaarMeasure] [ν₂.IsHaarMeasure] (h : ν₁ = ν₂) (β : TI K n) :
    Oinf μ ν₁ β = Oinf μ ν₂ β := by
  subst h; rfl

end Ops

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over' {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_surj {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) :
    Function.Surjective (GM.cmp (n := n) w) := by
  have hev : Function.Bijective (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) := by
    letI : Unique (PlacesOver E v) := ⟨⟨w⟩, h⟩
    constructor
    · intro a b e
      funext u
      obtain rfl := h u
      exact e
    · intro z
      refine ⟨fun u => (h u).symm ▸ z, ?_⟩
      show ((h w).symm ▸ z : (w.1.adicCompletion E)) = z
      rfl
  let e := RingEquiv.ofBijective _ hev
  intro y
  refine ⟨mapGL n (e.symm : _ →+* _) y, ?_⟩
  exact Units.ext (Matrix.ext fun a b => e.apply_symm_apply _)

variable {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem gal_eq {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) {a b : Gw n w.1 →* Gw n w.1}
    (ha : IsLocGal σ w a) (hb : IsLocGal σ w b) (x : Gw n w.1) : a x = b x := by
  obtain ⟨g, rfl⟩ := cmp_surj w h x
  rw [← ha, ← hb]

private theorem stabV (T : Ty σ n q w₀) (v : Pl F) (h : ∀ u : PlacesOver E v, u = T.mk' v)
    {a : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1} (ha : IsLocGal σ (T.mk' v) a) (x : Gw n (T.mk' v).1) (hx : x ∈ T.J (T.mk' v).1) :
    a x ∈ T.J (T.mk' v).1 ∧ T.χ (T.mk' v).1 (a x) = T.χ (T.mk' v).1 x := by
  obtain ⟨g, rfl⟩ := cmp_surj (T.mk' v) h x
  letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, h⟩
  have hall : ∀ u : PlacesOver E v, GM.cmp u g ∈ T.J u.1 := fun u => by
    obtain rfl := h u
    exact hx
  obtain ⟨h1, h2⟩ := T.stable v g hall
  rw [finprod_unique, finprod_unique] at h2
  have e : (default : PlacesOver E v) = T.mk' v := rfl
  rw [e] at h2
  rw [← ha]
  exact ⟨h1 _, h2⟩

end Loc

end UpperTheory.ConvolutionTheory.C.TraceVanishing

open UpperTheory.ConvolutionTheory.C.TraceVanishing in
set_option maxHeartbeats 3200000 in
theorem UpperTheory.ConvolutionTheory.C.termEV :
    UpperTheory.ConvolutionTheory.C.TermEV := by
  classical
  intro F E _ _ _ _ _ _ σ hgen k n hk hpr hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ
    hrk τ₀ τ g I hocc₀ hocc hI y hy
  have hprime : (Module.finrank F E).Prime := hk ▸ hpr
  have hx : (0 : ℝ) < y ^ (k + 1) := pow_pos hy _
  have hns : ∀ v ∈ nsS T, v ∈ T.S ∧ ¬ GM.Split E v := fun v hv => Finset.mem_filter.1 hv
  have hU : ∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v := fun v hv =>
    (UpperTheory.ConvolutionTheory.C.locGalEx F E σ hprime n v (T.mk' v) (hns v hv).2).1
  obtain ⟨r₁, p₁, hp₁, hpr₁⟩ := exists_enum T.sp
  obtain ⟨r₂, p₂, hp₂, hpr₂⟩ := exists_enum (nsS T)
  have hm₁ : ∀ i, p₁ i ∈ T.sp := fun i => (hpr₁ _).2 ⟨i, rfl⟩
  have hm₂ : ∀ i, p₂ i ∈ nsS T := fun i => (hpr₂ _).2 ⟨i, rfl⟩

  have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
    haveI := hm u
    exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
    haveI := hm u
    exact (T.co u).1.measure_lt_top.ne
  have hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0 := fun u => ENNReal.inv_ne_zero.2 (ht u)
  have hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤ := fun u => ENNReal.inv_ne_top.2 (h0 u)
  let mm : ∀ u : Pl E, Measure (Gw n u) := fun u => (m u (T.J u))⁻¹ • m u
  let bb : Pl E → ℂ := fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ)
  have hmmH : ∀ u, (mm u).IsHaarMeasure := fun u => by
    haveI := hm u
    exact Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)
  have hmm1 : ∀ u, mm u (T.J u) = 1 := fun u => by
    show ((m u (T.J u))⁻¹ • m u) (T.J u) = 1
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht u)]
  have hbb : ∀ u, bb u ≠ 0 := fun u => Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)
  set x : ℝ := y ^ (k + 1) with hxd
  set Oa := Oinf μ νE aE with hOa
  set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO

  obtain ⟨κ, hκ, hK⟩ := UpperTheory.exists_pos_const_eigenspace_bound_of_split_CMDatum F E σ n hn μ νE aE q w₀ hq T hU
  obtain ⟨c₀, hc₀, hTY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ
    (fun v hv hs' u => (hrk v hv hs' u).1)).2 y hy
  obtain ⟨c₁, hc₁, hval⟩ := UpperTheory.archimedean_baseChange_trace_comparison F E σ k n hn μ D s hs hposition νF a m hm q w₀ hq T V hV τ₀ τ hocc₀
    (fun v hv => hocc v (Finset.mem_filter.1 hv).1) y hy mm (fun _ => rfl) r₁ p₁ hp₁ hpr₁
  obtain ⟨hθO, hθP⟩ := UpperTheory.galoisTwist_commute_archOperator_and_offProjection F E σ hgen k n μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ T
  let w : Fin r₂ → Pl E := fun i => (T.mk' (p₂ i)).1
  have hwinj : Function.Injective w := fun i j h => hp₂ (by
    have e : (T.mk' (p₂ i)).1 = (T.mk' (p₂ j)).1 := h
    rw [← under_over' (T.mk' (p₂ i)), e, under_over'])
  have hwm : ∀ i, w i ∉ T.marked := by
    rintro i (h | ⟨v, hv, h⟩)
    · have h1 : p₂ i = q := by
        rw [← under_over' (T.mk' (p₂ i)), show (T.mk' (p₂ i)).1 = w₀.1 from h, under_over']
      exact T.q_not (h1 ▸ (hns _ (hm₂ i)).1)
    · have h1 : p₂ i = v := by
        rw [← under_over' (T.mk' (p₂ i)), show (T.mk' (p₂ i)).1 = (T.mk' v).1 from h, under_over']
      exact (hns _ (hm₂ i)).2 (h1 ▸ (Finset.mem_filter.1 hv).2)
  obtain ⟨hZc, hZs, hZa⟩ := UpperTheory.finiteDimensional_eigenspace_inf_fixed_offN_CMDatum F E σ n hn μ νE aE q w₀ T V hV hU x hx.ne'
  set Z := eigIn (V ⊓ offN μ T) (Oinf μ νE aE) x with hZd
  have hZV : Z ≤ V := fun f hf => (mem_eigIn'.1 hf).1.1
  have hZo : Z ≤ offN μ T := fun f hf => (mem_eigIn'.1 hf).1.2
  have hoffc : IsClosed (offN μ T : Set (LL μ)) := by
    simp only [offN, Submodule.coe_iInf]
    exact isClosed_iInter fun w => isClosed_iInter fun _ => (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w _ _ (T.co w) (T.chr w)).1
  have hθV : ∀ f ∈ V, θ.U f ∈ V := fun f hf => by
    rw [← hVθ]
    exact Submodule.mem_map_of_mem hf
  have hθZ : ∀ f ∈ Z, θ.U f ∈ Z := fun f hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_eigIn'.1 hf
    refine mem_eigIn'.2 ⟨⟨hθV f h1, ?_⟩, ?_⟩
    · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S f) hθP.eq
      simp only [ContinuousLinearMap.mul_apply, prj_self' h2] at this
      rw [this]
      exact prj_mem' hoffc _
    · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S f) hθO.eq
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this, h3, map_smul]
  choose s' hs1 hs2 using fun i => (UpperTheory.ConvolutionTheory.C.locGalEx F E σ hprime n (p₂ i) (T.mk' (p₂ i)) (hns _ (hm₂ i)).2).2
  have hθs : ∀ i g f, θ.U (rhoL μ (w i) g f) = rhoL μ (w i) (s' i g) (θ.U f) := fun i => ((hs2 i) μ θ hθ).1
  have hIs : ∀ i x y, I (p₂ i) ((τ (p₂ i)).ρ x y) = (τ (p₂ i)).ρ (s' i x) (I (p₂ i) y) := fun i x y => by
    have hv := hns _ (hm₂ i)
    have h := hI _ hv.1 hv.2
    have e := gal_eq (T.mk' (p₂ i)) (hU _ (hm₂ i)) h.1 (hs1 i) x
    have e' : (s' i : Gw n (T.mk' (p₂ i)).1 →* Gw n (T.mk' (p₂ i)).1) x = s' i x := rfl
    rw [h.2 x y, e, e']
  have ht0 : ∀ i, ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace (mm (w i)) (τ (p₂ i)) (I (p₂ i))
      ((T.J (w i) : Set (Gw n (w i))).indicator fun x => conj (T.χ (w i) x)) t := by
    intro i
    have hv := hns _ (hm₂ i)
    obtain ⟨h1, h2⟩ := hrk _ hv.1 hv.2 (T.mk' (p₂ i))
    haveI := hmmH (w i)
    obtain ⟨e, he0, he1, he2⟩ := UpperTheory.exists_unique_eigenline_of_rankOne_occurs E n μ V hV (w i) (τ (p₂ i)) (hocc _ hv.1) (T.J (w i)) (T.χ (w i))
      (T.co _) (T.chr _) h1 h2
    obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V (w i) (mm (w i)) hV
    obtain ⟨_, A, hA, -⟩ := h3 (τ (p₂ i)) (hocc _ hv.1) _ (test_ind (T.co (w i)) (T.chr (w i)))
    exact UpperTheory.integralOp_eigenline_scalar_of_twist (Gw n (w i)) (mm (w i)) (τ (p₂ i)) (I (p₂ i)) (g (p₂ i)) (T.J (w i)) (T.χ (w i)) A e (T.co _) (T.chr _)
      (hmm1 _) hA he0 he1 he2 (stabV T _ (hU _ (hm₂ i)) (hI _ hv.1 hv.2).1) (hI _ hv.1 hv.2).2
  choose t0 ht0n ht0t using ht0
  have hP0 : ∏ i, t0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0n i
  have hZ0 : Z ⊓ ⨅ i, eigL μ (w i) (T.J (w i)) (T.χ (w i)) = eigIn (V ⊓ T.typed μ) (Oinf μ νE aE) x := by
    ext f
    simp only [Submodule.mem_inf, Submodule.mem_iInf, hZd, mem_eigIn', offN, Ty.typed]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨h1, fun u => ?_⟩, h3⟩
      by_cases hu : u.under (𝓞 F) ∈ (nsS T : Set (Pl F))
      · obtain ⟨i, hi⟩ := (hpr₂ _).1 hu
        have e : (⟨u, ⟨rfl⟩⟩ : PlacesOver E (u.under (𝓞 F))) = T.mk' (u.under (𝓞 F)) := hU _ hu _
        have e2 : u = w i := by
          show u = (T.mk' (p₂ i)).1
          rw [hi]
          exact congrArg Subtype.val e
        rw [e2]
        exact h4 i
      · exact h2 u hu
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, fun u _ => h2 u⟩, h3⟩, fun i => h2 _⟩
  refine ⟨(κ : ℂ) * x * c₀ * c₁ * (∏ i, bb (w i)) * (∏ i, t0 i)⁻¹, fun hz => ?_, ?_⟩
  · have h1 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h2 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) hc₀) (hc₁ hz))
      (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)) (inv_ne_zero hP0)
  intro L ψ hfit e l 𝔢 he hsd j sq t hsq htS htN
  obtain ⟨hν, ha, -, hUl, hg, hUq⟩ := hsd
  have hψ₁ : ∀ v ∈ T.sp, Test (ψ v) ∧ ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g := fun v hv =>
    ⟨hfit.test v (Finset.mem_filter.1 hv).1, fun u hu g => (hfit.inv v hv u hu g).1⟩
  have hB₁ : ∀ i, ∃ B, IsOloc μ (T.mk' (p₁ i)).1 (mm _) (ψ (p₁ i)) B := fun i => by
    haveI := hmmH (T.mk' (p₁ i)).1
    exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ _ (mm _) (ψ (p₁ i)) (hfit.test _ (Finset.mem_filter.1 (hm₁ i)).1)).exists
  have hB₂ : ∀ i, ∃ B, IsOloc μ (T.mk' (p₂ i)).1 (mm _) (ψ (p₂ i)) B := fun i => by
    haveI := hmmH (T.mk' (p₂ i)).1
    exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ _ (mm _) (ψ (p₂ i)) (hfit.test _ (hns _ (hm₂ i)).1)).exists
  choose B₁ hB₁ using hB₁
  choose B₂ hB₂ using hB₂
  have hmmA : ∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1 := fun u => ⟨hmmH u, hmm1 u⟩
  obtain ⟨hCa, hCr, hCo, hCV⟩ := UpperTheory.heckeOperator_summand_weight_CMDatum F E σ n μ q w₀ hq T V hV e j r₁ p₁ hm₁ mm hmmA ψ (fun i => hψ₁ _ (hm₁ i)) B₁ hB₁
  obtain ⟨-, hDr, hDo, -⟩ := UpperTheory.heckeOperator_summand_weight_CMDatum F E σ n μ q w₀ hq T V hV e 0 r₁ p₁ hm₁ mm hmmA ψ (fun i => hψ₁ _ (hm₁ i)) B₁ hB₁
  have hD1 : (Uiw μ w₀.1 e ^ 0) ∘L (List.ofFn B₁).prod = (List.ofFn B₁).prod := by
    ext1 f
    simp
  rw [hD1] at hDr hDo
  set C := (Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B₁).prod with hCd
  have hCO : Commute C (Oinf μ νE aE) := oinf_comm μ νE aE C hCa
  have hRZ : ∀ f ∈ Z, (C ∘L θ.U) f ∈ Z := fun f hf => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := mem_eigIn'.1 (hθZ f hf)
    refine mem_eigIn'.2 ⟨⟨hCV _ h1, hCo _ h2⟩, ?_⟩
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) hCO.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    show Oinf μ νE aE (C (θ.U f)) = (x : ℂ) • C (θ.U f)
    rw [← this, h3, map_smul]
  have hRs : ∀ i g, ∀ f ∈ Z, (C ∘L θ.U) (rhoL μ (w i) g f) = rhoL μ (w i) (s' i g) ((C ∘L θ.U) f) := fun i g f _ => by
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) (hCr _ (hwm i) (s' i g)).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    show C (θ.U (rhoL μ (w i) g f)) = rhoL μ (w i) (s' i g) (C (θ.U f))
    rw [hθs, this]
  obtain ⟨cR, hTF⟩ := UpperTheory.ConvolutionTheory.C.twistFactor E n μ V Z r₂ w (fun i => τ (p₂ i)) s' (fun i => I (p₂ i)) (C ∘L θ.U) hV hwinj
    (fun i => hocc _ (hns _ (hm₂ i)).1) hZV hZc (fun i g f hf => hZs _ (hm₂ i) g f hf)
    (fun U hUc => hZa r₂ p₂ hp₂ hpr₂ U hUc) hRZ hRs hIs
  have hcr : cR * ∏ i, t0 i = c₀ * (c₁ * sq * ∏ v ∈ T.sp, t v) := by
    have e1 := hTF (fun i => kerChr (T.J (w i)) (T.χ (w i)) (T.chr _)) (fun i => mm (w i))
      (fun i => (T.J (w i) : Set (Gw n (w i))).indicator fun x => conj (T.χ (w i) x))
      (fun i => prj (eigL μ (w i) (T.J (w i)) (T.χ (w i)))) t0 (fun i => ker_co (T.co _) (T.chr _)) (fun i => hmmH _)
      (fun i => test_ind (T.co _) (T.chr _)) (fun i => ker_inv (T.chr _))
      (fun i => by
        haveI := hmmH (w i)
        exact (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ (w i) _ _ (T.co _) (T.chr _)).2.2.1 (mm (w i)) (hmm1 _)) ht0t
    have e2 := UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace E n μ Z r₂ w hwinj (fun i => T.J (w i)) (fun i => T.χ (w i)) (fun i => T.chr _) (C ∘L θ.U)
      (fun i => T.co _) hZc (fun i g f hf => hZs _ (hm₂ i) g f hf) hRZ
      (hZa r₂ p₂ hp₂ hpr₂ _ fun i => ker_co (T.co _) (T.chr _))
    have e3 := hTY C hCa hCr
    have e4 := hval ψ hψ₁ e he j sq t hsq htS B₁ hB₁
    rw [← e1, e2, hZ0, e3, e4]

  have hAeq : 𝔢.toAmp.A = Oinf μ νE aE ∘L prj (fixF μ (GM.levE L.UE)) := by
    show Oinf μ 𝔢.ν 𝔢.a₀ ∘L prj (fixF μ 𝔢.U) = _
    rw [ha, hUl, oinf_congr μ hν]
  have hpos : 0 ≤ Oinf μ νE aE := by
    have := 𝔢.pos
    rwa [ha, oinf_congr μ hν] at this
  have hOsa : ContinuousLinearMap.adjoint (Oinf μ νE aE) = Oinf μ νE aE :=
    (IsSelfAdjoint.of_nonneg hpos).adjoint_eq
  have hOF : ∀ h, Commute (Oinf μ νE aE) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg E n μ νE MeasureTheory.Measure.haar).2.2.2.2.2.2.2.2 aE h
  have hcp := UpperTheory.ConvolutionTheory.Tf.commPrj E n μ (GM.levE L.UE)
  have hOFx : ∀ v ∈ fixF μ (GM.levE L.UE), Oinf μ νE aE v ∈ fixF μ (GM.levE L.UE) := by
    intro v hv
    refine (hcp.2.1 _).2 fun u hu => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOF u).eq
    simp only [ContinuousLinearMap.mul_apply, (hcp.2.1 v).1 hv u hu] at this
    exact this.symm
  obtain ⟨hlc, hlψ, hle⟩ := UpperTheory.eigenspace_factorization_over_nonsplit_places_CMDatum F E σ n q w₀ hq μ T L ψ hfit hU r₂ p₂ hpr₂
  obtain ⟨hNf, hNo⟩ := UpperTheory.prod_localOperators_mem_fixed_and_offN_CMDatum F E σ n μ q w₀ T r₂ p₂ hp₂ hm₂ mm hmmH ψ (fun i => lvN T L (p₂ i)) hlψ B₂ hB₂
  set FN : Submodule ℂ (LL μ) := ⨅ i, fixL μ (T.mk' (p₂ i)).1 (lvN T L (p₂ i)) with hFN
  have hFNc : IsClosed (FN : Set (LL μ)) := by
    rw [hFN, Submodule.coe_iInf]
    exact isClosed_iInter fun i => isClosed_fixL μ _ _
  have hTc : IsClosed ((offN μ T ⊓ FN : Submodule ℂ (LL μ)) : Set (LL μ)) := by
    rw [Submodule.coe_inf]
    exact hoffc.inter hFNc
  have hcomm : ∀ O' : LL μ →L[ℂ] LL μ, (∀ u g, Commute O' (rhoL μ u g)) → ∀ f ∈ offN μ T ⊓ FN, O' f ∈ offN μ T ⊓ FN := by
    intro O' hO' f hf
    obtain ⟨a1, a2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · simp only [offN, Submodule.mem_iInf] at a1 ⊢
      exact fun u hu => eigL_comm μ O' (hO' u) (a1 u hu)
    · rw [hFN, Submodule.mem_iInf] at a2 ⊢
      exact fun i => fixL_comm μ O' (hO' _) (a2 i)
  have hmk : ∀ (P : LL μ →L[ℂ] LL μ), (∀ f ∈ offN μ T, P f ∈ offN μ T) → (∀ u ∉ T.marked, ∀ g, Commute P (rhoL μ u g)) →
      ∀ f ∈ offN μ T ⊓ FN, P f ∈ offN μ T ⊓ FN := by
    intro P h1 h2 f hf
    obtain ⟨a1, a2⟩ := Submodule.mem_inf.1 hf
    refine Submodule.mem_inf.2 ⟨h1 f a1, ?_⟩
    rw [hFN, Submodule.mem_iInf] at a2 ⊢
    exact fun i => fixL_comm μ P (h2 _ (hwm i)) (a2 i)
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hS : ∀ f, ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) f ∈ offN μ T ⊓ FN := fun f =>
    hmk _ hDo hDr _ ⟨hNo _ (prj_mem' hoffc f), hNf _⟩
  have hUS : ∀ f, (𝔢.Uq 0 ^ j) (((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) f) ∈ offN μ T ⊓ FN := fun f => by
    rw [hUq]
    exact hmk C hCo hCr _ ⟨hNo _ (prj_mem' hoffc f), hNf _⟩
  have hY : eigIn (V ⊓ (offN μ T ⊓ FN)) (Oinf μ νE aE) x = Z ⊓ FN := by
    ext f
    simp only [Submodule.mem_inf, hZd, mem_eigIn']
    tauto
  haveI hfd : FiniteDimensional ℂ ↥(eigIn (V ⊓ (offN μ T ⊓ FN)) (Oinf μ νE aE) x) := by
    rw [hY]
    exact hZa r₂ p₂ hp₂ hpr₂ _ hlc
  have hred := UpperTheory.trace_eigenspace_of_selfAdjoint_invariant_subspaces (LL μ) (offN μ T ⊓ FN) (fixF μ (GM.levE L.UE)) V hTc hcp.1 hVc hle (Oinf μ νE aE) hOsa
    (hcomm _ fun u g => hOF _) hOFx
    (hcomm _ fun u g => ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm) x (κ : ℂ)
    (𝔢.Uq 0 ^ j) ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) θ.U hfd
    (by
      have := (𝔢.Uq_amp 0).pow_left j
      rwa [hAeq] at this) hS hUS
  have hRop := hK L ψ hfit r₁ p₁ hp₁ hpr₁ r₂ p₂ hp₂ hpr₂ mm hmmA B₁ B₂ hB₁ hB₂ 𝔢.g hg
  have hCB : Commute C (List.ofFn B₂).prod := Commute.list_prod_right _ _ fun Bx hBx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hBx
    exact oloc_comm μ (hB₂ i) C (fun g => hCr _ (hwm i) g)
  have hZFc : IsClosed ((Z ⊓ FN : Submodule ℂ (LL μ)) : Set (LL μ)) := by
    rw [Submodule.coe_inf]
    exact hZc.inter hFNc
  have hsw : trOn (Z ⊓ FN) ((𝔢.Uq 0 ^ j) ∘L ((List.ofFn B₁).prod ∘L (List.ofFn B₂).prod ∘L prj (offN μ T)) ∘L θ.U) =
      trOn (Z ⊓ FN) ((List.ofFn B₂).prod ∘L (C ∘L θ.U)) := by
    refine trOn_congr hZFc fun f hf => ?_
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S (θ.U f)) hCB.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [prj_self' (hZo (hθZ f hf.1)), hUq]
    exact this
  have hTw : ∀ i, HasTwTrace (mm (w i)) (τ (p₂ i)) (I (p₂ i)) (ψ (p₂ i)) (bb (w i) * t (p₂ i)) := fun i =>
    hasTw_smul _ (hd0 _) (hdt _) (htN _ (hns _ (hm₂ i)).1 (hns _ (hm₂ i)).2)
  have hfac := hTF (fun i => lvN T L (p₂ i)) (fun i => mm (w i)) (fun i => ψ (p₂ i)) B₂ (fun i => bb (w i) * t (p₂ i)) hlc
    (fun i => hmmH _) (fun i => hfit.test _ (hns _ (hm₂ i)).1) hlψ hB₂ hTw
  have hprod : ∏ v ∈ T.S, t v = (∏ v ∈ T.sp, t v) * ∏ i, t (p₂ i) := by
    have e2 : nsS T = Finset.univ.image p₂ := by
      ext v
      simp [hpr₂]
    have e3 : ∏ v ∈ nsS T, t v = ∏ i, t (p₂ i) := by
      rw [e2, Finset.prod_image (fun _ _ _ _ h => hp₂ h)]
    rw [← e3]
    exact (Finset.prod_filter_mul_prod_filter_not T.S _ t).symm
  have hcR : cR = c₀ * (c₁ * sq * ∏ v ∈ T.sp, t v) * (∏ i, t0 i)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hP0).2 hcr
  rw [hAeq, hRop, hred, hY, hsw, hfac, hprod, hcR, Finset.prod_mul_distrib]
  ring
