import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedHolomorphicFormEqMultiplicitySpaceValue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd

noncomputable section

namespace GlobalTheory.TensRep

section General

open MeasureTheory GlobalTheory.LocRep GlobalTheory.SmoothRep
open scoped ContDiff Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : K → G → ℂ}
  {ρ : G →* (K →L[ℂ] K)}

theorem exists_rep_bound [μ.IsMulRightInvariant]
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    {H U : Subgroup G} (hU : IsOpen (U : Set G)) (hH : ∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H)
    {P : Type} {A : Set P} {e : P → ℝ → G}
    (he : ∀ p ∈ A, Continuous (e p) ∧ e p 0 = 1 ∧ ∀ a b, e p (a + b) = e p a * e p b)
    (hcomm : ∀ p t, ∀ k ∈ H, e p t * k = k * e p t)
    {N : ℕ} {qs : Fin N → P} (hq : ∀ i, qs i ∈ A) {s : ℝ} (hs : 0 < s)
    (hΘ : Continuous fun t : Fin N → ℝ => (List.ofFn fun i => e (qs i) (t i)).prod) {Ω : Set G}
    (hΩ : IsCompact Ω) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ f : G → ℝ, Continuous f → (∀ g, 0 ≤ f g) → (∀ k ∈ H, ∀ g, f (g * k) = f g) →
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), f (List.ofFn fun i => e (qs i) (t i)).prod ≤
        C * ∫ x in Ω, f x ∂μ) :
    ∃ (R : K → G → ℂ) (L : List (List P)), (∀ l ∈ L, ∀ p ∈ l, p ∈ A) ∧
      (∀ v, Sm ρ A e v → (∀ k ∈ H, ρ k v = v) → Continuous (R v) ∧ ι v =ᵐ[μ] R v) ∧
      ∀ x, ∃ c : ℝ, ∀ v,
        ‖R v x‖ ≤ c * (L.map fun l => ‖l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) v‖).sum := by
  obtain ⟨J, _, κ, l, hκ, hT⟩ := GlobalTheory.T.eq_sum_integral_cube_derivatives_alt G K ρ hiso hρ s hs N (fun i => e (qs i)) fun i => he _ (hq i)
  choose Λ hΛ using fun j => exists_eval hloc hlin hiso hρ htr hU hH hΘ
    (isCompact_univ_pi fun _ => isCompact_Icc) hΩ hC hM (hκ j)
  let d : P → K → K := fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0
  let S : Set K := {v | Sm ρ A e v ∧ ∀ k ∈ H, ρ k v = v}
  have hS : ∀ v ∈ S, ∀ p ∈ A, d p v ∈ S := fun v hv p hp => by
    refine ⟨(GlobalTheory.T.smooth_along_curve_products_stable_alt G K ρ P A e v hv.1).1 p hp, fun k hk => ?_⟩
    have h1 := hv.1.hasDerivAt hp
    have h2 := ((ρ k).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
    refine HasDerivAt.unique (f := fun r : ℝ => ρ (e p r) v) (x := 0) ?_ h1
    convert h2 using 1
    · funext r
      show _ = (ρ k * ρ (e p r)) v
      rw [← map_mul, ← hcomm p r k hk, map_mul, mul_apply_eq_comp, hv.2 k hk]
    · rfl
  have hSl : ∀ v ∈ S, ∀ m : List (Fin N), m.foldr (fun i => d (qs i)) v ∈ S := fun v hv m => by
    induction m with
    | nil => exact hv
    | cons i m ih => exact hS _ ih _ (hq i)
  let R : K → G → ℂ := fun v x => ∑ j, Λ j x ((l j).foldr (fun i => d (qs i)) v)
  refine ⟨R, (Finset.univ : Finset J).toList.map fun j => (l j).map qs, ?_, fun v hv1 hv2 => ?_, fun x => ?_⟩
  · intro m hm p hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp
    exact hq i
  · have hv : v ∈ S := ⟨hv1, hv2⟩
    refine ⟨continuous_finsetSum _ fun j _ => (hΛ j _ (hSl v hv _).2).1, ?_⟩
    have h1 := hT (fun i => d (qs i)) S (fun w hw i => ⟨hS w hw _ (hq i), hw.1.hasDerivAt (hq i)⟩) v hv
    have h2 := rep_sum hlin Finset.univ fun j => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
      κ j t • ρ (List.ofFn fun i => e (qs i) (t i)).prod ((l j).foldr (fun i => d (qs i)) v)
    rw [← h1] at h2
    filter_upwards [h2, ae_all_iff.2 fun j => (hΛ j _ (hSl v hv (l j)).2).2] with x e1 e2
    rw [e1]
    exact Finset.sum_congr rfl fun j _ => e2 j
  · refine ⟨∑ j, ‖Λ j x‖, fun v => ?_⟩
    rw [List.map_map, Finset.sum_map_toList, Finset.mul_sum]
    refine norm_sum_le_of_le _ fun j _ => ((Λ j x).le_opNorm _).trans ?_
    simp only [Function.comp, List.foldr_map]
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j => ‖Λ j x‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)) (norm_nonneg _)

end General

section Instance

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RightRegFund
open scoped Pointwise

theorem exists_transport (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hfund : I.IsFundDom (I.muA μf) fund) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (hR : I.IsRightReg μf fund R) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (T : G ≃* I.GA) (hT : Continuous T) (hT' : Continuous T.symm) :
    ∃ (μ : Measure G) (ρ : G →* (I.L2 μf fund →L[ℂ] I.L2 μf fund)), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant ∧
      (∀ g, ρ g = R (T g)) ∧ (∀ p : G → Prop, (∀ᵐ x ∂μ, p x) → ∀ᵐ y ∂(I.muA μf), p (T.symm y)) ∧
      (∀ C, IsCompact C → ∃ M : ℝ, ∀ v : I.L2 μf fund, IntegrableOn (fun x => I.ext v (T x)) C μ ∧
        ∫ x in C, ‖I.ext v (T x)‖ ∂μ ≤ M * ‖v‖) ∧
      (∀ (a : ℂ) (v w : I.L2 μf fund),
        (fun x => I.ext (a • v + w) (T x)) =ᵐ[μ] fun x => a * I.ext v (T x) + I.ext w (T x)) ∧
      (∀ g v, ‖ρ g v‖ = ‖v‖) ∧ (∀ v, Continuous fun g => ρ g v) ∧
      (∀ g v, (fun x => I.ext (ρ g v) (T x)) =ᵐ[μ] fun x => I.ext v (T (x * g))) ∧
      (∀ γ, T γ ∈ I.GFset → ∀ v : I.L2 μf fund, (fun x => I.ext v (T (γ * x))) =ᵐ[μ] fun x => I.ext v (T x)) ∧
      ∀ g : ℕ, 1 ≤ g → ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, (T k).2 ∈ I.Kg g := by
  obtain ⟨hT2, hL, hS, -, -, -, hK⟩ := GlobalTheory.T.finiteAdelicUnitary_congruenceTopology I
  obtain ⟨Γ, hΓ, hc, hfin, hfd⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant I μf
  obtain ⟨r1, r2, r3, r4, r5⟩ := isRightReg_props I μf fund hfund R hR
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : (I.muA μf).IsHaarMeasure := by
    unfold AutInst.muA
    haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
    exact Measure.prod.instIsHaarMeasure _ _
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  let E : I.GA ≃ₜ G := ⟨T.symm.toEquiv, hT', hT⟩
  let μ : Measure G := (I.muA μf).map T.symm
  have hemb : MeasurableEmbedding (T.symm : I.GA → G) := E.measurableEmbedding
  have hae : ∀ p : G → Prop, (∀ᵐ x ∂μ, p x) ↔ ∀ᵐ y ∂(I.muA μf), p (T.symm y) := fun p => hemb.ae_map_iff
  have hae' : ∀ p : I.GA → Prop, (∀ᵐ y ∂(I.muA μf), p y) → ∀ᵐ x ∂μ, p (T x) := fun p hp =>
    (hae _).2 (by simpa using hp)
  refine ⟨μ, ⟨⟨fun g => R (T g), by simp [r1]⟩, fun g h => by simp [r2]⟩,
    T.symm.isHaarMeasure_map _ hT' hT, ?_, fun _ => rfl, fun p => (hae p).1, fun C hC => ?_, fun a v w => ?_,
    fun g v => r3 _ _, fun v => (r4 v).comp hT, fun g v => ?_, fun γ hγ v => ?_, fun g hg => ?_⟩
  · refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_mul_const g) hemb.measurable]
    conv_rhs => rw [show μ = ((I.muA μf).map (· * T g)).map T.symm by rw [map_mul_right_eq_self]]
    rw [Measure.map_map hemb.measurable (measurable_mul_const _)]
    congr 1
    funext x
    simp
  · have hC' : IsCompact (T.symm ⁻¹' C) := E.isCompact_preimage.2 hC
    have hf : ((fun γ : Γ => (γ : I.GA)) ⁻¹' ((T.symm ⁻¹' C) * (T.symm ⁻¹' C)⁻¹ ∩ I.GFset)).Finite :=
      (hfin _ (hC'.mul hC'.inv)).preimage Subtype.val_injective.injOn
    obtain ⟨M, hM⟩ := GlobalTheory.LocalL2Isometry.integrableOn_rep hD hfund.1 hr hC'.measurableSet hC'.measure_lt_top.ne hf.toFinset
      fun γ hγ => hf.mem_toFinset.2 ⟨hγ, by rw [← hΓ]; exact γ.2⟩
    refine ⟨M, fun v => ⟨?_, ?_⟩⟩
    · rw [hemb.integrableOn_map_iff]
      simpa [Function.comp_def, AutInst.ext] using (hM v).1
    · rw [hemb.setIntegral_map]
      simpa [AutInst.ext] using (hM v).2
  · refine hae' (fun y => I.ext (a • v + w) y = a * I.ext v y + I.ext w y) ?_
    filter_upwards [ae_rep hfund.1 hr (Lp.coeFn_add (a • v) w), ae_rep hfund.1 hr (Lp.coeFn_smul a v)] with y e1 e2
    unfold AutInst.ext
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul]
  · simp only [_root_.map_mul]
    refine hae' (fun y => I.ext (R (T g) v) y = I.ext v (y * T g)) ?_
    filter_upwards [ae_rep hfund.1 hr (hR (T g) v), ae_good_mul hD (T g)] with y e1 e2
    obtain ⟨γ, e3, -⟩ := hr y
    unfold AutInst.ext at e1 ⊢
    rw [e1, e3, mul_assoc, rep_mul hr e2]
  · simp only [_root_.map_mul]
    exact hae' (fun y => I.ext v (T γ * y) = I.ext v y) ((r5 v).1.mono fun y hy => hy _ hγ)
  · obtain ⟨h1, ⟨K, h2⟩, -⟩ := hK g hg
    refine ⟨K.comap ((MonoidHom.snd _ _).comp T.toMonoidHom), ?_, fun k hk => h2 ▸ hk⟩
    have : IsOpen ((fun k : G => (T k).2) ⁻¹' (K : Set I.Gf)) := (h2 ▸ h1).preimage (continuous_snd.comp hT)
    exact this

open NumberField in

theorem hom_tens (I : AutInst) {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA}
    {R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)} {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] {σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)}
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] {σs : I.Ginf → (Hs →L[ℂ] Hs)}
    {tens : (∀ v, H v) → Hs} (ht : I.IsHilbTensor σ σs tens) {A : Hs →L[ℂ] I.L2 μf fund}
    (hA : A ∈ I.HomS σs μf fund R) {x : I.GA} (hx : x.2 = 1) (y z : ∀ v, H v)
    (hz : ∀ v, z v = σ v (uMat (x.1 v)) (y v)) : A (tens z) = R x (A (tens y)) := by
  obtain ⟨a, b⟩ := x
  obtain rfl : b = 1 := hx
  have h := congrArg (fun B : Hs →L[ℂ] I.L2 μf fund => B (tens y)) (hA a)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h, ht.2.1, funext hz]

end Instance

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict GlobalTheory.SmoothRep
open scoped TensorProduct InnerProductSpace ContDiff Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem exists_adelic_rep {D : D7} {θ : InfFam D} {V : HSp D} (hθ : IsInfFam θ) {μ : Measure (GA D V)}
    (hμ : μ.IsHaarMeasure) (hμ' : μ.IsMulRightInvariant)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : K → GA D V → ℂ}
    {ρ : GA D V →* (K →L[ℂ] K)}
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    {U : Subgroup (GA D V)} (hU : IsOpen (U : Set (GA D V))) :
    ∃ (R : K → GA D V → ℂ) (L : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧
      (∀ v, IsSmoothVector' θ V ρ v → (∀ k ∈ U, k ∈ GfC V → ρ k v = v) → Continuous (R v) ∧ ι v =ᵐ[μ] R v) ∧
      ∀ x, ∃ c : ℝ, ∀ v, ‖R v x‖ ≤ c * (L.map fun l => ‖l.foldr (dL2 θ V ρ) v‖).sum := by
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨N, τs, Xs, s, S, K, W, hX, hs, hK, hW, h⟩ := GlobalTheory.SobLoc.exists_adelic_chart hθ V U hU
  obtain ⟨-, -, -, -, -, -, -, -, -, hH⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨B, hB, hBW, hBc⟩ := local_compact_nhds hW
  have hc := fun i => GlobalTheory.SobLoc.oneP_spec hθ V (hH (τs i)).2 (hX i)
  have hΘ := GlobalTheory.continuous_prod_ofFn_curves N (fun i => oneP θ V (τs i) (Xs i)) fun i => (hc i).1
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt (GA D V) μ N _ (Metric.closedBall 0 S) B (K ^ N) hΘ
    (isCompact_closedBall _ _) hBc hB (pow_nonneg hK _)
  have hΩ : IsCompact (Set.image2 (fun (t : Fin N → ℝ) b => (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * b)
      (Metric.closedBall 0 S) B) := by
    rw [← Set.image_prod]
    exact ((isCompact_closedBall _ _).prod hBc).image ((hΘ.comp continuous_fst).mul continuous_snd)
  obtain ⟨R, L, hL, hR, hb⟩ := exists_rep_bound (μ := μ) (ι := ι) (ρ := ρ)
    (H := U ⊓ GfC V) (U := U) (A := {p : D.what₂.Tau × Mt V.rank | p.2 ∈ lieAt V p.1})
    (e := fun p => oneP θ V p.1 p.2) (qs := fun i => (τs i, Xs i))
    hloc hlin hiso hρ htr hU
    (fun y hy k hk => ⟨U.mul_mem (U.mul_mem (U.inv_mem hy) hk.1) hy,
      (MonoidHom.normal_ker (infHom V)).conj_mem' k hk.2 y⟩)
    (fun p hp => GlobalTheory.SobLoc.oneP_spec hθ V (hH p.1).2 hp)
    (fun p t k hk => GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem V _ _) hk.2)
    hX hs hΘ hΩ hC₁
    (fun f hf hf0 hfk => h₁ f _ hf hf0 fun x hx => by
      obtain ⟨φ, a, haU, ha, hφ, hφ'⟩ := h x (hBW hx)
      refine GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding N _ _ K φ (fun t => f (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)
        (fun t => f ((List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * x))
        (isCompact_univ_pi fun _ => isCompact_Icc) (isCompact_closedBall _ _) hK
        (hf.comp hΘ) (hf.comp (hΘ.mul continuous_const)) (fun g => hf0 _) (fun g => hf0 _)
        (fun t ht => ⟨mem_closedBall_zero_iff.2 (hφ t ht).1, le_of_eq ?_⟩) hφ'
      rw [(hφ t ht).2, hfk a ⟨haU, ha⟩])
  exact ⟨R, L, hL, fun v h1 h2 => hR v (fun k ps hps => h1 k (fun i => (ps i).1) (fun i => (ps i).2) hps)
    fun k hk => h2 k hk.1 hk.2, hb⟩

set_option maxHeartbeats 1000000 in

theorem exists_mmap {D : D7} {θ : InfFam D} {V : HSp D} (hθ : IsInfFam θ) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    {μ : Measure (GA D V)} (hμ : μ.IsHaarMeasure) (hμ' : μ.IsMulRightInvariant)
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : K → GA D V → ℂ}
    {ρ : GA D V →* (K →L[ℂ] K)}
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hρ : ∀ v, Continuous fun g => ρ g v) (htr : ∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g))
    (hleft : ∀ γ ∈ GQ V, ∀ v, (fun x => ι v (γ * x)) =ᵐ[μ] ι v)
    {U : Subgroup (GA D V)} (hU : IsOpen (U : Set (GA D V))) (Φ : ContinuousMultilinearMap ℂ M.H K)
    (he : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
      Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y))
    (hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y) :
    ∃ T : MMap M, (∀ u : M.Vec, ι (Φ fun τ => (u τ : M.H τ)) =ᵐ[μ] T u) ∧ (∀ u, IsAutFun V (T u)) ∧
      ∀ τ (u : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
        ∀ w : M.sm τ, ℓ w = T (Function.update u τ w) x := by
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨R, L, hL, hR, hb⟩ := exists_adelic_rep hθ hμ hμ' hloc hlin hiso hρ htr hU
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ he
  have p := fun y : M.Vec => hR _ (hsmM y).1 (hfix _)
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → ι (Φ fun τ => (y τ : M.H τ)) =ᵐ[μ] f →
      R (Φ fun τ => (y τ : M.H τ)) = f :=
    fun y f hf h => ((p y).1.ae_eq_iff_eq μ hf).1 ((p y).2.symm.trans h)
  let T : MMap M := MultilinearMap.mk' (fun y => R (Φ fun τ => (y τ : M.H τ)))
    (fun y τ a b => by
      refine uniq _ _ ((p _).1.add (p _).1) ?_
      have h1 := (p (Function.update y τ a)).2
      have h2 := (p (Function.update y τ b)).2
      simp only [GlobalTheory.BackForm.coe_update] at h1 h2 ⊢
      rw [Submodule.coe_add, Φ.map_update_add]
      filter_upwards [GlobalTheory.LocRep.rep_add hlin _ _, h1, h2] with x e1 e2 e3
      rw [e1, e2, e3, Pi.add_apply])
    (fun y τ c a => by
      refine uniq _ _ ((p _).1.const_smul c) ?_
      have h1 := (p (Function.update y τ a)).2
      simp only [GlobalTheory.BackForm.coe_update] at h1 ⊢
      rw [Submodule.coe_smul, Φ.map_update_smul]
      filter_upwards [GlobalTheory.LocRep.rep_smul hlin c _, h1] with x e1 e2
      rw [e1, e2, Pi.smul_apply, smul_eq_mul])
  refine ⟨T, fun u => (p u).2, fun u => ⟨fun γ hγ g => ?_, ⟨U, hU, fun k hk hk' g => ?_⟩, (p u).1⟩, fun τ u x => ?_⟩
  · refine (congrFun (uniq u (fun x => R (Φ fun τ => (u τ : M.H τ)) (γ * x))
      ((p u).1.comp (continuous_const_mul γ)) ?_) g).symm
    exact (hleft γ hγ _).symm.trans ((measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae (p u).2)
  · refine (congrFun (uniq u (fun x => R (Φ fun τ => (u τ : M.H τ)) (x * k))
      ((p u).1.comp (continuous_mul_const k)) ?_) g).symm
    have := rep_tr htr (p u).2 k
    rwa [hfix _ k hk hk'] at this
  · obtain ⟨c, hc⟩ := hb x
    exact GlobalTheory.BackForm.cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x c (fun y => hc _) τ u

theorem infMat_of_mem_fin {D : D7} (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : k ∈ GfC V) : infMat D.sp.cm.sig V.gram φ k = 1 := by
  have hk' : infHom V k = 1 := hk
  show (infHom V k).1.map φ = 1
  rw [hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem atTau_spec {D : D7} (V : HSp D) {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a : Mt V.rank}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : atTau θ V τ a ∈ GinfC V ∧
      ∀ τ', archM V (θ τ') (atTau θ V τ a) = (Pi.mulSingle τ a : D.what₂.Tau → Mt V.rank) τ' := by
  obtain ⟨L, hL1, -, -, -, -, hL3, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hu : (Pi.mulSingle τ a : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun τ' => by
    by_cases h : τ' = τ
    · subst h; simpa using ha
    · simp [Pi.mulSingle_eq_of_ne h, Formalism.QuantumDeterminants.UH]
  exact (hL3 τ a ha).symm ▸ hL1 _ hu

end GlobalTheory.TensRep

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
