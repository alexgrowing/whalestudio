import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

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

private theorem hasTrace_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (d : ENNReal) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : HasTrace m ρ f s) : HasTrace (d • m) ρ f ((d.toReal : ℂ) * s) := by
  obtain ⟨A, hA, hF⟩ := h
  have hb : (d.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)
  refine ⟨(d.toReal : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure hdt, ?_⟩, hasFinTrace_smul A _ hb hF⟩
  rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]

private theorem exists_ext {ι α : Type} {P : α → Type} (f : ι → α) (hf : Function.Injective f) (d : ∀ a, P a)
    (g : ∀ i, P (f i)) : ∃ G : ∀ a, P a, ∀ i, G (f i) = g i := by
  classical
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ g h.choose else d a, fun i => ?_⟩
  have aux : ∀ (j : ι) (e : f j = f i), (e ▸ g j : P (f i)) = g i := by
    intro j e
    obtain rfl := hf e
    rfl
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact aux _ _

private theorem prod_mem_of {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    (l : List (H →L[ℂ] H)) (h : ∀ B ∈ l, ∀ v ∈ W, B v ∈ W) : ∀ v ∈ W, l.prod v ∈ W := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons B l ih =>
    intro v hv
    rw [List.prod_cons]
    exact h B (by simp) _ (ih (fun B' hB' => h B' (by simp [hB'])) v hv)

section Loc
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem rhoL_comm' {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hm, ← hm]
  unfold rhoL at *
  rw [hc]

private theorem oloc_fix {w w' : Pl K} (h : w ≠ w') [MeasurableSpace (Gw n w)] (m : Measure (Gw n w)) (ψ : Gw n w → ℂ)
    (B : LL μ →L[ℂ] LL μ) (hB : IsOloc μ w m ψ B) (J : Subgroup (Gw n w')) {v : LL μ} (hv : v ∈ fixL μ w' J) :
    B v ∈ fixL μ w' J := by
  have hc : ∀ x : Gw n w', ∀ b, B (rhoL μ w' x b) = rhoL μ w' x (B b) := by
    intro x b
    refine ext_inner_left ℂ fun a => ?_
    rw [hB, ← ContinuousLinearMap.adjoint_inner_left, hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h1 := congrArg (· b) (rhoL_comm' μ h g x)
    simp only [ContinuousLinearMap.mul_apply] at h1
    simp only
    rw [ContinuousLinearMap.adjoint_inner_left, h1]
  simp only [fixL, fixF, Submodule.mem_iInf] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hv' : rhoL μ w' k v = v := hv _ ⟨k, hk, rfl⟩
  show rhoL μ w' k (B v) = B v
  rw [← hc, hv']

private theorem isClosed_fixL (w : Pl K) (J : Subgroup (Gw n w)) : IsClosed (fixL μ w J : Set (LL μ)) := by
  simp only [fixL, fixF, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id

private theorem prj_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {x : H} (hx : x ∈ W) : prj W x = x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure W hx)

private theorem prj_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Y W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (h : Y ≤ W) (x : H) : prj Y x ∈ W :=
  Submodule.topologicalClosure_minimal Y h hW (Submodule.starProjection_apply_mem _ x)

private theorem trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext x
    simp [prj]
  simp [trOn, this, GroundTheory.Automorphic.trace]

end Loc

private theorem under_over' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.archimedean_baseChange_trace_comparison :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (k n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
        (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
        ∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (a : TI F n)
          [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (m : ∀ u : Pl E, Measure (Gw n u)),
          (∀ u, (m u).IsHaarMeasure) →
        ∀ (q : Pl F) (w₀ : PlacesOver E q), GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V →
        ∀ (τ₀ : SmIrr (Gw n w₀.1)) (τ : ∀ v : Pl F, SmIrr (Gw n (T.mk' v).1)), Occurs μ V w₀.1 τ₀ →
          (∀ v ∈ T.sp, Occurs μ V (T.mk' v).1 (τ v)) → ∀ y : ℝ, 0 < y →
        ∀ (mm : ∀ u : Pl E, Measure (Gw n u)), (∀ u, mm u = (m u (T.J u))⁻¹ • m u) →
        ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ T.sp ↔ v ∈ Set.range p) →
          ∃ c : ℂ, (T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ → c ≠ 0) ∧
            ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), (∀ v ∈ T.sp, Test (ψ v) ∧ ∀ u ∈ T.J (T.mk' v).1, ∀ g, ψ v (u * g) = ψ v g) →
            ∀ (e : Fin n → ℤ), Antitone e → ∀ (j : ℕ) (sq : ℂ) (t : Pl F → ℂ),
              HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • e)).indicator 1) sq →
              (∀ v ∈ T.sp, HasTrace (m (T.mk' v).1) (τ v).ρ (ψ v) (t v)) →
            ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
              trOn (T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y) ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) = c * sq * ∏ v ∈ T.sp, t v := by
    classical
  intro F E _ _ _ _ _ σ k n hn μ _ D s hs hposition νF _ a _ _ m hm q w₀ hq T V hV τ₀ τ hocc₀ hocc y hy mm hmmdef r p hpinj hpr
  obtain ⟨hZc, hZs, hZa, hY⟩ := UpperTheory.ConvolutionTheory.L1.zBasic F E σ k n hn μ D s hs hposition νF a q w₀ hq T V hV y hy
  have hpm : ∀ i, p i ∈ T.sp := fun i => (hpr _).2 ⟨i, rfl⟩
  have hprod : ∀ t : Pl F → ℂ, ∏ v ∈ T.sp, t v = ∏ i, t (p i) := by
    intro t
    have e : T.sp = Finset.univ.image p := by
      ext v
      simp [hpr]
    rw [e, Finset.prod_image (fun _ _ _ _ h => hpinj h)]
  have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
    haveI := hm u
    exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
  have ht0 : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
    haveI := hm u
    exact (T.co u).1.measure_lt_top.ne
  have hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0 := fun u => ENNReal.inv_ne_zero.2 (ht0 u)
  have hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤ := fun u => ENNReal.inv_ne_top.2 (h0 u)
  have hmm : ∀ u, (mm u).IsHaarMeasure := fun u => by
    haveI := hm u
    rw [hmmdef u]
    exact Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)
  have hmm1 : ∀ u, mm u (T.J u) = 1 := fun u => by
    rw [hmmdef u, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht0 u)]
  obtain ⟨bb, hbb, htr⟩ : ∃ bb : Pl E → ℂ, (∀ u, bb u ≠ 0) ∧
      ∀ (u : Pl E) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gw n u) X) (f : Gw n u → ℂ) (z : ℂ),
        HasTrace (m u) ρ f z → HasTrace (mm u) ρ f (bb u * z) := by
    refine ⟨fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ), fun u => ?_, fun u X _ _ ρ f z h => ?_⟩
    · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)
    · rw [hmmdef u]
      exact hasTrace_smul _ (hd0 u) (hdt u) h
  have hJq : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hne : ∀ i, (T.mk' (p i)).1 ≠ w₀.1 := by
    intro i h
    have h1 : p i = q := calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = w₀.1.under (𝓞 F) := by rw [h]
      _ = q := under_over' _
    exact T.q_not (h1 ▸ (Finset.mem_filter.1 (hpm i)).1)
  have hover : ∀ i j, (T.mk' (p i)).1 = (T.mk' (p j)).1 → p i = p j := by
    intro i j h
    calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = (T.mk' (p j)).1.under (𝓞 F) := by rw [h]
      _ = p j := under_over' _
  set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO
  have hYfix : T.Y μ V O y ≤ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := by
    rw [hY, ← hJq]
    exact inf_le_right.trans (iInf₂_le w₀.1 (Or.inl rfl))
  have step : ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) (e : Fin n → ℤ), Antitone e → ∀ (j : ℕ) (B : Fin r → LL μ →L[ℂ] LL μ),
      (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
      trOn (T.Y μ V O y) ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) =
        trOn (T.Y μ V O y) (Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod) := by
    intro ψ e he j B hB
    have hP : ∀ x, (List.ofFn B).prod (prj (T.Y μ V O y) x) ∈
        fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := fun x => by
      refine prod_mem_of _ _ ?_ _ (prj_mem (isClosed_fixL μ _ _) hYfix x)
      intro C hC v hv
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hC
      exact oloc_fix μ (hne i) _ _ _ (hB i) _ hv
    have hU := UpperTheory.ConvolutionTheory.C.uiwPow E n μ w₀.1 e he j
    simp only [trOn]
    congr 1
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hU, ContinuousLinearMap.comp_apply, prj_of_mem _ (hP x)]
  by_cases hZ : T.Z μ V O y = ⊥
  · refine ⟨0, fun h => absurd hZ h, ?_⟩
    intro ψ _ e _ j sq t _ _ B _
    have hYb : T.Y μ V O y = ⊥ := by rw [hY, hZ, bot_inf_eq]
    rw [hYb, trOn_bot]
    simp
  let w : Fin (r + 1) → Pl E := Fin.cons w₀.1 fun i => (T.mk' (p i)).1
  have hw : Function.Injective w := by
    refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
    · rintro ⟨i, h⟩
      exact hne i h
    · intro i j h
      exact hpinj (hover i j h)
  have hmk : ∀ u, u ∈ T.marked ↔ ∃ i, w i = u := by
    intro u
    constructor
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨0, rfl⟩
      · obtain ⟨i, rfl⟩ := (hpr v).1 hv
        exact ⟨i.succ, rfl⟩
    · rintro ⟨i, rfl⟩
      refine Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨p i, hpm i, rfl⟩) i
  have hinf : ∀ G : ∀ u : Pl E, Subgroup (Gw n u),
      ⨅ u ∈ T.marked, fixL μ u (G u) = ⨅ i, fixL μ (w i) (G (w i)) := by
    intro G
    refine le_antisymm (le_iInf fun i => iInf₂_le (w i) ((hmk _).2 ⟨i, rfl⟩)) (le_iInf₂ fun u hu => ?_)
    obtain ⟨i, rfl⟩ := (hmk u).1 hu
    exact iInf_le _ i
  have hYZ : T.Y μ V O y = T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i)) := by rw [hY, hinf T.J]
  let σ' : ∀ i, SmIrr (Gw n (w i)) := Fin.cons (α := fun i => SmIrr (Gw n (w i))) τ₀ fun i => τ (p i)
  have hoccs : ∀ i, Occurs μ V (w i) (σ' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hocc₀
    · exact hocc _ (hpm i)
  have hadm : ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
      FiniteDimensional ℂ ↥(T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (U i)) := by
    intro U hU
    obtain ⟨G, hG⟩ := exists_ext (P := fun u : Pl E => Subgroup (Gw n u)) w hw (fun _ => ⊥) U
    have h := hZa G (fun u hu => by
      obtain ⟨i, rfl⟩ := (hmk u).1 hu
      rw [hG]
      exact hU i)
    have e : (⨅ i, fixL μ (w i) (G (w i))) = ⨅ i, fixL μ (w i) (U i) := iInf_congr fun i => by rw [hG i]
    rw [hinf G, e] at h
    exact h
  obtain ⟨N, hN, hfac⟩ := UpperTheory.ConvolutionTheory.C.summandFactor E n μ V (T.Z μ V O y) (r + 1) w σ' hV hw hoccs
    (fun v hv => hv.1.1) hZ hZc (fun i g v hv => hZs (w i) ((hmk _).2 ⟨i, rfl⟩) g v hv) hadm
  refine ⟨N * ∏ i, bb (w i), fun _ => ?_, ?_⟩
  · exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)
  intro ψ hψ e he j sq t hsq ht B hB
  obtain ⟨hCO, -, hI⟩ := UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test E n w₀.1
  obtain ⟨htest, hinv⟩ := hI (j • e)
  let φ : ∀ i, Gw n (w i) → ℂ :=
    Fin.cons (α := fun i => Gw n (w i) → ℂ) ((GM.iwCoset w₀.1 (j • e)).indicator 1) fun i => ψ (p i)
  let T' : Fin (r + 1) → LL μ →L[ℂ] LL μ := Fin.cons (α := fun _ => LL μ →L[ℂ] LL μ) (Uiw μ w₀.1 (j • e)) B
  let s' : Fin (r + 1) → ℂ := Fin.cons (α := fun _ => ℂ) (bb w₀.1 * sq) fun i => bb (T.mk' (p i)).1 * t (p i)
  have h1 : ∀ i, Test (φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htest
    · exact (hψ _ (hpm i)).1
  have h2 : ∀ i, ∀ u ∈ T.J (w i), ∀ g, φ i (u * g) = φ i g := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro u hu g
      exact hinv u (hJq ▸ hu) g
    · intro u hu g
      exact (hψ _ (hpm i)).2 u hu g
  have h3 : ∀ i, IsOloc μ (w i) (mm (w i)) (φ i) (T' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · haveI := hmm w₀.1
      exact UpperTheory.ConvolutionTheory.C.hopOloc E n μ w₀.1 (mm w₀.1) (GLnLocal.iwahori (w₀.1.adicCompletion E) n)
        (Cartan.diagPow (w₀.1.adicCompletion E) n (j • e)) hCO (by rw [← hJq]; exact hmm1 _)
    · exact hB i
  have h4 : ∀ i, HasTrace (mm (w i)) (σ' i).ρ (φ i) (s' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htr w₀.1 τ₀.V τ₀.ρ _ sq hsq
    · exact htr _ (τ (p i)).V (τ (p i)).ρ _ _ (ht _ (hpm i))
  have hf : trOn (T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i))) (List.ofFn T').prod = N * ∏ i, s' i :=
    hfac (fun i => T.J (w i)) (fun i => mm (w i)) φ T' s' (fun i => T.co _) (fun i => hmm _) h1 h2 h3 h4
  have hlist : (List.ofFn T').prod = Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod := by
    rw [List.ofFn_succ, List.prod_cons]
    rfl
  rw [step ψ e he j B hB, hYZ, ← hlist, hf, hprod t]
  have hw0 : w 0 = w₀.1 := rfl
  have hws : ∀ i : Fin r, w i.succ = (T.mk' (p i)).1 := fun _ => rfl
  have hs0 : s' 0 = bb w₀.1 * sq := rfl
  have hss : ∀ i : Fin r, s' i.succ = bb (T.mk' (p i)).1 * t (p i) := fun _ => rfl
  simp only [Fin.prod_univ_succ, hw0, hws, hs0, hss, Finset.prod_mul_distrib]
  ring
