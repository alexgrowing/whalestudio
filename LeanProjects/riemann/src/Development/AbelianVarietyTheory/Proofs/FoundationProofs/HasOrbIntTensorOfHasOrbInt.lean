import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.RestrMeas
open scoped ENNReal NNReal Topology Pointwise

noncomputable section

namespace GlobalTheory.Orb

section Local

variable {H : Type} [Group H] [MeasurableSpace H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [BorelSpace H] [LocallyCompactSpace H] [T2Space H] {T : Subgroup H} {dt : Measure T}
  {dh : Measure H} (hT : IsClosed (T : Set H)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] [SFinite dh]
  [dh.IsMulLeftInvariant]
include hT

theorem HasQuotInt.exists_lift {φ : H → ℂ} {c : ℂ} (h : HasQuotInt T dt dh φ c) (hi : LeftInv T φ) :
    ∃ f : H → ℂ, Integrable f dh ∧ ∫ x, f x ∂dh = c ∧
      ∀ x, Integrable (fun t : T => f (t * x)) dt ∧ ∫ t : T, f (t * x) ∂dt = φ x := by
  obtain ⟨b, hb, h1⟩ := exists_bruhat hT dt
  have hm : ∀ x, Measurable fun t : T => b (t * x) := fun x => hb.comp (measurable_subtype_coe.mul_const _)
  have hlt : ∀ x, ∀ᵐ t : T ∂dt, b (t * x) < ∞ := fun x => ae_lt_top (hm x) (by simp [h1])
  have hb' : Measurable fun x => (b x).toNNReal := hb.ennreal_toNNReal
  have hν := (isQuotMeasure_quotMeas dt dh hT).eq_map (b := fun x => (b x).toNNReal) hb'.coe_nnreal_ennreal
    fun x => by
      rw [← h1 x]
      exact lintegral_congr_ae ((hlt x).mono fun t ht => ENNReal.coe_toNNReal ht.ne)
  obtain ⟨h2, h3⟩ := h
  rw [quotInt, hν, integral_map measurable_mk.aemeasurable (hν ▸ h2.1)] at h3
  rw [hν] at h2
  replace h2 := h2.comp_measurable measurable_mk
  have e : descend T φ ∘ mk T = φ := hi.lift_descend
  rw [e, integrable_withDensity_iff_integrable_smul hb'] at h2
  simp only [hi.descend_mk] at h3
  rw [integral_withDensity_eq_integral_smul hb'] at h3
  refine ⟨_, h2, h3, fun x => ?_⟩
  simp only [fun t : T => hi t t.2 x, NNReal.smul_def]
  refine ⟨(integrable_toReal_of_lintegral_ne_top (hm x).aemeasurable (by simp [h1])).smul_const _, ?_⟩
  rw [integral_smul_const]
  exact (congrArg (· • φ x) ((integral_toReal (hm x).aemeasurable (hlt x)).trans (by simp [h1]))).trans (one_smul ℝ _)

theorem hasQuotInt_indicator_mul [IsFiniteMeasureOnCompacts dh] {K : Subgroup H} (ho : IsOpen (K : Set H))
    (hc : IsCompact (K : Set H)) :
    HasQuotInt T dt dh (((T : Set H) * (K : Set H)).indicator 1) (dh.real K / dt.real (K.subgroupOf T)) := by
  have ho' : IsOpen (K.subgroupOf T : Set T) := ho.preimage continuous_subtype_val
  have h0 : (dt.real (K.subgroupOf T) : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(ho'.measure_pos dt ⟨1, one_mem _⟩).ne',
      (hT.isClosedEmbedding_subtypeVal.isCompact_preimage hc).measure_ne_top⟩
  have h := (weil_integral (dt := dt) (dh := dh) hT (f := (K : Set H).indicator fun _ => (dt.real (K.subgroupOf T) : ℂ)⁻¹)
    ((integrable_indicator_iff ho.measurableSet).2 (integrableOn_const hc.measure_ne_top))).2
  convert h using 1
  · funext x
    by_cases hx : x ∈ (T : Set H) * (K : Set H)
    · obtain ⟨s, hs, k, hk, rfl⟩ := hx
      rw [indicator_of_mem (Set.mul_mem_mul hs hk)]
      refine Eq.trans ?_ (leftInv_integral (dt := dt) _ s hs k).symm
      have : ∀ t : T, (K : Set H).indicator (fun _ => (dt.real (K.subgroupOf T) : ℂ)⁻¹) (t * k) =
          (K.subgroupOf T : Set T).indicator (fun _ => (dt.real (K.subgroupOf T) : ℂ)⁻¹) t := fun t => by
        classical exact if_congr (K.mul_mem_cancel_right hk) rfl rfl
      simp [this, integral_indicator_const _ ho'.measurableSet, h0]
    · have : ∀ t : T, (t : H) * x ∉ (K : Set H) := fun t ht => hx ⟨_, T.inv_mem t.2, _, ht, by simp⟩
      simp [hx, this]
  · simp [integral_indicator_const _ ho.measurableSet, div_eq_mul_inv]

end Local

section Two

variable {H H₁ H₂ : Type} [Group H] [MeasurableSpace H] [TopologicalSpace H] [IsTopologicalGroup H]
  [SecondCountableTopology H] [BorelSpace H] [LocallyCompactSpace H] [T2Space H]
  [Group H₁] [MeasurableSpace H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁]
  [SecondCountableTopology H₁] [BorelSpace H₁] [LocallyCompactSpace H₁] [T2Space H₁]
  [Group H₂] [MeasurableSpace H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂]
  [SecondCountableTopology H₂] [BorelSpace H₂] [LocallyCompactSpace H₂] [T2Space H₂]
  {T : Subgroup H} {T₁ : Subgroup H₁} {T₂ : Subgroup H₂} {dt₁ : Measure T₁} {dt₂ : Measure T₂}
  {dh₁ : Measure H₁} {dh₂ : Measure H₂} [dt₁.IsHaarMeasure] [dt₁.IsMulRightInvariant] [dt₂.IsHaarMeasure]
  [dt₂.IsMulRightInvariant] [SFinite dh₁] [dh₁.IsMulLeftInvariant] [SFinite dh₂] [dh₂.IsMulLeftInvariant]
  {φ₁ : H₁ → ℂ} {φ₂ : H₂ → ℂ} {c₁ c₂ : ℂ}

theorem HasQuotInt.mul_of_measurePreserving (hT : IsClosed (T : Set H)) (hT₁ : IsClosed (T₁ : Set H₁))
    (hT₂ : IsClosed (T₂ : Set H₂)) {dt : Measure T} {dh : Measure H} [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
    [SFinite dh] [dh.IsMulLeftInvariant] {p : H →* H₁ × H₂} {q : T → T₁ × T₂}
    (hq : ∀ t : T, p t = (((q t).1 : H₁), ((q t).2 : H₂))) (mp : MeasurePreserving p dh (dh₁.prod dh₂))
    (mq : MeasurePreserving q dt (dt₁.prod dt₂)) (i₁ : LeftInv T₁ φ₁) (i₂ : LeftInv T₂ φ₂)
    (h₁ : HasQuotInt T₁ dt₁ dh₁ φ₁ c₁) (h₂ : HasQuotInt T₂ dt₂ dh₂ φ₂ c₂) :
    HasQuotInt T dt dh (fun x => φ₁ (p x).1 * φ₂ (p x).2) (c₁ * c₂) := by
  haveI : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  haveI : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  obtain ⟨f₁, a₁, rfl, b₁⟩ := h₁.exists_lift hT₁ i₁
  obtain ⟨f₂, a₂, rfl, b₂⟩ := h₂.exists_lift hT₂ i₂
  have hi := a₁.mul_prod a₂
  convert (weil_integral (dt := dt) hT (mp.integrable_comp_of_integrable hi)).2 using 1
  · funext x
    have hj := (b₁ (p x).1).1.mul_prod (b₂ (p x).2).1
    rw [← (b₁ _).2, ← (b₂ _).2, ← integral_prod_mul, ← mq.map_eq,
      integral_map mq.aemeasurable (mq.map_eq ▸ hj.aestronglyMeasurable)]
    simp [hq]
  · rw [← integral_prod_mul, ← mp.map_eq, integral_map mp.aemeasurable (mp.map_eq ▸ hi.aestronglyMeasurable)]
    rfl

omit [MeasurableSpace H₁] [IsTopologicalGroup H₁] [SecondCountableTopology H₁] [BorelSpace H₁] [LocallyCompactSpace H₁]
  [T2Space H₁] [MeasurableSpace H₂] [IsTopologicalGroup H₂] [SecondCountableTopology H₂] [BorelSpace H₂]
  [LocallyCompactSpace H₂] [T2Space H₂] in

def prodSub {U : Subgroup (H₁ × H₂)} (h : ∀ x, x ∈ U ↔ x.1 ∈ T₁ ∧ x.2 ∈ T₂) : T₁ × T₂ ≃ₜ* U where
  toFun t := ⟨(t.1, t.2), (h _).2 ⟨t.1.2, t.2.2⟩⟩
  invFun t := (⟨t.1.1, ((h _).1 t.2).1⟩, ⟨t.1.2, ((h _).1 t.2).2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := (Continuous.subtype_mk (by fun_prop) _).prodMk (Continuous.subtype_mk (by fun_prop) _)

theorem HasQuotInt.prod (hT₁ : IsClosed (T₁ : Set H₁)) (hT₂ : IsClosed (T₂ : Set H₂)) {U : Subgroup (H₁ × H₂)}
    (h : ∀ x, x ∈ U ↔ x.1 ∈ T₁ ∧ x.2 ∈ T₂) (i₁ : LeftInv T₁ φ₁) (i₂ : LeftInv T₂ φ₂)
    (h₁ : HasQuotInt T₁ dt₁ dh₁ φ₁ c₁) (h₂ : HasQuotInt T₂ dt₂ dh₂ φ₂ c₂) :
    HasQuotInt U ((dt₁.prod dt₂).map (prodSub h)) (dh₁.prod dh₂) (fun x => φ₁ x.1 * φ₂ x.2) (c₁ * c₂) := by
  haveI : LocallyCompactSpace T₁ := hT₁.locallyCompactSpace
  haveI : LocallyCompactSpace T₂ := hT₂.locallyCompactSpace
  have hU : IsClosed (U : Set (H₁ × H₂)) := by
    rw [show (U : Set (H₁ × H₂)) = (T₁ : Set H₁) ×ˢ (T₂ : Set H₂) from Set.ext h]
    exact hT₁.prod hT₂
  exact HasQuotInt.mul_of_measurePreserving hU hT₁ hT₂ (p := MonoidHom.id _) (q := (prodSub h).symm) (fun _ => rfl)
    (MeasurePreserving.id _)
    ⟨(map_continuous _).measurable, (prodSub h).toHomeomorph.toMeasurableEquiv.map_symm_map⟩ i₁ i₂ h₁ h₂

omit [MeasurableSpace H₁] [IsTopologicalGroup H₁] [SecondCountableTopology H₁] [BorelSpace H₁] [LocallyCompactSpace H₁]
  [T2Space H₁] [MeasurableSpace H₂] [IsTopologicalGroup H₂] [SecondCountableTopology H₂] [BorelSpace H₂]
  [LocallyCompactSpace H₂] [T2Space H₂] [TopologicalSpace H₁] [TopologicalSpace H₂] in

theorem mem_cent_prod (γ₁ : H₁) (γ₂ : H₂) (x : H₁ × H₂) : x ∈ cent (γ₁, γ₂) ↔ x.1 ∈ cent γ₁ ∧ x.2 ∈ cent γ₂ := by
  simp only [mem_cent, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]

theorem HasOrbInt.prod {γ₁ : H₁} {γ₂ : H₂} {m₁ : Measure (cent γ₁)} {m₂ : Measure (cent γ₂)} [m₁.IsHaarMeasure]
    [m₁.IsMulRightInvariant] [m₂.IsHaarMeasure] [m₂.IsMulRightInvariant] {f₁ : H₁ → ℂ} {f₂ : H₂ → ℂ}
    (h₁ : HasOrbInt dh₁ γ₁ m₁ f₁ c₁) (h₂ : HasOrbInt dh₂ γ₂ m₂ f₂ c₂) :
    HasOrbInt (dh₁.prod dh₂) (γ₁, γ₂) ((m₁.prod m₂).map (prodSub (mem_cent_prod γ₁ γ₂)))
      (fun x => f₁ x.1 * f₂ x.2) (c₁ * c₂) :=
  HasQuotInt.prod (isClosed_cent _) (isClosed_cent _) _ (leftInv_conjFn le_rfl _) (leftInv_conjFn le_rfl _) h₁ h₂

end Two

section Restricted

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Fintype W] [Countable V]
  [Group X] [MeasurableSpace X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SecondCountableTopology X] [BorelSpace X] [LocallyCompactSpace X] [T2Space X]
  [∀ w, Group (Ya w)] [∀ w, MeasurableSpace (Ya w)] [∀ w, TopologicalSpace (Ya w)] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, SecondCountableTopology (Ya w)] [∀ w, BorelSpace (Ya w)] [∀ w, LocallyCompactSpace (Ya w)]
  [∀ w, T2Space (Ya w)]
  [∀ v, Group (Yf v)] [∀ v, MeasurableSpace (Yf v)] [∀ v, TopologicalSpace (Yf v)] [∀ v, IsTopologicalGroup (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)] [∀ v, BorelSpace (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, T2Space (Yf v)]
  {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K : ∀ v, Subgroup (Yf v)} {μa : ∀ w, Measure (Ya w)}
  {μf : ∀ v, Measure (Yf v)} {μ : Measure X} {T : Subgroup X} {Ta : ∀ w, Subgroup (Ya w)} {Tf : ∀ v, Subgroup (Yf v)}
  {qa : ∀ w, T →* Ta w} {qf : ∀ v, T →* Tf v} {dta : ∀ w, Measure (Ta w)} {dtf : ∀ v, Measure (Tf v)} {dt : Measure T}

theorem hasQuotInt_tensor (hX : IsRestrGroup pa pf K) (hμ : IsHaarProd pa pf K μa μf μ) (hT : IsClosed (T : Set X))
    (hTa : ∀ w, IsClosed (Ta w : Set (Ya w))) (hTf : ∀ v, IsClosed (Tf v : Set (Yf v)))
    (ea : ∀ w (t : T), (qa w t : Ya w) = pa w t) (ef : ∀ v (t : T), (qf v t : Yf v) = pf v t)
    (hR : IsRestrGroup qa qf fun v => (K v).subgroupOf (Tf v))
    (hdt : IsHaarProd qa qf (fun v => (K v).subgroupOf (Tf v)) dta dtf dt)
    [∀ w, (dta w).IsMulRightInvariant] [∀ v, (dtf v).IsMulRightInvariant]
    {φa : ∀ w, Ya w → ℂ} {φf : ∀ v, Yf v → ℂ} {ca : W → ℂ} {cf : V → ℂ}
    (ia : ∀ w, LeftInv (Ta w) (φa w)) (jf : ∀ v, LeftInv (Tf v) (φf v))
    (ha : ∀ w, HasQuotInt (Ta w) (dta w) (μa w) (φa w) (ca w))
    (hf : ∀ v, HasQuotInt (Tf v) (dtf v) (μf v) (φf v) (cf v))
    (h1 : ∀ᶠ v in cofinite, φf v = ((Tf v : Set (Yf v)) * (K v : Set (Yf v))).indicator 1) :
    (∀ᶠ v in cofinite, cf v = 1) ∧
      HasQuotInt T dt μ (fun x => (∏ w, φa w (pa w x)) * ∏ᶠ v, φf v (pf v x)) ((∏ w, ca w) * ∏ᶠ v, cf v) := by
  classical
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI : ∀ w, LocallyCompactSpace (Ta w) := fun w => (hTa w).locallyCompactSpace
  haveI : ∀ v, LocallyCompactSpace (Tf v) := fun v => (hTf v).locallyCompactSpace
  haveI := hdt.isMulRightInvariant hR
  obtain ⟨_, _, _, hμ⟩ := hμ
  obtain ⟨_, _, _, hdt⟩ := hdt
  obtain ⟨S, hS⟩ := exists_finset_of_eventually (h1.and (hμ.1.and hdt.1))
  have hc : ∀ v ∉ S, cf v = 1 := fun v hv => by
    have := (hasQuotInt_indicator_mul (dt := dtf v) (dh := μf v) (hTf v) (hX.isOpen_K v) (hX.isCompact_K v)).2
    rw [← (hf v).2, (hS v hv).1, this, Measure.real, Measure.real, (hS v hv).2.1, (hS v hv).2.2]
    simp
  refine ⟨eventually_of_finset S hc, ?_⟩
  choose fa a1 a2 a3 using fun w => (ha w).exists_lift (hTa w) (ia w)
  choose g b1 b2 b3 using fun v => (hf v).exists_lift (hTf v) (jf v)
  let ff : ∀ v, Yf v → ℂ := fun v => if v ∈ S then g v else (K v : Set (Yf v)).indicator 1
  have e1 : ∀ v ∈ S, ff v = g v := fun v hv => if_pos hv
  have e2 : ∀ v ∉ S, ff v = (K v : Set (Yf v)).indicator 1 := fun v hv => if_neg hv
  obtain ⟨hI, hI'⟩ := hμ.integral_tensor_indicator (fun w => (hX.continuous_pa w).measurable)
    (fun v => (hX.continuous_pf v).measurable) (fun v => (hX.isOpen_K v).measurableSet) hX.eventually_mem
    (fun v hv => (hS v hv).2.1) e2 a1 fun v hv => e1 v hv ▸ b1 v
  have hKT : ∀ v {y}, y ∈ K v → y ∈ (Tf v : Set (Yf v)) * (K v : Set (Yf v)) := fun v y hy =>
    ⟨1, one_mem _, y, hy, one_mul y⟩
  have key : ∀ x, (∀ v ∉ S, pf v x ∈ K v) →
      ∫ t : T, (∏ w, fa w (pa w (t * x))) * ∏ᶠ v, ff v (pf v (t * x)) ∂dt =
        (∏ w, φa w (pa w x)) * ∏ᶠ v, φf v (pf v x) := fun x hx => by
    have := (hdt.integral_tensor_indicator (fun w => (hR.continuous_pa w).measurable)
      (fun v => (hR.continuous_pf v).measurable) (fun v => (hR.isOpen_K v).measurableSet) hR.eventually_mem
      (fa := fun w t => fa w (t * pa w x)) (ff := fun v t => ff v (t * pf v x))
      (fun v hv => (hS v hv).2.2) (fun v hv => funext fun t => by
        rw [e2 v hv]; exact if_congr ((K v).mul_mem_cancel_right (hx v hv)) rfl rfl)
      (fun w => (a3 w _).1) fun v hv => by rw [e1 v hv]; exact (b3 v _).1).2
    simp only [ea, ef, ← map_mul] at this
    rw [this, finprod_eq_prod_of_mem (K := fun v => K v)
      (fun v hv y hy => by rw [(hS v hv).1, indicator_of_mem (hKT v hy), Pi.one_apply]) hx]
    exact congrArg₂ _ (Finset.prod_congr rfl fun w _ => (a3 w _).2)
      (Finset.prod_congr rfl fun v hv => by rw [e1 v hv]; exact (b3 v _).2)
  convert (weil_integral (dt := dt) hT hI).2 using 1
  · funext x
    by_cases hx : ∀ v ∉ S, pf v x ∈ (Tf v : Set (Yf v)) * (K v : Set (Yf v))
    · have : ∀ v, ∃ s : Tf v, (v ∉ S → s * pf v x ∈ K v) ∧ (pf v x ∈ K v → s = 1) := fun v => by
        by_cases h : pf v x ∈ K v
        · exact ⟨1, fun _ => by simpa using h, fun _ => rfl⟩
        · by_cases hv : v ∈ S
          · exact ⟨1, fun h' => absurd hv h', fun _ => rfl⟩
          · obtain ⟨s, hs, k, hk, e⟩ := hx v hv
            exact ⟨⟨s, hs⟩⁻¹, fun _ => by simpa [← e] using hk, fun h' => absurd h' h⟩
      choose s s1 s2 using this
      obtain ⟨u, -, hu⟩ := hR.exists_eq 1 s ((hX.eventually_mem x).mono fun v hv => s2 v hv ▸ one_mem _)
      refine Eq.trans ?_ ((key (u * x) fun v hv => by rw [map_mul, ← ef, hu]; exact s1 v hv).symm.trans
        (leftInv_integral (dt := dt) (fun x => (∏ w, fa w (pa w x)) * ∏ᶠ v, ff v (pf v x)) u u.2 x))
      simp only [map_mul, ← ea, ← ef, fun w => ia w _ (qa w u).2, fun v => jf v _ (qf v u).2]
    · rw [finprod_eq_zero_of_notMem (fun v hv => (hS v hv).1) ((hX.eventually_mem x).mono fun v => hKT v) hx, mul_zero]
      refine (integral_eq_zero_of_ae (.of_forall fun t => ?_)).symm
      refine mul_eq_zero_of_right _ (finprod_eq_zero_of_notMem e2 (hX.eventually_mem _) fun h => hx fun v hv => ?_)
      exact ⟨_, (qf v t⁻¹).2, _, h v hv, by simp [ef]⟩
  · rw [hI', finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (hc v h)]
    exact congrArg₂ _ (Finset.prod_congr rfl fun w _ => (a2 w).symm)
      (Finset.prod_congr rfl fun v hv => by rw [e1 v hv, b2])

end Restricted

section Adelic

open GlobalTheory.AdelicU NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
  {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)} {γ : GAd σ J}
  {dta : ∀ w, Measure (cent (projArch σ J w γ))} {dtf : ∀ v, Measure (cent (proj σ J v γ))} {dt : Measure (cent γ)}
  {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}

theorem hasOrbInt_tensor_of_hasOrbInt (hμ : IsRestrictedProd σ J L μa μf μ) (hdt : IsCentProd L γ dta dtf dt)
    [∀ w, (dta w).IsMulRightInvariant] [∀ v, (dtf v).IsMulRightInvariant]
    (h1 : ∀ᶠ v in cofinite, ff v = unitLoc σ J L v)
    (hK : ∀ᶠ v in cofinite, {x | x⁻¹ * proj σ J v γ * x ∈ stabLoc σ J L v} =
      (cent (proj σ J v γ) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)))
    {ca : InfinitePlace F → ℂ} {cf : HeightOneSpectrum (𝓞 F) → ℂ}
    (ha : ∀ w, HasOrbInt (μa w) (projArch σ J w γ) (dta w) (fa w) (ca w))
    (hf : ∀ v, HasOrbInt (μf v) (proj σ J v γ) (dtf v) (ff v) (cf v)) :
    (∀ᶠ v in cofinite, cf v = 1) ∧ HasOrbInt μ γ dt (tensor σ J fa ff) ((∏ w, ca w) * ∏ᶠ v, cf v) := by
  have := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have h := hasQuotInt_tensor (restrGroup_GAd σ J L) hμ (isClosed_cent γ) (fun _ => isClosed_cent _)
    (fun _ => isClosed_cent _) (fun _ _ => rfl) (fun _ _ => rfl) (restrGroup_cent L γ) hdt
    (fun _ => leftInv_conjFn le_rfl _) (fun _ => leftInv_conjFn le_rfl _) ha hf
    ((h1.and hK).mono fun v hv => by rw [hv.1, ← hv.2]; rfl)
  refine ⟨h.1, ?_⟩
  rw [HasOrbInt, show conjFn γ (tensor σ J fa ff) = _ from funext fun x => ?_]
  · exact h.2
  · simp only [conjFn, tensor, map_mul, map_inv]

theorem hasOrbInt_tensor (hμ : IsRestrictedProd σ J L μa μf μ) (hdt : IsCentProd L γ dta dtf dt)
    [∀ w, (dta w).IsMulRightInvariant] [∀ v, (dtf v).IsMulRightInvariant]
    (hfa : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) (hff : IsFinFamily σ J L ff)
    (hK : ∀ᶠ v in cofinite, {x | x⁻¹ * proj σ J v γ * x ∈ stabLoc σ J L v} =
      (cent (proj σ J v γ) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)))
    (ha : ∀ w, IsProperOrbit (cent (projArch σ J w γ)) (projArch σ J w γ) ∨
      ∃ c, HasOrbInt (μa w) (projArch σ J w γ) (dta w) (fa w) c)
    (hf : ∀ v, IsProperOrbit (cent (proj σ J v γ)) (proj σ J v γ) ∨
      ∃ c, HasOrbInt (μf v) (proj σ J v γ) (dtf v) (ff v) c) :
    dt.IsMulRightInvariant ∧
    (∀ w, HasOrbInt (μa w) (projArch σ J w γ) (dta w) (fa w) (orbInt (μa w) (projArch σ J w γ) (dta w) (fa w))) ∧
    (∀ v, HasOrbInt (μf v) (proj σ J v γ) (dtf v) (ff v) (orbInt (μf v) (proj σ J v γ) (dtf v) (ff v))) ∧
    (∀ᶠ v in cofinite, orbInt (μf v) (proj σ J v γ) (dtf v) (ff v) = 1) ∧
    HasOrbInt μ γ dt (tensor σ J fa ff) ((∏ w, orbInt (μa w) (projArch σ J w γ) (dta w) (fa w)) *
      ∏ᶠ v, orbInt (μf v) (proj σ J v γ) (dtf v) (ff v)) := by
  have := hμ.haar_arch
  have := hμ.haar_loc
  have := hdt.1
  have := hdt.2.1
  have : LocallyCompactSpace (cent γ) := (isClosed_cent _).locallyCompactSpace
  have : ∀ w, LocallyCompactSpace (cent (projArch σ J w γ)) := fun _ => (isClosed_cent _).locallyCompactSpace
  have ha' := fun w => (ha w).elim (fun h => h.hasOrbInt (dh := μa w) (dt := dta w) (hfa w).1 (hfa w).2)
    fun ⟨_, h⟩ => ⟨h.1, rfl⟩
  have hf' := fun v => (hf v).elim
    (fun h => h.hasOrbInt (dh := μf v) (dt := dtf v) (hff.1 v).1.continuous (hff.1 v).2) fun ⟨_, h⟩ => ⟨h.1, rfl⟩
  exact ⟨IsHaarProd.isMulRightInvariant hdt (restrGroup_cent L γ), ha', hf',
    hasOrbInt_tensor_of_hasOrbInt hμ hdt hff.2 hK ha' hf'⟩

omit [Submodule.IsLattice E L] in

example (v : HeightOneSpectrum (𝓞 F)) : {x | x⁻¹ * proj σ J v 1 * x ∈ stabLoc σ J L v} =
    (cent (proj σ J v 1) : Set (GLoc σ J v)) * (stabLoc σ J L v : Set (GLoc σ J v)) :=
  Set.ext fun x => iff_of_true (by simp) ⟨x, mem_cent.2 (by simp), 1, one_mem _, mul_one x⟩

end Adelic

end GlobalTheory.Orb
