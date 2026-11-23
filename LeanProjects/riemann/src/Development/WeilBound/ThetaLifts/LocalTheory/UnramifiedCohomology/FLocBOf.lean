import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.SpanSoLoc
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.KAtCompact
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKG.Loc.FL

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Fin PositivityTheory.ThKCT
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
  {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

attribute [local instance] PositivityTheory.ThK.kc_ring PositivityTheory.ThK.adele_t2Space PositivityTheory.ThK.kc_smul

variable {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {v : Pl F}

theorem point {e ei ev} (hc : Cfg B M M₁ H H' e (shiftB σ H H')) (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e)
    (h : IsEvLoc M M₁ e ei ev) {om : Rep σ X W} {om₁ : Rep σ X₁ W₁} {χX χW : Chr F E} {rX rW : ℝ}
    (hx : Mix2 H H' χX χW rX rW om om₁ e) {ω ρ ω₁ ρ₁} (L : PositivityTheory.ThK.IsLocRep M B.ψ om v ω ρ)
    (L₁ : PositivityTheory.ThK.IsLocRep M₁ B.ψ om₁ v ω₁ ρ₁) (l : Fl F v n₁ d₁ →ₗ[ℂ] ℂ) (hl : augAt om₁ v ≤ LinearMap.ker l)
    {u m : UA σ X.J} (hu : u ∈ unip σ X H) (hu' : u ∈ UAt σ X (evFin F v)) {t g₁} (hm : IsLevi (W₁ := X₁) H t g₁ m)
    (hm' : m ∈ UAt σ X (evFin F v)) (hg : g₁ ∈ UAt σ X₁ (evFin F v)) {ψ} (hψ : ψ ∈ SB _) (a : (AE F E)ˣ) :
    l (ev v (rv B M v (idem F v • shiftB σ H H' a) (ω (u * m, 1) ψ))) =
      (χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) * l (ev v (rv B M v (idem F v • shiftB σ H H' (t * a)) ψ)) := by
  obtain ⟨r, s, hX⟩ := hc.herm
  obtain ⟨i, j, hH⟩ := hc.hH
  obtain ⟨i', j', hH'⟩ := hc.hH'
  obtain ⟨ε, A', hfr⟩ := Fr.isFr hc.base (.inl hX) hH
  have hp : u * m ∈ uSub σ X v := mul_mem (show u ∈ uSub σ X v from hu') hm'
  have o : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := (uSub σ W v).one_mem
  have o₁ : (1 : UA σ W₁.J) ∈ UAt σ W₁ (evFin F v) := (uSub σ W₁ v).one_mem
  obtain ⟨z, c, hz⟩ := (Fr.IsFr.ad hfr).fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hc.base.cm) (u⁻¹).2 (Fr.mem_unip.1 (inv_mem hu)).1
  have hmi := Fr.levi_inv hm
  let x' := incV F H'.x
  let P₁ : Fin n → AE F E := idem F v • ((cA σ a.1 * c * (t⁻¹).1) • incV F H.x)
  let P₂ : Fin n → AE F E := idem F v • (incM F H.ι *ᵥ (cA σ a.1 • (mat g₁⁻¹ *ᵥ z)))
  let P₃ : Fin n → AE F E := idem F v • (cA σ (t * a).1 • incV F H.y)
  have sh : ∀ b : (AE F E)ˣ, idem F v • shiftB σ H H' b = Matrix.vecMulVec (idem F v • (cA σ b.1 • incV F H.y)) x' := fun b => by
    rw [shiftB, Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]
  have atv : ∀ P : Fin n → AE F E, At (evFin F v) (Matrix.vecMulVec (idem F v • P) x') := fun P => by
    rw [Matrix.smul_vecMulVec]; exact Cone.at_idem v _
  have e1 : mat (u * m)⁻¹ *ᵥ (idem F v • (cA σ a.1 • incV F H.y)) = P₁ + (P₂ + P₃) := by
    have hz' : mat u⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ z + c • incV F H.x := hz
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, mul_inv_rev, Fr.mat_mul, ← Matrix.mulVec_mulVec, hz', Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_smul, hmi.1, hmi.2.1, Fr.levi_vec hmi, inv_inv]
    simp only [P₁, P₂, P₃, ← smul_add, Matrix.mulVec_smul, Units.val_mul, map_mul]
    congr 1
    simp only [smul_add, smul_smul, mul_assoc, mul_comm (cA σ t.1)]
    abel
  have at0 : At (evFin F v) (Matrix.vecMulVec (P₁ + (P₂ + P₃)) x') := by
    simp only [P₁, P₂, P₃, ← smul_add]; exact atv _
  have rr : ∀ w, At (evFin F v) w → ∀ φ ∈ SB _, rv B M v w φ = ρ w φ := fun w hw φ hφ =>
    (L.actsH w hw φ hφ _).1 (rv_acts B M hw φ)
  have e2 := L.impl _ hp 1 o _ at0 ψ hψ
  rw [← e1, Matrix.mul_vecMulVec, Fr.mat_cancel', Fr.mat_one, Matrix.transpose_one, Matrix.mul_one, e1, ← rr _ at0 ψ hψ,
    ← rr _ (atv _) _ (L.pres _ hp 1 o ψ hψ)] at e2
  rw [sh, ← e2, sh]
  set ψ' := rv B M v (Matrix.vecMulVec (P₁ + (P₂ + P₃)) x') ψ with hψ'
  have s' : ψ' ∈ SB _ := rv_sb hc.base M v _ hψ
  have hev : ev v ψ' ∈ SB _ := (h.vac v).2 ▸ Submodule.mem_map_of_mem s'
  have e3 := ev_loc hc.good hc.good₁ h (S := om (u * m, 1)) (S₁ := om₁ (g₁, 1)) (fun Φ hΦ => by
      have := hx t g₁ m hm u hu 1 1 1 Fr.levi_one 1 (one_mem _) Φ hΦ
      rwa [mul_one (1 : UA σ W.J)] at this) s' (L.pres _ hp 1 o _ s') ((L.acts _ hp 1 o _ s' _).2 rfl)
    ((L₁.acts _ hg 1 o₁ _ hev _).2 rfl)
  have e4 : l (ω₁ (g₁, 1) (ev v ψ')) = l (ev v ψ') := by
    have := hl (Submodule.subset_span ⟨g₁, hg, _, hev, _, L₁.pres _ hg 1 o₁ _ hev, (L₁.acts _ hg 1 o₁ _ hev _).2 rfl, rfl⟩)
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  have e5 : ev v ψ' = ev v (rv B M v (Matrix.vecMulVec P₃ x') ψ) := by
    rw [hψ', rv_add B M v hH'.xx, rv_add B M v hH'.xx,
      ev_inv hc.base hc.good hc.good₁ h (atv _) (he.inv _ (.inl ⟨idem F v • ((cA σ a.1 * c * (t⁻¹).1) • x'), by
        rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩))
        (rv_sb hc.base M v _ (rv_sb hc.base M v _ hψ)),
      ev_inv hc.base hc.good hc.good₁ h (atv _) (he.inv _ (.inr ⟨idem F v • (cA σ a.1 • (mat g₁⁻¹ *ᵥ z)), by
        rw [Matrix.mulVec_smul _ (idem F v)]⟩)) (rv_sb hc.base M v _ hψ)]
  rw [e3, map_smul, e4, e5]
  change _ = _ * l (ev v (rv B M v (Matrix.vecMulVec P₃ x') ψ))
  generalize l (ev v (rv B M v (Matrix.vecMulVec P₃ x') ψ)) = q
  simp

theorem fLocB_of (hI : IdeleFub) (hJ : IdealId0) (hS : StabEx) (hIw : IwaEx) (hMx : MixAB) (hT : PositivityTheory.ThKEst.TriplePair)
    (hSt : SoStab) (hSe : SoEv) (hLi : LinEx) : FLocB := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' c e ei ev he h K m hK hm X om om' om₁ om₁' T T₁
  have hc : Cfg B G.M' G₁.M' H H' e (shiftB σ H H') :=
    ⟨T.base, ⟨_, _, T.geo.hV'⟩, ⟨_, _, T.geo.hW⟩, ⟨_, _, T₁.geo.hV'⟩, ⟨_, _, T₁.geo.hW⟩, T.geo.hM', T₁.geo.hM',
      ⟨_, _, c.hH⟩, ⟨_, _, c.hH'⟩, .inr ⟨he, rfl⟩⟩
  obtain ⟨-, hP, -⟩ := hT F E σ B _ _ G X om om' T
  obtain ⟨-, hP₁, -⟩ := hT F E σ B _ _ G₁ X om₁ om₁' T₁
  have b1 := T.geo.eBig
  have b2 := T.geo.aBig
  have b3 := T.geo.lt
  obtain ⟨ee, hee⟩ := T.geo.even
  have b4 := c.ep
  have b5 := c.eq
  have hν : Continuous X.ν := hP.hW.1
  set z := (a - (b + 2)) / 2 + 1 with hzd
  have hz : 2 ≤ z := by omega
  have hzr : ((a + (b + 2) : ℕ) : ℝ) / 2 = (b + 1 : ℕ) + (z : ℝ) := by
    have : a + (b + 2) = 2 * (b + 1 + z) := by omega
    rw [this]; push_cast; ring
  have hx := (hMx F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q) G.M' G₁.M' c.hH c.hH'
    X.α (X.α / X.β) om' om₁' (by convert hP using 1 <;> omega) hP₁).2 e he
  set v := B.v₁
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ om' ⟨hP.base, ⟨_, _, hP.herm⟩, ⟨_, _, hP.skew⟩, hP.good, _, _, hP.weil⟩ v
  obtain ⟨ω₁, ρ₁, L₁⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ _ om₁'
    ⟨hP₁.base, ⟨_, _, hP₁.herm⟩, ⟨_, _, hP₁.skew⟩, hP₁.good, _, _, hP₁.weil⟩ v
  have hIK := hIw F E σ B _ _ _ _ _ H T.base T.geo.hV' (fun e => by simpa [e, form] using c.hH.xy) c.hH.xx K hK
  haveI := kAt_compact hIK.1 v
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : IsProbabilityMeasure (m.kf v) := ⟨(hm.kf v).2⟩
  haveI := (hm.kf v).1
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  haveI := (hm.xf v).1
  have o1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (uSub σ G.W v).one_mem
  have sb : ∀ k ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB _, ω (k, 1) φ ∈ SB _ := fun k hk φ hφ => L.pres _ hk _ o1 φ hφ
  have op : ∀ (k : kAt K (evFin F v)) (l : (AE F E)ˣ), ∀ φ ∈ SB _,
      opF v (fun Φ => G.M'.co.rho B.ψ (idem F v • shiftB σ H H' l) (om' (k.1, 1) Φ)) φ =
        rv B G.M' v (idem F v • shiftB σ H H' l) (ω (k.1, 1) φ) :=
    fun k l φ hφ => opF_eq hφ (rv_sb hc.base G.M' v _ (sb _ (kAt_mem k) φ hφ)) (acts_comp ((IsUWeilPair.isUSplitting hP.weil).pres _)
      ((L.acts _ (kAt_mem k) _ o1 φ hφ _).2 rfl) (rv_acts B _ (Fin.at_idem v _) _))
  let A : Fl F v _ _ → Fl F v _ _ := fun φ y => ∫ l : idAt E (evFin F v),
    ev v (rv B G.M' v (idem F v • shiftB σ H H' l.1) φ) y * wt X.ν z l.1 ∂(m.xf v)
  have hA := fun φ (hφ : φ ∈ SB _) => tate' hI hJ hS hc h v m hm hν hz (φ := φ) hφ
  have lc : ∀ φ ∈ SB _, IsLocallyConstant fun k : uSub σ G.V' v => ω (k.1, 1) φ := fun φ hφ => by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun k₀ => ?_
    obtain ⟨U, hU, hU'⟩ := (PositivityTheory.ThKF0.actsEx F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP v).2.2 _ (sb _ k₀.2 φ hφ)
    have t : Tendsto (fun k : uSub σ G.V' v => (((k * k₀⁻¹).1, 1) : UA σ G.V'.J × UA σ G.W.J)) (𝓝 k₀) (𝓝 1) := by
      have : Continuous fun k : uSub σ G.V' v => (((k * k₀⁻¹).1, 1) : UA σ G.V'.J × UA σ G.W.J) :=
        (continuous_subtype_val.comp (continuous_mul_const k₀⁻¹)).prodMk continuous_const
      have := this.tendsto k₀
      rwa [mul_inv_cancel] at this
    filter_upwards [t.eventually hU] with k hk
    have h1 := (L.acts _ (k * k₀⁻¹).2 _ o1 _ (sb _ k₀.2 φ hφ) _).1 (hU' _ hk (k * k₀⁻¹).2 o1)
    rw [← L.mul _ (k * k₀⁻¹).2 _ o1 _ k₀.2 _ o1 φ hφ, mul_one, ← Subgroup.coe_mul, inv_mul_cancel_right] at h1
    exact h1.symm
  have lcK : ∀ φ ∈ SB _, IsLocallyConstant fun k : kAt K (evFin F v) => A (ω (k.1, 1) φ) := fun φ hφ =>
    ((lc φ hφ).comp A).comp_continuous (f := fun k : kAt K (evFin F v) => (⟨k.1, kAt_mem k⟩ : uSub σ G.V' v))
      (continuous_subtype_val.subtype_mk _)
  have ce : ∀ φ ∈ SB _, coneF B G.M' om' m v (ev v) (shiftB σ H H') X.ν z φ =
      fun y => ∫ k : kAt K (evFin F v), A (ω (k.1, 1) φ) y * 1 ∂(m.kf v) :=
    fun φ hφ => funext fun y => by
      simp only [coneF, op _ _ φ hφ, A, wt, mul_assoc, mul_one]
  refine ⟨fun g hg φ hφ φ₁ hφ₁ hact l hl => ?_, fun φ hφ => ?_⟩
  · have cl : ∀ φ ∈ SB _, l (coneF B G.M' om' m v (ev v) (shiftB σ H H') X.ν z φ) =
        ∫ k : kAt K (evFin F v), l (A (ω (k.1, 1) φ)) ∂(m.kf v) := fun φ hφ => by
      rw [ce φ hφ, int_lin (m.kf v) (fun k => A (ω (k.1, 1) φ)) (fun _ => 1) (lcK φ hφ).range_finite
        (fun a => ((lcK φ hφ).isOpen_fiber a).measurableSet) Set.univ (fun a ha => absurd trivial ha)
        (integrable_const _).integrableOn l]
      simp only [mul_one]
    have al : ∀ ψ ∈ SB _, l (A ψ) = ∫ s : idAt E (evFin F v),
        l (ev v (rv B G.M' v (idem F v • shiftB σ H H' s.1) ψ)) * wt X.ν z s.1 ∂(m.xf v) := fun ψ hψ =>
      int_lin (m.xf v) _ _ (hA ψ hψ).1 (fun a => ((hA ψ hψ).2.1.isOpen_fiber a).measurableSet) _ (fun a ha => not_not.1 ha)
        (hA ψ hψ).2.2 l
    rw [cl _ hφ₁, cl _ hφ, (L.acts g hg 1 o1 φ hφ _).1 hact]
    have := KInv.kInv T.base T.geo.hV' c.hH hK hIK v (m.kf v) (f := fun x => l (A (ω (x, 1) φ)))
      (continuousOn_iff_continuous_restrict.2 ((lc φ hφ).comp fun ψ => l (A ψ)).continuous)
      (fun u hu hu' t g₁ mm hL hm' hg₁ ht x hxx => by
        have hp : u * mm ∈ uSub σ G.V' v := mul_mem (show u ∈ uSub σ G.V' v from hu') hm'
        have e := L.mul _ hp 1 o1 x hxx 1 o1 φ hφ
        rw [mul_one] at e
        have s1 := sb x hxx φ hφ
        let t₀ : idAt E (evFin F v) := ⟨t, Subgroup.subset_closure ht⟩
        have h0 : (0 : ℝ) < absE F E t := lt_of_le_of_ne NNReal.zero_le_coe
          (Ne.symm (NNReal.coe_ne_zero.2 ((Group.isUnit t).map (absE F E)).ne_zero))
        simp only [e]
        rw [al _ (sb _ hp _ s1), al _ s1, ← integral_mul_left_eq_self (μ := m.xf v) (fun s : idAt E (evFin F v) =>
          l (ev v (rv B G.M' v (idem F v • shiftB σ H H' s.1) (ω (x, 1) φ))) * wt X.ν z s.1) t₀, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        have n0 : ((absE F E t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
        simp only [point hc he h hx L L₁ l hl hu hu' hL hm' hg₁ s1, t₀, Subgroup.coe_mul, wt, map_mul, hzr, Real.rpow_add h0,
          Real.rpow_natCast, Chars.ν]
        push_cast
        ring) hg
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    have e := L.mul _ (kAt_mem k) 1 o1 g hg 1 o1 φ hφ
    rw [mul_one] at e
    simp only [e]
  · obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
      by_contra hn
      push Not at hn
      exact h.ne (ContinuousLinearMap.ext hn)
    have s0 := hφ.1
    have gen : ∀ a : Fl F v _ _, a ∈ SB _ → (∀ u, Function.update G.M'.vac v a u ∈ SB _) ∧
        (∀ᶠ u in cofinite, Function.update G.M'.vac v a u = G.M'.vac u) ∧
        ∀ᶠ u in cofinite, Function.update G.M'.vac v a u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1 := by
      intro a ha
      have cf : ∀ᶠ u in cofinite, Function.update G.M'.vac v a u = G.M'.vac u := by
        filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with u hu using Function.update_of_ne hu _ _
      refine ⟨fun u => ?_, cf, by filter_upwards [cf, hc.good.std] with u a b using a.trans b⟩
      by_cases e : u = v
      · subst e; rwa [Function.update_self]
      · rw [Function.update_of_ne e]; exact (hc.good.vac u).1
    have up : ∀ a : Fl F v _ _, (fun u => ev u (Function.update G.M'.vac v a u)) = Function.update G₁.M'.vac v (ev v a) :=
      fun a => funext fun u => by
        by_cases e : u = v
        · subst e; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne e, Function.update_of_ne e, (h.vac u).1]
    have pt : ∀ (k : kAt K (evFin F v)) (s : (AE F E)ˣ), ev v (rv B G.M' v (idem F v • shiftB σ H H' s) (ω (k.1, 1) φ)) ∈
        Submodule.span ℂ (G₁.M'.SoLoc B.ψ B.τ₁) := fun k s => by
      obtain ⟨g1, g2, g3⟩ := gen φ s0
      have s1 := sb _ (kAt_mem k) φ s0
      obtain ⟨g4, -, g6⟩ := gen _ s1
      have s2 := rv_sb hc.base G.M' v (locCo G.M'.co v (idem F v • shiftB σ H H' s)) s1
      obtain ⟨g7, g8, -⟩ := gen _ s2
      have m0 : pure f (Function.update G.M'.vac v φ) ∈ G.M'.So B.ψ B.τ₁ :=
        Submodule.subset_span ⟨f, _, g1, g2, by rwa [Function.update_self], rfl⟩
      have m1 := hSt F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP (k.1, 1) _ m0
      rw [(PositivityTheory.ThKF.pureAct F _ v (om' (k.1, 1)) f _ g1 g3).2.2 _ (by
        rw [Function.update_self]; exact (L.acts _ (kAt_mem k) _ o1 φ s0 _).2 rfl), Function.update_idem] at m1
      have m2 := (hSe F E σ B _ _ _ _ _ _ _ _ H H' _ _ _ _ _ _ _ _ G.M' G₁.M' c.hH c.hH' T.base T.geo.hV' T.geo.hW hc.good hc.good₁
        e he _ m1).2 (idem F v • cA σ s.1)
      rw [incM_rk, smul_assoc, show cA σ s.1 • rk F H.y H'.x = shiftB σ H H' s from rfl,
        (PositivityTheory.ThKF.pureAct F _ v (G.M'.co.rho B.ψ (idem F v • shiftB σ H H' s)) f _ g4 g6).2.2 _ (by
          rw [Function.update_self]; exact rv_acts B _ (Fin.at_idem v _) _), Function.update_idem, h.pure f _ g7 g8, up] at m2
      exact so_slice hc.good₁ hf m2
    refine span_soLoc hLi T.base T₁.geo.hV' T₁.geo.hW _ _ ?_
    rw [ce φ s0]
    refine (int_fin (m.kf v) (fun k => A (ω (k.1, 1) φ)) (fun _ => 1) (lcK φ s0).range_finite
      (fun a => ((lcK φ s0).isOpen_fiber a).measurableSet) Set.univ (fun a ha => absurd trivial ha)
      (integrable_const _).integrableOn _ fun k => ?_).2
    have q := hA _ (sb _ (kAt_mem k) φ s0)
    exact (int_fin (m.xf v) _ _ q.1 (fun a => (q.2.1.isOpen_fiber a).measurableSet) _ (fun a ha => not_not.1 ha) q.2.2 _
      fun s => pt k s.1).2

end PositivityTheory.ThKG.Loc.FL

end
