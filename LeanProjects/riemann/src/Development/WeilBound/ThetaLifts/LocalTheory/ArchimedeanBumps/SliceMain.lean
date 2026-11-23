import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SliceLine
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsMaximalCompactInfinite

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKCT PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pureA_mem' {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem exists_admissible_functional_adelic {κ : Type} [Fintype κ] (L : SInf F κ →L[ℂ] ℂ) (a : κ → Af F) : ∃ l ∈ (adeleClass F).adm κ,
    ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g a * L f := by
  have ex : ∀ Φ : schA F κ, ∃ f : SInf F κ, ∀ y, f y = Φ.1 (ptA y a) := by
    rintro ⟨Φ, hΦ⟩
    induction hΦ using Submodule.span_induction with
    | mem _ h => obtain ⟨f, g, -, rfl⟩ := h; exact ⟨g a • f, fun y => (mul_comm _ _).trans (pureA_ptA f g y a).symm⟩
    | zero => exact ⟨0, fun _ => rfl⟩
    | add _ _ _ _ p q => obtain ⟨p, hp⟩ := p; obtain ⟨q, hq⟩ := q; exact ⟨p + q, fun y => by rw [SchwartzMap.add_apply, hp, hq]; rfl⟩
    | smul c _ _ p => obtain ⟨p, hp⟩ := p; exact ⟨c • p, fun y => by rw [SchwartzMap.smul_apply, hp]; rfl⟩
  choose s hs using ex
  let s' : schA F κ →ₗ[ℂ] SInf F κ :=
    { toFun := s
      map_add' := fun a b => SchwartzMap.ext fun z => by rw [SchwartzMap.add_apply, hs, hs, hs]; rfl
      map_smul' := fun c a => SchwartzMap.ext fun z => by rw [SchwartzMap.smul_apply, hs, hs]; rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (L.toLinearMap ∘ₗ s')
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g a * L f := fun f g hg => by
    have h1 := LinearMap.congr_fun hl ⟨_, pureA_mem' f hg⟩
    have h2 : s ⟨_, pureA_mem' f hg⟩ = g a • f := SchwartzMap.ext fun z => by
      rw [hs]; exact (pureA_ptA f g z a).trans (mul_comm _ _)
    refine h1.trans ?_
    show L (s _) = _
    rw [h2, map_smul, smul_eq_mul]
  exact ⟨l, fun g hg => ⟨g a • L, fun f => h f g hg⟩, h⟩

theorem joint_cont {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]
    {K C : Type} [TopologicalSpace K] [TopologicalSpace C] (A : C → SchwartzMap V ℂ →L[ℂ] SchwartzMap V₁ ℂ)
    (hA : ∀ g, Continuous fun c => A c g)
    (hb : ∀ q : Seminorm ℂ (SchwartzMap V₁ ℂ), Continuous q → ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ c g, q (A c g) ≤ p g)
    (g : K → SchwartzMap V ℂ) (hg : Continuous g) : Continuous fun x : K × C => A x.2 (g x.1) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ V₁ ℂ).tendsto_nhds]
  intro i ε hε
  have hq := (schwartz_withSeminorms ℂ V₁ ℂ).continuous_seminorm i
  obtain ⟨p, hp, hle⟩ := hb _ hq
  have c1 : Continuous fun x : K × C => p (g x.1 - g x₀.1) + schwartzSeminormFamily ℂ V₁ ℂ i (A x.2 (g x₀.1) - A x₀.2 (g x₀.1)) :=
    (hp.comp ((hg.comp continuous_fst).sub continuous_const)).add (hq.comp (((hA _).comp continuous_snd).sub continuous_const))
  have := (c1.tendsto x₀).eventually (gt_mem_nhds (a := ε) (by simpa using hε))
  filter_upwards [this] with x hx
  refine lt_of_le_of_lt ?_ hx
  have e : A x.2 (g x.1) - A x₀.2 (g x₀.1) = A x.2 (g x.1 - g x₀.1) + (A x.2 (g x₀.1) - A x₀.2 (g x₀.1)) := by
    rw [map_sub]; abel
  rw [e]
  exact (map_add_le_add _ _ _).trans (add_le_add_left (hle _ _) _)

theorem dom_int {ι : Type} [Fintype ι] (z : ℕ) : ∃ N : ℕ,
    Integrable (fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N) ∧ 0 < ∫ c : ι → ℂ, (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N := by
  set a := 2 * Fintype.card ι * z
  set b := Module.finrank ℝ (ι → ℂ) + 1
  have hc : Continuous fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ (a + b) :=
    Continuous.div (by fun_prop) (by fun_prop) fun c => by positivity
  have hi : Integrable fun c : ι → ℂ => (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ (a + b) := by
    refine (integrable_one_add_norm (μ := volume) (r := b) (by simp [b])).mono' hc.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast, pow_add, ← div_div,
      div_eq_mul_inv]
    refine mul_le_of_le_one_left (by positivity) ((div_le_one (by positivity)).2 ?_)
    have : ∏ w, ‖c w‖ ^ 2 ≤ ∏ _w : ι, (1 + ‖c‖) ^ 2 :=
      Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => by
        have := norm_le_pi_norm c w
        gcongr; linarith
    calc _ ≤ (∏ _w : ι, (1 + ‖c‖) ^ 2) ^ z := by gcongr
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_mul, ← mul_assoc]
  exact ⟨a + b, hi, integral_pos_of_integrable_nonneg_nonzero (x := 1) hc hi (fun c => by positivity) (by simp; positivity)⟩

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem xi_int {lift} (hL : IsLift σ B lift) (x : @Measure (idAt E (evI F)) (borel _))
    (hx : @Measure.IsHaarMeasure _ _ _ (borel _) x) (z : ℕ) (hz : 1 ≤ z) : ∃ N : ℕ, @Integrable _ _ _ _ (borel _)
      (fun t : idAt E (evI F) => (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z / (1 + ‖fun w => piInf (B.emb w) (t.1 : AE F E)‖) ^ N) x := by
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le' hz
  obtain ⟨N, hi, hp⟩ := dom_int (ι := InfinitePlace F) z
  obtain ⟨κ, hκ, h⟩ := hL.haar x hx
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  refine ⟨N, ?_⟩
  have h1 := h fun c => (((∏ w, ‖c w‖ ^ 2) ^ (z + 1) / (1 + ‖c‖) ^ N : ℝ) : ℂ)
  have h2 : ∫ c : InfinitePlace F → ℂ, (((∏ w, ‖c w‖ ^ 2) ^ (z + 1) / (1 + ‖c‖) ^ N : ℝ) : ℂ) * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹ =
      ((∫ c : InfinitePlace F → ℂ, (∏ w, ‖c w‖ ^ 2) ^ z / (1 + ‖c‖) ^ N : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun w => Measure.ae_eval_ne (fun _ : InfinitePlace F => (volume : Measure ℂ)) w 0] with c hc
    have : (∏ w, ‖c w‖ ^ 2) ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc w))
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [pow_succ]
    field_simp
  rw [h2, integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj] at h1
  exact Integrable.of_integral_ne_zero (by rw [h1]; positivity)

theorem mem_kAt {K : Subgroup (UA σ X.J)} {k} : k ∈ kAt K (evI F) ↔ k ∈ K ∧ k ∈ UAt σ X (evI F) := by
  have : Subgroup.closure (UAt σ X (evI F)) = atGrp σ X (evI F) := Subgroup.closure_eq (atGrp σ X (evI F))
  rw [kAt, this]; rfl

theorem kAt_cpt (hS : StabEx) (hB : B.IsGood σ) {r s} (hX : X.IsHerm σ B r s) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) :
    IsCompact (kAt K (evI F) : Set (UA σ X.J)) := by
  obtain ⟨K', -, -, h1, h2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K' = K := Subgroup.ext fun g => (h1 g).trans (hK g).symm
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g - 1 := (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  have hc : IsClosed {g : UA σ X.J | realAd F 1 • (mat g - 1) = mat g - 1} := by
    refine isClosed_eq ?_ hm
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.smul_apply, Algebra.smul_def]
    exact continuous_const.mul (hm.matrix_elem i j)
  have : (kAt K' (evI F) : Set (UA σ X.J)) = (K' : Set (UA σ X.J)) ∩ {g : UA σ X.J | realAd F 1 • (mat g - 1) = mat g - 1} :=
    Set.ext fun g => mem_kAt.trans (and_congr_right fun _ => at_iff)
  rw [this]
  exact h2.inter_right hc

variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
  {u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)} {ei ev}

theorem k_ops (hS : StabEx) (hO : ArchOp) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {χX χW om r s r' s'}
    (hP : IsPair B M χX χW om r s r' s') : ∃ T : kAt K (evI F) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d),
      (∀ k, IsArchOp om (k.1, 1) (T k)) ∧ (∀ k, ∀ f ∈ M.Pol B.ψ B.emb, T k f ∈ M.Pol B.ψ B.emb) ∧ (∀ f, Continuous fun k => T k f) ∧
      ∀ q : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
        ∀ k f, q (T k f) ≤ p f := by
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := (atGrp σ W (evI F)).one_mem
  choose T hT hPol using fun k : kAt K (evI F) => hO F E σ B n d X W M χX χW om r s r' s' hP k.1 (mem_kAt.1 k.2).2 1 h1
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 (kAt_cpt hS hP.base hP.herm hK)
  obtain ⟨g₀, hg, ⟨a, ha⟩, -⟩ := vac_fin hP.good
  have hw : ∀ f (l : SInf F (Fin n × Fin d) →L[ℂ] ℂ), Continuous fun k => l (T k f) := fun f l => by
    obtain ⟨l', hl, hl'⟩ := exists_admissible_functional_adelic ((g₀ a)⁻¹ • l) a
    have hc := (IsUWeilPair.isUSplitting hP.weil).cont l' hl _ (pureA_mem' f hg)
    refine (hc.comp (continuous_subtype_val.prodMk (continuous_const (y := (1 : UA σ W.J))))).congr fun k => ?_
    have := (hT k).1 f g₀ hg
    exact (congrArg l' this).trans (by
      rw [hl' _ _ hg]
      exact mul_inv_cancel_left₀ ha _)
  have hb : ∀ f (q : Seminorm ℂ (SInf F (Fin n × Fin d))), Continuous q → ∃ C, ∀ k, q (T k f) ≤ C := fun f q hq =>
    weak_bounded (fun k => T k f) (fun l => by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hw f l).continuousOn
      exact ⟨C, fun k => hC k trivial⟩) q hq
  refine ⟨T, hT, fun k => hPol k ⟨(mem_kAt.1 k.2).2, ((hK _).1 (mem_kAt.1 k.2).1).1⟩ ⟨h1, fun w => ?_⟩,
    fun f => strong_of_weak _ (hw f) (hb f), fun q hq => equicont T q hq fun f => hb f q hq⟩
  rw [mat_one', Matrix.map_one _ (map_zero _) (map_one _)]
  exact Commute.one_left _

theorem op_comp (hH : ArchHeis) (hU : ArchUniq) {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') {k T}
    (hT : IsArchOp om (k, 1) T) {w} (hw : At (evI F) w) (f : SInf F (Fin n × Fin d)) :
    opI (fun Φ => M.co.rho B.ψ w (om (k, 1) Φ)) f = opI (M.co.rho B.ψ w) (T f) := by
  obtain ⟨f₁, hf⟩ := (hH F E σ B n d X W M hP.base).2 w hw (T f)
  rw [opI_eq hU hf]
  refine opI_eq hU fun r hr => ?_
  have h1 := hT.2 f r hr
  show M.co.rho B.ψ w (om (k, 1) _) = _
  rw [h1]
  exact hf r ⟨hr.1, h1 ▸ (IsUWeilPair.isUSplitting hP.weil).pres _ _ hr.2⟩

theorem shift_eq (hc : Cfg B M M₁ H H' e u) {lift} (hL : IsLift σ B lift) : ∃ cc : (AE F E)ˣ → InfinitePlace F → ℂ, Continuous cc ∧
    (∀ t w, ‖cc t w‖ = ‖piInf (B.emb w) (t : AE F E)‖) ∧ ∀ t, realAd F 1 • u t = lift (cc t) • u 1 := by
  have key : ∀ a : AE F E, lift (fun w => piInf (B.emb w) a) = realAd F 1 • a := fun a => by
    rw [← hL.inv _ (hL.part a).1]; congr 1; funext w; exact ((hL.part a).2 w).symm
  rcases hc.ev with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨fun t w => piInf (B.emb w) (t : AE F E), continuous_pi fun w => (hL.cont w).comp Units.continuous_val,
      fun _ _ => rfl, fun t => ?_⟩
    simp only [key, shiftA, Units.val_one, one_smul, smul_assoc]
  · refine ⟨fun t w => piInf (B.emb w) (cA σ (t : AE F E)), continuous_pi fun w => ?_, fun t w => ?_, fun t => ?_⟩
    · simp only [hL.conj]; exact Complex.continuous_conj.comp ((hL.cont w).comp Units.continuous_val)
    · simp only [hL.conj, Complex.norm_conj]
    · simp only [key, shiftB, Units.val_one, map_one, one_smul, smul_assoc]

theorem cone_core (hSt : StabEx) (hO : ArchOp) (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hI : SchInt)
    (hc : Cfg B M M₁ H H' e u) (hl : IsEvLoc M M₁ e ei ev) {lift} (hL : IsLift σ B lift) {K : Subgroup (UA σ X.J)} {m : LocMeas K}
    (hK : IsStab B K) (hm : m.Is) {χX χW om r s r' s'} (hP : IsPair B M χX χW om r s r' s') (ν : Chr F E) (z : ℕ)
    (hν : Continuous ν) (hz : 1 ≤ z) : ∃ L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁),
      ∀ f (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ),
        (∀ k : kAt K (evI F), @Integrable _ _ _ _ (borel _) (fun t : idAt E (evI F) =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) m.xi) ∧
        (Integrable (fun k : kAt K (evI F) => @integral _ _ _ _ (borel _) m.xi fun t =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) m.ki) ∧
        l (L f) = ∫ k, @integral _ _ _ _ (borel _) m.xi (fun t =>
          l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1) ∂m.ki := by
  obtain ⟨A, hA, hAe, hAd⟩ := line_ex hS hH hU hc hl hL
  obtain ⟨T, hT, -, hTc, hTb⟩ := k_ops hSt hO hK hP
  obtain ⟨cc, hcc, hcn, hce⟩ := shift_eq hc hL
  obtain ⟨N, hN⟩ := xi_int hL m.xi hm.xi z hz
  letI : MeasurableSpace (idAt E (evI F)) := borel _
  haveI : BorelSpace (idAt E (evI F)) := ⟨rfl⟩
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨-, h2, -⟩ := PositivityTheory.ThKEst.lcsc_UA σ X.J
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : CompactSpace (kAt K (evI F)) := isCompact_iff_compactSpace.1 (kAt_cpt hSt hP.base hP.herm hK)
  haveI := hm.ki
  haveI := hm.xi
  haveI : IsFiniteMeasure m.ki := ⟨isCompact_univ.measure_lt_top⟩
  haveI : SigmaFinite m.ki := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite m.ki := MeasureTheory.instSFiniteOfSigmaFinite
  have hpos : ∀ t : idAt E (evI F), 0 < (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z / (1 + ‖fun w => piInf (B.emb w) (t.1 : AE F E)‖) ^ N :=
    fun t => div_pos (pow_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (pi_ne _ _)) 2) _) (by positivity)
  haveI : SigmaFinite m.xi := by
    have h := hN.aefinStronglyMeasurable
    have h1 : m.xi.restrict h.sigmaFiniteSet = m.xi := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      have h2 := h.ae_eq_zero_compl
      rw [Filter.EventuallyEq, ae_restrict_iff' h.measurableSet.compl] at h2
      filter_upwards [h2] with t ht
      by_contra hn
      exact (hpos t).ne' (ht hn)
    rw [← h1]
    infer_instance
  have hab : ∀ t : idAt E (evI F), (absE F E t.1 : ℝ) = ∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2 :=
    fun t => hL.abs _ ((hL.idAt _).1 t.2)
  have hwc : Continuous fun t : idAt E (evI F) => wt ν z t.1 := by
    simp only [wt, hab]
    refine (continuous_subtype_val.comp (hν.comp continuous_subtype_val)).mul (Continuous.pow (Complex.continuous_ofReal.comp ?_) _)
    exact continuous_finset_prod _ fun w _ => ((hL.cont w).comp (Units.continuous_val.comp continuous_subtype_val)).norm.pow 2
  have hwn : ∀ t : idAt E (evI F), ‖wt ν z t.1‖ = (∏ w, ‖piInf (B.emb w) (t.1 : AE F E)‖ ^ 2) ^ z := fun t => by
    rw [wt, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, hab, Real.norm_of_nonneg (by positivity)]
  let G : kAt K (evI F) × idAt E (evI F) → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) :=
    fun x => wt ν z x.2.1 • (A (cc x.2.1)).comp (T x.1)
  have hGc : ∀ f, Continuous fun x => G x f := fun f => by
    have h1 := joint_cont (fun t : idAt E (evI F) => A (cc t.1)) (fun g => (hA g).comp (hcc.comp continuous_subtype_val))
      (fun q hq => by
        obtain ⟨p, hp, h⟩ := hAd q 0 hq
        exact ⟨p, hp, fun c g => by simpa using h _ g⟩) _ (hTc f)
    exact (hwc.comp continuous_snd).smul h1
  have hGb : ∀ q : Seminorm ℂ (SInf F (Fin n₁ × Fin d₁)), Continuous q → ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
      ∀ x f, q (G x f) ≤ p f * ((∏ w, ‖piInf (B.emb w) (x.2.1 : AE F E)‖ ^ 2) ^ z /
        (1 + ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖) ^ N) := fun q hq => by
    obtain ⟨p, hp, h⟩ := hAd q N hq
    obtain ⟨p', hp', h'⟩ := hTb p hp
    refine ⟨p', hp', fun x f => ?_⟩
    have e1 : ‖cc x.2.1‖ = ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖ := by
      simp only [Pi.norm_def]
      congr 2
      funext w
      exact NNReal.eq (hcn _ w)
    have h3 := (h (cc x.2.1) (T x.1 f)).trans (h' x.1 f)
    rw [e1, ← le_div_iff₀ (by positivity)] at h3
    change q (wt ν z x.2.1 • A (cc x.2.1) (T x.1 f)) ≤ _
    rw [map_smul_eq_mul, hwn]
    refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans (le_of_eq ?_)
    ring
  have hD : Integrable (fun x : kAt K (evI F) × idAt E (evI F) => (∏ w, ‖piInf (B.emb w) (x.2.1 : AE F E)‖ ^ 2) ^ z /
      (1 + ‖fun w => piInf (B.emb w) (x.2.1 : AE F E)‖) ^ N) (m.ki.prod m.xi) := by
    simpa using (integrable_const (μ := m.ki) (1 : ℝ)).mul_prod hN
  obtain ⟨L, hL'⟩ := weak_op (m.ki.prod m.xi) G (fun f => hI _ _ _ _ (hGc f) fun k j => by
      obtain ⟨p, -, h⟩ := hGb _ (cont_seminorm k j)
      exact (hD.const_mul (p f)).mono' ((cont_seminorm k j).comp (hGc f)).aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (apply_nonneg _ _)]; exact h x f))
    fun k j => by
      obtain ⟨p, hp, h⟩ := hGb _ (cont_seminorm k j)
      exact ⟨p, _, hp, hD, h⟩
  have hGe : ∀ f (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ) (k : kAt K (evI F)) (t : idAt E (evI F)),
      l (ei (opI (fun Φ => M.co.rho B.ψ (realAd F 1 • u t.1) (om (k.1, 1) Φ)) f)) * wt ν z t.1 = l (G (k, t) f) := fun f l k t => by
    rw [hce, op_comp hH hU hP (hT k) (at_smul (hL.supp _) _), ← hAe, mul_comm]
    exact (map_smul l _ _).symm
  refine ⟨L, fun f l => ?_⟩
  simp only [hGe]
  refine ⟨fun k => ?_, (hL' f l).1.integral_prod_left, (hL' f l).2.trans (integral_prod _ (hL' f l).1)⟩
  obtain ⟨p, -, h⟩ := hGb ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  exact (hN.const_mul (p f)).mono' (l.continuous.comp ((hGc f).comp (Continuous.prodMk_right k))).aestronglyMeasurable
    (Eventually.of_forall fun t => h (k, t) f)

theorem archSlice_of (hSt : StabEx) (hO : ArchOp) (hS : Slice) (hH : ArchHeis) (hU : ArchUniq) (hI : SchInt) : ArchSlice := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc hl lift hL K m hK hm χX χW om r s r' s' hP
  refine ⟨kAt_cpt hSt hP.base hP.herm hK, fun k hk => ⟨(mem_kAt.1 hk).2, ((hK _).1 (mem_kAt.1 hk).1).1⟩, fun f l => ?_⟩
  obtain ⟨A, hA, hAe, hAd⟩ := line_ex hS hH hU hc hl hL
  obtain ⟨T, hT, -, hTc, hTb⟩ := k_ops hSt hO hK hP
  have e1 : ∀ (k : kAt K (evI F)) c, ei (opI (fun Φ => M.co.rho B.ψ (lift c • u 1) (om (k.1, 1) Φ)) f) = A c (T k f) := fun k c => by
    rw [op_comp hH hU hP (hT k) (at_smul (hL.supp _) _), ← hAe]
  simp only [e1]
  refine ⟨l.continuous.comp (joint_cont A hA (fun q hq => ?_) _ (hTc f)), fun N => ?_, fun ν z hν hz L hLc => ?_⟩
  · obtain ⟨p, hp, h⟩ := hAd q 0 hq
    exact ⟨p, hp, fun c g => by simpa using h _ g⟩
  · obtain ⟨p, hp, h⟩ := hAd ((normSeminorm ℂ ℂ).comp l.toLinearMap) N l.continuous.norm
    obtain ⟨p', -, h'⟩ := hTb p hp
    exact ⟨p' f, fun k c => (h c _).trans (h' k f)⟩
  · obtain ⟨L', h⟩ := cone_core hSt hO hS hH hU hI hc hl hL hK hm hP ν z hν hz
    have : L f = L' f := SchwartzMap.ext fun y => by
      rw [hLc f y, ← evAt_apply y (L' f), (h f (evAt y)).2.2]
      simp only [evAt_apply, wt, mul_assoc]
    rw [this, (h f l).2.2]
    simp only [wt, mul_assoc]

end PositivityTheory.ThKG.Loc.Bump

end
