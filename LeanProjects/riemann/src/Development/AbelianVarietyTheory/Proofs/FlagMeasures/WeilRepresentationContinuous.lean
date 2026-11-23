import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrientedWeilDatumOfAdelicWeilRepTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnSwap

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace GlobalTheory.ThetaJointCont

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
variable {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem level_near (hom : IsWeilDatumO ψ S T χS χT om) {U : AddSubgroup (WO S T)}
    (hU : IsOpen (U : Set (WO S T))) (p₀ : GA D S × GA D T) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∀ᶠ p in 𝓝 p₀, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u φ = φ) → ∀ u ∈ K₀, u.map (infPart D) = 0 →
        heisO ψ S T u (om p φ) = om p φ := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous fun z : WO S T × (GA D S × GA D T) => actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 := by
    unfold actO
    simp only [inv_inv]
    exact (((GlobalTheory.RealWeil.continuous_mt T).2.comp (continuous_snd.comp continuous_snd)).matrix_mul continuous_fst).matrix_mul
      ((GlobalTheory.RealWeil.continuous_mt S).1.comp (continuous_fst.comp continuous_snd))
  have hev : ∀ᶠ z in 𝓝 ((0 : WO S T), p₀), actO S T z.2.1⁻¹ z.2.2⁻¹ z.1 ∈ U := by
    refine hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds ?_)
    show actO S T p₀.1⁻¹ p₀.2⁻¹ 0 ∈ U
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
    exact U.zero_mem
  rw [nhds_prod_eq] at hev
  obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 hev
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ ha
  refine ⟨K₀, h0, hK₀, hb.mono fun p hp φ hφ hl u hu hinf => ?_⟩
  obtain ⟨g, h⟩ := p
  have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
  have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) φ hφ
  rw [hl _ (hab (hsub hu) hp) hv, actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
  exact e.symm

theorem infPart_sub (hc : Chart θ σ) (w : WO S T) : (w - iotaW σ T S (piW θ T S w)).map (infPart D) = 0 := by
  generalize hu : w - iotaW σ T S (piW θ T S w) = u
  have hp : piW θ T S u = 0 := by
    rw [← hu, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
  ext i j
  exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j

theorem continuous_mov₂ (hθ : IsInfFam θ) :
    Continuous fun z : (GA D S × GA D T) × RW T S => mov θ z.1.1⁻¹ z.1.2⁻¹ z.2 := by
  refine continuous_pi fun τ => ?_
  unfold mov
  simp only [inv_inv]
  exact (((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt T).2.comp
    (continuous_snd.comp continuous_fst))).matrix_mul ((continuous_apply τ).comp continuous_snd)).matrix_mul
    ((GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt S).1.comp
      (continuous_fst.comp continuous_fst)))

theorem mov_bound (hθ : IsInfFam θ) (p₀ : GA D S × GA D T) {K : Set (RW T S)} (hK : IsCompact K) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ ∀ᶠ p in 𝓝 p₀, ∀ z ∈ K, ‖mov θ p.1⁻¹ p.2⁻¹ z‖ ≤ ρ := by
  have hc := continuous_mov₂ (S := S) (T := T) hθ
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn (hc.comp (Continuous.prodMk_right p₀)).continuousOn
  refine ⟨max 1 (κ + 1), le_max_left _ _, hK.eventually_forall_of_forall_eventually fun z hz => ?_⟩
  have : ∀ᶠ y in 𝓝 (p₀, z), ‖mov θ y.1.1⁻¹ y.1.2⁻¹ y.2‖ < κ + 1 :=
    hc.norm.continuousAt.eventually_lt continuousAt_const ((hκ z hz).trans_lt (lt_add_one κ))
  exact this.mono fun y hy => hy.le.trans (le_max_right _ _)

theorem deriv_bound (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) :
    ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ z : RW T S, ‖z‖ ≤ 1 → ∀ w, ‖dv θ σ S T z (om p f) w‖ ≤ C := by
  have hψ := hom.std
  have hθ := hc.inf
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, hK₀, hlev⟩ := level_near hom hU p₀
  obtain ⟨c, hc0, hcube⟩ := cube_bound hom hc b h0 hK₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := words_bound (dvL hc hψ S T) (fun w => (LinearMap.proj w).comp (thetaSub ψ S T).subtype)
    (fun m => theta_bounded hψ m.2) (1 + N) ⟨f, hf⟩
  obtain ⟨ρ, hρ1, hρ⟩ := mov_bound hθ p₀ ((isCompact_closedBall (0 : RW T S) 1).union (Set.finite_range b).isCompact)
  refine ⟨√(4 ^ N * (c * (C₁ * ρ ^ (1 + N)) ^ 2)), (hlev.and hρ).mono fun p hp z hz w => ?_⟩
  obtain ⟨g, h⟩ := p
  obtain ⟨hlev, hρ⟩ := hp
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ ρ) ∧ F = om (g, h) (wd l).1}
  have key := sobolev_iter N 1 (fun i r => iotaW σ T S (r • b i)) A (c * (C₁ * ρ ^ (1 + N)) ^ 2) w
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (dv θ σ S T z (om (g, h) f))
    ⟨[mov θ g⁻¹ h⁻¹ z], le_rfl, fun u hu => by
      rw [List.mem_singleton.1 hu]
      exact hρ z (Or.inl (mem_closedBall_zero_iff.2 hz)), dv_om hom hc g h z hf⟩
  · exact Real.le_sqrt_of_sq_le key
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        exact hρ _ (Or.inr ⟨i, rfl⟩)
    · rw [dv_om hom hc g h (b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    have hφ := (wd l).2
    have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ w) _ hφ
    rw [actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
    have hn : ∀ x, ‖om (g, h) (heisO ψ S T (actO S T g⁻¹ h⁻¹ w) (wd l).1) x‖ = ‖om (g, h) (wd l).1 (w + x)‖ := fun x => by
      rw [e, GlobalTheory.HeisOrtho.norm_heisO hψ.1, add_comm]
    have := hcube (g, h) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hφ (actO S T g⁻¹ h⁻¹ w)) (fun x hx => by
      have e2 := hlev _ hφ (fun u hu h0 => words_level hc hψ h0 l _ (hl u hu h0)) _ hx (infPart_sub hc x)
      rw [hn, hn]
      conv_rhs => rw [← e2, GlobalTheory.HeisOrtho.norm_heisO hψ.1, add_assoc, add_sub_cancel]) (C₁ * ρ ^ (1 + N)) (fun x => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
      exact hC₁ ρ hρ1 l h1 h2 _)
    simpa only [hn, zero_add] using this

theorem norm_heisO_sub_le (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) {C : ℝ}
    (hC : ∀ z : RW T S, ‖z‖ ≤ 1 → ∀ w, ‖dv θ σ S T z F w‖ ≤ C) (x : RW T S) (w : WO S T) :
    ‖heisO ψ S T (iotaW σ T S x) F w - F w‖ ≤ C * ‖x‖ := by
  have hz : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hx : ‖x‖ • ‖x‖⁻¹ • x = x := by
    rcases eq_or_ne x 0 with rfl | h
    · simp
    · rw [smul_inv_smul₀ (norm_ne_zero_iff.2 h)]
  obtain ⟨L, hL, e, e'⟩ := exists_line hc hψ (‖x‖⁻¹ • x)
  have h1 := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le (C := C)
    (fun s _ => (hasDerivAt_heisO hc.inf hψ hL hF w s).hasDerivWithinAt) (fun s _ => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1, ← e']
      exact hC _ hz _) (Set.mem_univ 0) (Set.mem_univ ‖x‖)
  rwa [L.map_zero, heisO_zero, e, hx, sub_zero, norm_norm] at h1

theorem continuous_om_oriented (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun q : (GA D S × GA D T) × WO S T => om q.1 f q.2 := by
  have hψ := hom.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : ContinuousSub (WA T S) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun ⟨p₀, w₀⟩ => ?_
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K₀, h0, -, hlev⟩ := level_near hom hU p₀
  obtain ⟨C, hC⟩ := deriv_bound hom hc hf p₀
  let x : WA T S → RW T S := fun w => piW θ T S (w - w₀)
  let u : WA T S → WA T S := fun w => (w - w₀) - iotaW σ T S (x w)
  have hx : Continuous x := (continuous_pi' hθ T S).comp (continuous_id.sub continuous_const)
  have hix : Continuous fun w => iotaW σ T S (x w) := (hc.continuous_iota T S).comp hx
  have hu : Continuous u := (continuous_id.sub continuous_const).sub hix
  have hx0 : x w₀ = 0 := by simp only [x, sub_self, map_zero]
  have hu0 : u w₀ = 0 := by simp only [u, hx0, sub_self, map_zero]
  let c : WA T S → ℂ := fun w => ψ (-symplOH S T (w₀ + iotaW σ T S (x w)) (u w)) * ψ (-symplOH S T w₀ (iotaW σ T S (x w)))
  have hcc : Continuous c :=
    (hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T (continuous_const.add hix) hu).neg).mul
      (hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T continuous_const hix).neg)
  have hc0 : c w₀ = 1 := by
    simp only [c, hx0, hu0, map_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have t1 : Tendsto (fun q : (GA D S × GA D T) × WO S T =>
      heisO ψ S T (iotaW σ T S (x q.2)) (om q.1 f) w₀ - om q.1 f w₀) (𝓝 (p₀, w₀)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun q => C * ‖x q.2‖) ?_ ?_
    · exact (continuous_fst.continuousAt.eventually hC).mono fun q hq =>
        norm_heisO_sub_le hc hψ (hom.om_pres _ f hf) hq _ _
    · have h3 : Continuous fun q : (GA D S × GA D T) × WO S T => C * ‖x q.2‖ :=
        continuous_const.mul (hx.comp continuous_snd).norm
      simpa only [hx0, norm_zero, mul_zero] using h3.tendsto (p₀, w₀)
  have t2 := ((hcc.comp continuous_snd).tendsto (p₀, w₀)).mul
    (t1.add (((hom.om_cont f hf w₀).comp continuous_fst).tendsto (p₀, w₀)))
  simp only [Function.comp_apply, hc0, one_mul, zero_add, sub_add_cancel] at t2
  refine t2.congr' ?_
  have ev : ∀ᶠ q : (GA D S × GA D T) × WO S T in 𝓝 (p₀, w₀), u q.2 ∈ K₀ :=
    (hu.comp continuous_snd).continuousAt.preimage_mem_nhds (by
      show K₀ ∈ 𝓝 (u w₀)
      rw [hu0]; exact h0)
  filter_upwards [ev, continuous_fst.continuousAt.eventually hlev] with q h1 h2
  have e := congrFun (h2 f hf hl _ h1 (infPart_sub hc _)) (w₀ + iotaW σ T S (x q.2))
  have e2 : w₀ + iotaW σ T S (x q.2) + u q.2 = q.2 := by simp only [u]; abel
  rw [heisO, e2] at e
  rw [heisO, ← e]
  simp only [c]
  have n1 : ∀ a, ψ (-a) * ψ a = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  linear_combination (om q.1 f q.2 * (ψ (-symplOH S T (w₀ + iotaW σ T S (x q.2)) (u q.2)) *
    ψ (symplOH S T (w₀ + iotaW σ T S (x q.2)) (u q.2)))) * n1 (symplOH S T w₀ (iotaW σ T S (x q.2))) +
    om q.1 f q.2 * n1 (symplOH S T (w₀ + iotaW σ T S (x q.2)) (u q.2))

open GlobalTheory.Mem.Th in

theorem continuous_om_pair (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' : IdC D}
    {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ha : admitted V W χ χ') (hw : IsWeilOn ψ V W χ χ' om)
    (Φ : ThS ψ V W) : Continuous fun q : (GA D V × GA D W) × WA V W => (om q.1 Φ).1 q.2 := by
  have small : ∀ {V W : HSp D} {χ χ' : IdC D} {om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)}, admitted V W χ χ' →
      V.rank < W.rank → IsWeilOn ψ V W χ χ' om → ∀ Φ : ThS ψ V W,
      Continuous fun q : (GA D V × GA D W) × WA V W => (om q.1 Φ).1 q.2 := by
    intro V W χ χ' om ha hr hw Φ
    obtain ⟨omO, hO, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO D ψ hψ V W χ χ' om ha hr hw
    have h := (continuous_om_oriented hO ((GlobalTheory.OrientedCoord.isThetaFunO_coord V W hr.le ψ _).2 (mem_ThS.1 Φ.2))).comp
      (continuous_fst.prodMk ((GlobalTheory.OrientedCoord.continuous_coord_symm V W).comp continuous_snd))
    refine h.congr fun q => (congrFun (e q.1 Φ) _).trans ?_
    exact congrArg (om q.1 Φ).1 ((GlobalTheory.OrientedCoord.coord V W).apply_symm_apply q.2)
  rcases ha.1.lt_or_gt with hr | hr
  · exact small ha hr hw Φ
  · obtain ⟨om', hw', e⟩ := GlobalTheory.Mem.WeilSwap.exists_isWeilOn_swap D ψ hψ V W χ χ' om ha.1 hw
    have h := (small ⟨ha.1.symm, ha.2.2.1, ha.2.1, ha.2.2.2.2, ha.2.2.2.1⟩ hr hw' (GlobalTheory.Mem.WeilSwap.trEquiv ψ ha.1 Φ)).comp
      ((continuous_swap.comp continuous_fst).prodMk
        (continuous_snd.matrix_transpose : Continuous fun q : (GA D V × GA D W) × WA V W => q.2.transpose))
    exact h.congr fun q => e q.1.1 q.1.2 Φ _ (fun _ => rfl) q.2

open GlobalTheory.Mem.Th in

theorem continuous_evS_om : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ Φ : X.Sch V W, Continuous fun q : (GA D V × GA D W) × WA V W => Wl.evS V W (Wl.om V W χ χ' q.1 Φ) q.2 := by
  intro D X T Wl V W χ χ' hne h1 h2 Φ
  have hc : ∀ χ, IsHC D (T.eChr χ) := fun χ => (Set.ext_iff.1 T.eChr_range _).1 ⟨χ, rfl⟩
  have hm : ∀ Φ, Wl.evS V W Φ ∈ ThS Wl.ψ V W := fun Φ =>
    mem_ThS.2 ((Set.ext_iff.1 (Wl.evS_range V W hne) _).1 ⟨Φ, rfl⟩)
  let E : X.Sch V W ≃ₗ[ℂ] ThS Wl.ψ V W := LinearEquiv.ofBijective ((Wl.evS V W).codRestrict _ hm)
    ⟨fun a b h => Wl.evS_inj V W (congrArg Subtype.val h), fun f => by
      obtain ⟨a, ha⟩ := (Set.ext_iff.1 (Wl.evS_range V W hne) f.1).2 (mem_ThS.1 f.2)
      exact ⟨a, Subtype.ext ha⟩⟩
  have hE : ∀ f : ThS Wl.ψ V W, Wl.evS V W (E.symm f) = f.1 := fun f => congrArg Subtype.val (E.apply_symm_apply f)
  let om : GA D V × GA D W →* Module.End ℂ (ThS Wl.ψ V W) := E.conjRingEquiv.toMonoidHom.comp (Wl.om V W χ χ')
  have hom : ∀ p f, (om p f).1 = Wl.evS V W (Wl.om V W χ χ' p (E.symm f)) := fun _ _ => rfl
  have hw : IsWeilOn Wl.ψ V W (T.eChr χ) (T.eChr χ') om := by
    refine ⟨fun g h w₀ f f' e => ?_, fun γ hγ γ' hγ' f => ?_, fun f w => ?_, fun μ 𝓕 hμ h𝓕 p f => ?_,
      fun e he g h hg hh x y hx hy => ?_⟩
    · rw [hom, hom]
      exact Wl.om_heis V W χ χ' hne h1 h2 g h w₀ _ _ (by rw [hE, hE, e])
    · rw [hom, Wl.om_aut V W χ χ' hne h1 h2 γ hγ γ' hγ', hE]
    · exact Wl.om_cont V W χ χ' hne h1 h2 _ w
    · rw [hom, Wl.om_unit V W χ χ' hne h1 h2 μ 𝓕 hμ h𝓕, hE]
    · obtain ⟨r, hr, k⟩ := Wl.om_split V W χ χ' hne h1 h2 e he g h hg hh x y hx hy
      refine ⟨r, hr, fun ℓ hℓ f => ?_⟩
      have := k (ℓ.comp E.toLinearMap) (fun u hu a a' e' => hℓ u hu (E a) (E a') e') (E.symm f)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      exact this
  have := continuous_om_pair Wl.ψ_std ⟨hne, hc χ, hc χ', h1, h2⟩ hw (E Φ)
  simpa only [hom, E.symm_apply_apply] using this

end GlobalTheory.ThetaJointCont

end
