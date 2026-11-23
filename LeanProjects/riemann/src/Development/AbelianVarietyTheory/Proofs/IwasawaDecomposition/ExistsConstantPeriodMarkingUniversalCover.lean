import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodsInFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open GlobalTheory.HolHom Filter

namespace GlobalTheory.ShFam.Hor.Mark

section Lin

theorem exists_addEquiv {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ C) (g : B →+ C)
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f.range = g.range) :
    ∃ T : A ≃+ B, ∀ a, g (T a) = f a := by
  refine ⟨((AddMonoidHom.ofInjective hf).trans (AddEquiv.addSubgroupCongr h)).trans
    (AddMonoidHom.ofInjective hg).symm, fun a => ?_⟩
  simp only [AddEquiv.trans_apply, AddMonoidHom.apply_ofInjective_symm]
  rfl

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {r : ℕ}

theorem real_indep {v : Fin r → W} (hv : LinearIndependent ℤ v)
    (hd : DiscreteTopology (Submodule.span ℤ (Set.range v))) : LinearIndependent ℝ v := by
  rw [linearIndependent_iff_card_eq_finrank_span, Real.finrank_eq_int_finrank_of_discrete hd]
  exact (finrank_span_eq_card hv).symm

theorem eventually_coord_eq {B : Type} [TopologicalSpace B] {b₀ : B} {lam : B → Fin r → W} {t : B → Fin r → ℤ}
    (hl : ContinuousAt lam b₀) (hi : LinearIndependent ℝ (lam b₀))
    (ht : ContinuousAt (fun b => ∑ m, t b m • lam b m) b₀) : ∀ᶠ b in 𝓝 b₀, t b = t b₀ := by
  let M : B → (Fin r → ℝ) →L[ℝ] W := fun b => ∑ m, (ContinuousLinearMap.proj m).smulRight (lam b m)
  have hM : ∀ b c, M b c = ∑ m, c m • lam b m := fun b c => by simp [M]
  have hMc : ContinuousAt M b₀ := by
    refine tendsto_finset_sum _ fun m _ => ?_
    exact ((ContinuousLinearMap.smulRightL ℝ (Fin r → ℝ) W (ContinuousLinearMap.proj m)).continuous.continuousAt.comp
      (continuousAt_pi.1 hl m))
  obtain ⟨K, hK0, hK⟩ := (M b₀).toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot'.2 fun c hc =>
    funext (Fintype.linearIndependent_iff.1 hi c ((hM b₀ c).symm.trans hc)))
  let c : B → Fin r → ℝ := fun b m => t b m
  have hc : ∀ b, ∑ m, t b m • lam b m = M b (c b) := fun b => by simp [hM, c, Int.cast_smul_eq_zsmul]
  have h1 : Tendsto (fun b => (K : ℝ) * ‖M b₀ - M b‖) (𝓝 b₀) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := M b₀)).sub hMc).norm.const_mul (K : ℝ)
    simpa using this
  have h2 : Tendsto (fun b => (K : ℝ) * ‖M b (c b - c b₀)‖) (𝓝 b₀) (𝓝 0) := by
    have := (ht.sub (hMc.clm_apply (continuousAt_const (y := c b₀)))).tendsto.norm.const_mul (K : ℝ)
    simpa [hc] using this
  filter_upwards [h1.eventually (gt_mem_nhds one_half_pos), h2.eventually (gt_mem_nhds one_half_pos)] with b e1 e2
  have e3 : ‖c b - c b₀‖ ≤ K * ‖M b₀ (c b - c b₀)‖ := ZeroHomClass.bound_of_antilipschitz _ hK _
  have e4 : ‖M b₀ (c b - c b₀)‖ ≤ ‖M b (c b - c b₀)‖ + ‖M b₀ - M b‖ * ‖c b - c b₀‖ := by
    refine le_trans ?_ (add_le_add le_rfl ((M b₀ - M b).le_opNorm _))
    refine le_trans (le_of_eq ?_) (norm_add_le _ _)
    simp
  have e5 : ‖c b - c b₀‖ < 1 := by
    have := mul_le_mul_of_nonneg_left e4 K.2
    nlinarith [norm_nonneg (c b - c b₀)]
  funext m
  have e6 := (norm_le_pi_norm (c b - c b₀) m).trans_lt e5
  rw [Real.norm_eq_abs] at e6
  have e7 : |t b m - t b₀ m| < 1 := by
    have : ((|t b m - t b₀ m| : ℤ) : ℝ) < 1 := by simpa [c] using e6
    exact_mod_cast this
  exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 e7)

end Lin

section Pull

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  {y : Sp ℂ ⟶ S'} {x : Sp ℂ ⟶ S} {g g' : ℕ}

def IsEx {y : Sp ℂ ⟶ S} (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) : Prop :=
  (∀ z w, e (z + w) = e z * e w) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left

theorem exists_up (h : IsGrpPullback G' G f φ) (hx : y ≫ f = x) (p : Over.mk x ⟶ G) :
    ∃ q : Over.mk y ⟶ G', q.left ≫ φ = p.left :=
  ⟨Over.homMk (h.1.lift p.left y ((Over.w p).trans hx.symm)) (h.1.lift_snd _ _ _), h.1.lift_fst _ _ _⟩

theorem up_ext (h : IsGrpPullback G' G f φ) {T : Over S'} {p q : T ⟶ G'} (e : p.left ≫ φ = q.left ≫ φ) : p = q :=
  Over.OverMorphism.ext (h.1.hom_ext e ((Over.w p).trans (Over.w q).symm))

theorem up_mul (h : IsGrpPullback G' G f φ) (hx : y ≫ f = x) {p q : Over.mk x ⟶ G} {p' q' : Over.mk y ⟶ G'}
    (hp : p'.left ≫ φ = p.left) (hq : q'.left ≫ φ = q.left) : (p' * q').left ≫ φ = (p * q).left := by
  subst hx
  exact (h.2 (Over.mk y) p' q' p q hp.symm hq.symm).symm

theorem up_eq_one (h : IsGrpPullback G' G f φ) (hx : y ≫ f = x) {p : Over.mk x ⟶ G} {p' : Over.mk y ⟶ G'}
    (hp : p'.left ≫ φ = p.left) : p' = 1 ↔ p = 1 := by
  rw [← mul_eq_left (a := p'), ← mul_eq_left (a := p)]
  exact ⟨fun e => Over.OverMorphism.ext (by rw [← up_mul h hx hp hp, e, hp]),
    fun e => up_ext h (by rw [up_mul h hx hp hp, e, hp])⟩

theorem up_deriv (h : IsGrpPullback G' G f φ) {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)}
    {e' : (Fin g → ℂ) → (Over.mk y ⟶ G')} (he : ∀ z, (e' z).left ≫ φ = e z)
    (hol : IsHolTo Set.univ fun z => (e' z).left) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ G'.left}
    (hv : v ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) :
    IsDerivAt0 e w (v ≫ φ) ↔ IsDerivAt0 (fun z => (e' z).left) w v := by
  obtain rfl : (fun z => (e' z).left ≫ φ) = e := funext he
  simp only [isDerivAt0_iff]
  refine ⟨fun H => ?_, fun H => H.comp φ⟩
  obtain ⟨u, hu⟩ := (holAt_of_isHolTo hol (Set.mem_univ 0)).exists_isDerivAt w
  obtain rfl : u = v := h.1.hom_ext ((hu.comp φ).unique H) (hu.over.trans hv.symm)
  exact hu

theorem IsEx.up (h : IsGrpPullback G' G f φ) (hx : y ≫ f = x) {e : (Fin g → ℂ) → (Over.mk x ⟶ G)} (H : IsEx e)
    {e' : (Fin g → ℂ) → (Over.mk y ⟶ G')} (he : ∀ z, (e' z).left ≫ φ = (e z).left) : IsEx e' := by
  have hol : IsHolTo Set.univ fun z => (e' z).left :=
    isHolTo_of_holAt isOpen_univ fun z _ => holAt_of_isPullback h.1
      (by simpa only [he] using holAt_of_isHolTo H.2.1 (Set.mem_univ z))
      (by simpa only [show ∀ t, (e' t).left ≫ G'.hom = y from fun t => Over.w (e' t)] using holAt_const y z)
  refine ⟨fun z w => up_ext h (by rw [up_mul h hx (he z) (he w), he, H.1]), hol, fun v hv => ?_⟩
  have hw : v.left ≫ G'.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y := Over.w v
  simp only [← up_deriv h he hol hw]
  refine H.2.2 (Over.homMk (v.left ≫ φ) ?_) ?_
  · rw [Category.assoc, h.1.w, ← Category.assoc, hw, Category.assoc, hx]; rfl
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) hv).trans (he 0))

theorem HolAt.congr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {y y' : V → (Sp ℂ ⟶ X)}
    {b : V} (h : HolAt y b) (e : ∀ᶠ t in 𝓝 b, y' t = y t) : HolAt y' b := fun U hU => by
  have := h U (e.self_of_nhds ▸ hU)
  refine ⟨?_, fun f => (this.2 f).congr_of_eventuallyEq (e.mono fun t ht => by simp only [ht])⟩
  filter_upwards [e, this.1] with t h1 h2 using h1 ▸ h2

theorem exists_up_family (h : IsGrpPullback G' G f φ) {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {B : Set V} {y : V → (Sp ℂ ⟶ S')} {x : V → (Sp ℂ ⟶ S)}
    (hx : ∀ b ∈ B, y b ≫ f = x b) (holy : ∀ b ∈ B, HolAt y b) {e : ∀ b, W → (Over.mk (x b) ⟶ G)}
    (hol : IsHolTo (B ×ˢ Set.univ) fun bz : V × W => (e bz.1 bz.2).left) :
    ∃ e' : ∀ b, W → (Over.mk (y b) ⟶ G'), (∀ b ∈ B, ∀ z, (e' b z).left ≫ φ = (e b z).left) ∧
      IsHolTo (B ×ˢ Set.univ) fun bz : V × W => (e' bz.1 bz.2).left := by
  have H : ∀ b z, ∃ q : Over.mk (y b) ⟶ G', b ∈ B → q.left ≫ φ = (e b z).left := fun b z => by
    by_cases hb : b ∈ B
    · exact (exists_up h (hx b hb) _).imp fun _ h _ => h
    · exact ⟨1, fun h => (hb h).elim⟩
  choose e' he using H
  have hB := isOpen_of_isHolTo hol
  refine ⟨e', fun b hb z => he b z hb, isHolTo_of_holAt hB fun bz hbz => holAt_of_isPullback h.1
    (HolAt.congr (holAt_of_isHolTo hol hbz) (eventually_of_mem (hB.mem_nhds hbz) fun t ht => he _ _ ht.1)) ?_⟩
  simp only [show ∀ b z, (e' b z).left ≫ G'.hom = y b from fun b z => Over.w (e' b z)]
  exact HolAt.precomp (c := y) (k := fun bz : V × W => bz.1) (holy _ hbz.1) differentiableAt_fst

theorem IsEx.exists_equiv {e : (Fin g → ℂ) → (Over.mk x ⟶ G)} {e' : (Fin g' → ℂ) → (Over.mk x ⟶ G)} (H : IsEx e)
    (H' : IsEx e') : ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), ∀ z, e z = e' (L z) := by
  obtain ⟨L, hL, -⟩ := existsUnique_linear H.1 H'.1 H.2.1 H'.2.1 H'.2.2
  obtain ⟨L', hL', -⟩ := existsUnique_linear H'.1 H.1 H'.2.1 H.2.1 H.2.2
  exact ⟨LinearEquiv.ofLinear L L'
    ((existsUnique_linear H'.1 H'.1 H'.2.1 H'.2.1 H'.2.2).unique (fun z => (hL' z).trans (hL _)) fun _ => rfl)
    ((existsUnique_linear H.1 H.1 H.2.1 H.2.1 H.2.2).unique (fun z => (hL z).trans (hL' _)) fun _ => rfl), hL⟩

theorem deriv_comp_equiv {X : Scheme.{0}} {e : (Fin g' → ℂ) → (Sp ℂ ⟶ X)} (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : IsDerivAt0 (fun z => e (L z)) w v ↔ IsDerivAt0 e (L w) v := by
  have key : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (L z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (L w) := fun U f => by
    have := L.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    rw [map_zero] at this
    exact DFunLike.congr_fun this w
  simp only [IsDerivAt0, key, map_zero]

end Pull

section Dom

variable {n k : ℕ}

theorem convex_logDom : Convex ℝ (logDom n k) := by
  have : logDom n k = Set.univ.pi fun j : Fin n =>
      if (j : ℕ) < k then {z : ℂ | z.re < 0} else Metric.ball 0 1 := by
    ext s
    refine forall_congr' fun j => ?_
    split_ifs <;> simp [*]
  rw [this]
  refine convex_pi fun j _ => ?_
  split_ifs
  exacts [convex_halfSpace_re_lt 0, convex_ball _ _]

theorem isOpen_logDom : IsOpen (logDom n k) := by
  rw [logDom, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun j => ?_
  split_ifs
  exacts [isOpen_lt (by fun_prop) continuous_const, isOpen_lt (by fun_prop) continuous_const]

theorem nonempty_logDom : (logDom n k).Nonempty :=
  ⟨fun j => if (j : ℕ) < k then -1 else 0, fun j => by split_ifs with h <;> simp [h]⟩

theorem differentiable_logExp : Differentiable ℂ (logExp k : (Fin n → ℂ) → Fin n → ℂ) := by
  refine differentiable_pi.2 fun j => ?_
  unfold logExp
  split_ifs <;> fun_prop

theorem logExp_mem {s : Fin n → ℂ} (hs : s ∈ logDom n k) : logExp k s ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro j
  have := hs j
  unfold logExp
  split_ifs at this ⊢
  · rwa [Complex.norm_exp, Real.exp_lt_one_iff]
  · exact this

end Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} {Fu : Fam Xo c σ e} {n g' r k : ℕ}
  {ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)} {ex : ExpMaps Z σ g'}
  {lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ} {ρ : Fin g' → Fin r → ℂ}

theorem isEx_chart (h : IsExpChart ch ex) {x : CxPts (genStr Z) σ} (hx : x ∈ ch.source) : IsEx (ex x) := by
  obtain ⟨-, -, -, hadd, hol, hd⟩ := h
  refine ⟨hadd x hx, isHolTo_of_holAt isOpen_univ fun z _ => ?_, fun v hv => (hd x hx).2 v.left ⟨Over.w v, ?_⟩⟩
  · have := (holAt_of_isHolTo hol (z := (ch x, z)) ⟨ch.map_source hx, trivial⟩).precomp (k := fun z => (ch x, z))
      (by fun_prop)
    have e : ∀ x', x' = x → (fun t => (ex x' t).left) = fun t => (ex x t).left := by rintro _ rfl; rfl
    exact e _ (ch.left_inv hx) ▸ this
  · rw [hv, map_zero_eq_one (hadd x hx)]

variable (Fu ex) in

def Match (x : CxPts (genStr Z) σ) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c)
    (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)) : Prop :=
  (∀ z, Fu.ex i P z = 1 ↔ ex x (L z) = 1) ∧ ∀ (w) (v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left),
    v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y →
    (IsDerivAt0 (fun w => (Fu.ex i P w).left) w (v ≫ Z.m0.toSABMap.φ) ↔
      IsDerivAt0 (fun w => (ex x w).left) (L w) (v ≫ Z.m.φ))

section Point

variable {x : CxPts (genStr Z) σ} {i : Fin Fu.n} {P : (Fu.Di i).La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.XF c}

theorem exists_match_of_lifts (h : IsExpChart ch ex) (hx : x ∈ ch.source)
    (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P) (hu : y ≫ pullback.fst _ _ = Fu.u i P)
    (hy : y ≫ Z.jQ = x.1) {e₁ : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G)} {e₂ : (Fin g' → ℂ) → (Over.mk y ⟶ Z.oF.t.G)}
    (h₁ : ∀ z, (e₁ z).left ≫ Z.m0.toSABMap.φ = (Fu.ex i P z).left) (h₂ : ∀ z, (e₂ z).left ≫ Z.m.φ = (ex x z).left) :
    IsEx e₂ ∧ ∃ L, Match Fu ex x i P y L ∧ ∀ z, e₁ z = e₂ (L z) := by
  have hy' : y ≫ Z.jQ ≫ pullback.fst _ _ = x.1 ≫ genι Z := by rw [← Category.assoc, hy]
  have H₁ : IsEx e₁ := IsEx.up Z.m0.toSABMap.cart hu ⟨Fu.ex_add i P hP, isHolTo_ex Fu i hP, (Fu.ex_diff i P hP).2⟩ h₁
  have H₂ : IsEx e₂ := (isEx_chart h hx).up Z.m.cart hy' h₂
  obtain ⟨L, hL⟩ := H₁.exists_equiv H₂
  refine ⟨H₂, L, ⟨fun z => ?_, fun w v hv => ?_⟩, hL⟩
  · rw [← up_eq_one Z.m0.toSABMap.cart hu (h₁ z), ← up_eq_one Z.m.cart hy' (h₂ _), hL]
  · rw [up_deriv Z.m0.toSABMap.cart h₁ H₁.2.1 hv, up_deriv Z.m.cart h₂ H₂.2.1 hv,
      ← deriv_comp_equiv (e := fun z => (e₂ z).left)]
    simp only [hL]

theorem dirs_surjective (Fu : Fam Xo c σ e) (h : IsExpChart ch ex) (a : CxFr Z σ) (hx : a.1 ∈ ch.source)
    (hi : Inner a.1) {W : Letter Dw → Fin g' → ℂ} (hW : Dirs a (fun w => (ex a.1 w).left) W) :
    LinearMap.range (Fintype.linearCombination ℂ W) = ⊤ := by
  obtain ⟨i, Q, P, W', y, hP, hu, hy, hv, hQ⟩ := T.exists_periods_in_frame_off_boundary E H Dw l Xo c O β Z σ g e Fu a hi
  choose e₁ h₁ using fun z => exists_up Z.m0.toSABMap.cart hu (Fu.ex i P z)
  choose e₂ h₂ using fun z => exists_up Z.m.cart (x := a.1.1 ≫ genι Z) (y := y) (by rw [← Category.assoc, hy]) (ex a.1 z)
  obtain ⟨-, L, hL, -⟩ := exists_match_of_lifts h hx hP hu hy h₁ h₂
  have hWW : ∀ z, L (W' z) = W z := fun z => by
    obtain ⟨v, h1, h2, h3⟩ := hv z
    exact ((h.2.2.2.2.2 a.1 hx).2 _ (a.2.tan z.1 z.2)).unique (h2 ▸ (hL.2 _ v h1).1 h3) (hW z)
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨w, rfl⟩ := L.surjective w
  have hw : w ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1.ge trivial
  refine (Submodule.span_le (p := ((LinearMap.range (Fintype.linearCombination ℂ W)).comap
    L.toLinearMap).restrictScalars ℝ)).2 ?_ hw
  rintro _ ⟨v, rfl⟩
  exact ⟨Q v, by simp [Fintype.linearCombination_apply, hQ, hWW]⟩

theorem exists_per (h : IsExpChart ch ex) (a : CxFr Z σ) (hx : a.1 ∈ ch.source) (hi : Inner a.1)
    (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P) (hu : y ≫ pullback.fst _ _ = Fu.u i P)
    (hy : y ≫ Z.jQ = a.1.1) {L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)} (hL : Match Fu ex a.1 i P y L)
    {W : Letter Dw → Fin g' → ℂ} (hW : Dirs a (fun w => (ex a.1 w).left) W) :
    ∃ Q, Per Fu a i Q ∧ ∀ v, ∑ z, Q v z • W z = L (P v) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective _ (dirs_surjective Fu h a hx hi hW)
  have hs' : ∀ w, ∑ z, s w z • W z = w := fun w => by
    simpa [Fintype.linearCombination_apply] using DFunLike.congr_fun hs w
  refine ⟨(s ∘ₗ L.toLinearMap).toAddMonoidHom.comp P, ⟨P, fun z => L.symm (W z), y, hP, hu, hy, fun z => ?_,
    fun v => L.injective ?_⟩, fun v => hs' _⟩
  · have hw : a.2.v z.1 z.2 ≫ Z.t.G.hom =
        (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) ≫ Z.jQ ≫ pullback.fst _ _ := by
      rw [(a.2.tan z.1 z.2).1, ← hy]
      simp only [Category.assoc]
    refine ⟨Z.m.cart.1.lift _ _ hw, Z.m.cart.1.lift_snd _ _ _, Z.m.cart.1.lift_fst _ _ _,
      (hL.2 _ _ (Z.m.cart.1.lift_snd _ _ _)).2 ?_⟩
    rw [Z.m.cart.1.lift_fst, L.apply_symm_apply]
    exact hW z
  · simpa using (hs' _).symm

theorem exists_marking (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    {L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)} (hL : Match Fu ex x i P y L) {b : Fin r → Fin g' → ℂ}
    (hb : LinearIndependent ℤ b) (hk : ∀ w, ex x w = 1 ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j) :
    LinearIndependent ℝ b ∧ ∃ T : (Fu.Di i).La ≃+ (Fin r → ℤ), ∀ v, ∑ m, T v m • b m = L (P v) := by
  have key : ∀ w, L.symm w ∈ P.range ↔ w ∈ LinearMap.range (Fintype.linearCombination ℤ b) := fun w => by
    rw [← Fu.ex_ker i P hP, hL.1, L.apply_symm_apply, hk]
    simp only [LinearMap.mem_range, Fintype.linearCombination_apply, eq_comm]
  refine ⟨real_indep hb ?_, exists_addEquiv (L.toLinearMap.toAddMonoidHom.comp P)
    (Fintype.linearCombination ℤ b).toAddMonoidHom (L.injective.comp hP.2.1)
    hb.fintypeLinearCombination_injective (AddSubgroup.ext fun w => ?_)⟩
  · have := hP.2.2.1
    rw [← Fintype.range_linearCombination]
    exact DiscreteTopology.of_continuous_injective (β := P.range) (f := fun w => ⟨L.symm w.1, (key _).2 w.2⟩)
      ((L.symm.toContinuousLinearEquiv.continuous.comp continuous_subtype_val).subtype_mk _)
      fun w w' h => Subtype.ext (L.symm.injective (congrArg Subtype.val h))
  · refine Iff.trans ?_ (key w)
    exact exists_congr fun v => L.eq_symm_apply.symm

end Point

theorem isHolTo_of_open {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} (i : X ⟶ Y)
    [IsOpenImmersion i] {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [valAt'_eq_valR, valR_comp] at this
    exact this
  exact key U (i.preimage_image_eq U) f

theorem exists_under {x : CxPts (genStr Z) σ} (hx : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  have := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact not_not.1 hx

theorem pt_mem (h : IsLogChart k ch ex lam ρ) {s : Fin n → ℂ} (hs : s ∈ logDom n k) :
    logExp k s ∈ ch.target ∧ ch.symm (logExp k s) ∈ ch.source ∧ Inner (ch.symm (logExp k s)) := by
  have ht : logExp k s ∈ ch.target := h.1.1 ▸ logExp_mem hs
  refine ⟨ht, ch.map_target ht, (h.2.1 _ (ch.map_target ht)).2 fun j hj => ?_⟩
  rw [ch.right_inv ht, logExp, if_pos hj]
  exact Complex.exp_ne_zero _

theorem isHolTo_chart (h : IsLogChart k ch ex lam ρ) {B : Set (Fin n → ℂ)} (hB : IsOpen B) (hBD : B ⊆ logDom n k) :
    IsHolTo (B ×ˢ Set.univ) fun t : (Fin n → ℂ) × (Fin g' → ℂ) => (ex (ch.symm (logExp k t.1)) t.2).left := by
  have hx : IsHolTo (ch.target ×ˢ (Set.univ : Set (Fin g' → ℂ))) (fun zw => (ex (ch.symm zw.1) zw.2).left) :=
    h.1.2.2.2.2.1
  refine isHolTo_of_holAt (hB.prod isOpen_univ) fun bz hbz => ?_
  have d : DifferentiableAt ℂ (fun t : (Fin n → ℂ) × (Fin g' → ℂ) => (logExp k t.1, t.2)) bz :=
    ((differentiable_logExp _).comp bz differentiableAt_fst).prodMk differentiableAt_snd
  have hh := holAt_of_isHolTo hx (z := (logExp k bz.1, bz.2)) ⟨(pt_mem h (hBD hbz.1)).1, trivial⟩
  exact HolAt.precomp (c := fun zw : (Fin n → ℂ) × (Fin g' → ℂ) => (ex (ch.symm zw.1) zw.2).left)
    (k := fun t : (Fin n → ℂ) × (Fin g' → ℂ) => (logExp k t.1, t.2)) (z := bz) hh d

variable (Fu ch ex lam k) in

def Marks (s : Fin n → ℂ) (i : Fin Fu.n) (T : (Fu.Di i).La ≃+ (Fin r → ℤ)) : Prop :=
  ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W →
    ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧
      IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T v m • lam s m

theorem exists_local (Fu : Fam Xo c σ e) (h : IsLogChart k ch ex lam ρ) {s₁ : Fin n → ℂ} (hs₁ : s₁ ∈ logDom n k) :
    ∃ i T, ∀ᶠ s in 𝓝 s₁, Marks Fu k ch ex lam s i T := by
  have := Z.jQ_open
  obtain ⟨y₁, -⟩ := exists_under (pt_mem h hs₁).2.2
  have hy : ∀ s, ∃ y : Sp ℂ ⟶ Xo.XF c, s ∈ logDom n k → y ≫ Z.jQ = (ch.symm (logExp k s)).1 := fun s => by
    by_cases hs : s ∈ logDom n k
    · exact (exists_under (pt_mem h hs).2.2).imp fun _ h _ => h
    · exact ⟨y₁, fun h => (hs h).elim⟩
  choose y hy using hy
  have holy : IsHolTo (logDom n k) y := isHolTo_of_open Z.jQ (isHolTo_of_holAt isOpen_logDom fun s hs =>
    HolAt.congr ((holAt_of_isHolTo h.1.2.2.1 (pt_mem h hs).1).precomp (differentiable_logExp s))
      (eventually_of_mem (isOpen_logDom.mem_nhds hs) hy))
  obtain ⟨B, i, P, hB, hB₁, hBD, hP, hu⟩ := Fu.lift n (logDom n k) (fun s => y s ≫ pullback.fst _ _) isOpen_logDom
    (fun s hs => by
      rw [Category.assoc, pullback.condition, ← Z.jQ_over, Category.assoc, ← Category.assoc (y s), hy s hs,
        ← Category.assoc, (ch.symm (logExp k s)).2, ← Spec.map_comp]
      rfl)
    (isHolTo_of_holAt isOpen_logDom fun s hs => (holAt_of_isHolTo holy hs).comp _) s₁ hs₁
  have hu' : ∀ s ∈ B, y s ≫ pullback.fst _ _ = Fu.u i (P s) := fun s hs => (hu s hs).symm
  have hy' : ∀ s ∈ B, y s ≫ Z.jQ ≫ pullback.fst _ _ = (ch.symm (logExp k s)).1 ≫ genι Z := fun s hs => by
    rw [← Category.assoc, hy s (hBD hs)]
  have holy' := fun s (hs : s ∈ B) => holAt_of_isHolTo holy (hBD hs)
  obtain ⟨e₁, h₁, hol₁⟩ := exists_up_family Z.m0.toSABMap.cart hu' holy' (e := fun s => Fu.ex i (P s))
    (Fu.hol i n B P hB hP).2
  obtain ⟨e₂, h₂, hol₂⟩ := exists_up_family Z.m.cart hy' holy' (e := fun s => ex (ch.symm (logExp k s)))
    (isHolTo_chart h hB hBD)
  have hM := fun s (hs : s ∈ B) => exists_match_of_lifts h.1 (pt_mem h (hBD hs)).2.1 (hP.1 s hs) (hu' s hs)
    (hy s (hBD hs)) (h₁ s hs) (h₂ s hs)
  obtain ⟨-, L₁, hL₁, -⟩ := hM s₁ hB₁
  have hL : ∀ s, ∃ L, s ∈ B → Match Fu ex (ch.symm (logExp k s)) i (P s) (y s) L ∧ ∀ z, e₁ s z = e₂ s (L z) :=
    fun s => by
      by_cases hs : s ∈ B
      · exact (hM s hs).2.imp fun _ h _ => h
      · exact ⟨L₁, fun h => (hs h).elim⟩
  choose L hL using hL
  have hm := fun s (hs : s ∈ B) => exists_marking (hP.1 s hs) (hL s hs).1 (h.2.2.2.1 s (hBD hs)).1
    (h.2.2.2.1 s (hBD hs)).2.1
  obtain ⟨hi, T₁, -⟩ := hm s₁ hB₁
  have hT : ∀ s, ∃ T : (Fu.Di i).La ≃+ (Fin r → ℤ), s ∈ B → ∀ v, ∑ m, T v m • lam s m = L s (P s v) := fun s => by
    by_cases hs : s ∈ B
    · exact (hm s hs).2.imp fun _ h _ => h
    · exact ⟨T₁, fun h => (hs h).elim⟩
  choose T hT using hT
  have hLc := ((differentiableOn_linear hol₁ hol₂ (fun s hs => (hM s hs).1.2.2) (h := fun s => (L s).toLinearMap)
    fun s hs => (hL s hs).2).continuousOn).continuousAt (hB.mem_nhds hB₁)
  have hev : ∀ v, ∀ᶠ s in 𝓝 s₁, T s v = T s₁ v := fun v =>
    eventually_coord_eq (t := fun s => T s v) (h.2.2.1.continuousAt (isOpen_logDom.mem_nhds hs₁)) hi
      ((hLc.clm_apply ((hP.2 v).continuousOn.continuousAt (hB.mem_nhds hB₁))).congr
        (eventually_of_mem (hB.mem_nhds hB₁) fun s hs => (hT s hs v).symm))
  refine ⟨i, T s₁, ?_⟩
  filter_upwards [hB.mem_nhds hB₁, eventually_all.2 fun m : Fin r => hev ((T s₁).symm (Pi.single m 1))]
    with s hs hsT a W ha hW
  have hTT : ∀ v, T s v = T s₁ v := fun v => by
    obtain ⟨w, rfl⟩ := (T s₁).symm.surjective v
    have : ((T s₁).symm.trans (T s)).toAddMonoidHom = AddMonoidHom.id _ :=
      AddMonoidHom.functions_ext' _ _ _ fun m => AddMonoidHom.ext_int (by simpa using hsT m)
    simpa using DFunLike.congr_fun this w
  obtain ⟨Q, hQ, hQ'⟩ := exists_per h.1 a (ha ▸ (pt_mem h (hBD hs)).2.1) (ha ▸ (pt_mem h (hBD hs)).2.2) (hP.1 s hs)
    (hu' s hs) (ha ▸ hy s (hBD hs)) (ha ▸ (hL s hs).1) hW
  exact ⟨Q, LinearEquiv.refl _ _, hQ, fun _ _ => rfl, fun v => by
    rw [LinearEquiv.refl_apply, hQ', ← hT s hs, hTT]⟩

theorem Marks.trans (h : IsLogChart k ch ex lam ρ) {s s' : Fin n → ℂ} (hs : s ∈ logDom n k) {i j : Fin Fu.n}
    {T : (Fu.Di i).La ≃+ (Fin r → ℤ)} {T' : (Fu.Di j).La ≃+ (Fin r → ℤ)} (h₁ : Marks Fu k ch ex lam s i T)
    (h₂ : Marks Fu k ch ex lam s j T') (h₃ : Marks Fu k ch ex lam s' j T') : Marks Fu k ch ex lam s' i T := by
  obtain ⟨f⟩ := EigLoc.exists_eigFrame E H Dw l Xo c O β Z ℂ σ _ (ch.symm (logExp k s)).2
  choose W hW _ using fun z : Letter Dw => (h.1.2.2.2.2.2 _ (pt_mem h hs).2.1).2 _ (f.tan z.1 z.2)
  obtain ⟨Q, u, hQ, hu, e₁⟩ := h₁ ⟨_, f⟩ W rfl hW
  obtain ⟨Q', u', hQ', hu', e₂⟩ := h₂ ⟨_, f⟩ W rfl hW
  have cmp := GlobalTheory.T.two_markings_differ_by_level_isometry E H Dw l Xo c O β Z σ g e Fu ⟨_, f⟩
  obtain rfl : i = j := cmp.1 _ _ _ _ hQ hQ'
  obtain ⟨d, hd, -, e₃⟩ := cmp.2 _ _ _ hQ hQ'
  have hT : ∀ v, T v = T' (u'.symm (d (u v))) := fun v =>
    (h.2.2.2.1 s hs).1.fintypeLinearCombination_injective (by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, ← e₁, ← e₂, u'.apply_symm_apply, e₃])
  intro a W' ha hW'
  obtain ⟨R, t, hR, ht, e₄⟩ := h₃ a W' ha hW'
  refine ⟨R, ((u.trans d).trans u'.symm).trans t, hR, fun v w => ?_, fun v => ?_⟩
  · simp only [LinearEquiv.trans_apply]
    rw [ht, ← hu', u'.apply_symm_apply, u'.apply_symm_apply, hd, hu]
  · rw [hT]
    exact e₄ _

theorem exists_marking_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (n g' r k : ℕ) (ch : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g') (lam : (Fin n → ℂ) → Fin r → Fin g' → ℂ) (ρ : Fin g' → Fin r → ℂ), IsLogChart k ch ex lam ρ → ∃ (i : Fin Fu.n) (T₀ : (Fu.Di i).La ≃+ (Fin r → ℤ)), ∀ s ∈ logDom n k, ∀ (a : CxFr Z σ) (W : Letter Dw → Fin g' → ℂ), a.1 = ch.symm (logExp k s) → Dirs a (fun w => (ex a.1 w).left) W → ∃ (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La), Per Fu a i Q ∧ IsIsom (Fu.Di i) gm ∧ ∀ v, ∑ z, Q (gm v) z • W z = ∑ m, T₀ v m • lam s m := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu n g' r k ch ex lam ρ h
  obtain ⟨s₀, hs₀⟩ := nonempty_logDom (n := n) (k := k)
  obtain ⟨i, T₀, h₀⟩ := exists_local Fu h hs₀
  refine ⟨i, T₀, fun s hs => convex_logDom.isPreconnected.induction₂'
    (fun s s' => Marks Fu k ch ex lam s i T₀ → Marks Fu k ch ex lam s' i T₀) (fun x hx => ?_)
    (fun _ _ _ _ _ _ h1 h2 => h2 ∘ h1) hs₀ hs h₀.self_of_nhds⟩
  obtain ⟨j, T₁, h₁⟩ := exists_local Fu h hx
  filter_upwards [self_mem_nhdsWithin, h₁.filter_mono nhdsWithin_le_nhds] with y hy h₂
  exact ⟨fun h₃ => h₃.trans h hx h₁.self_of_nhds h₂, fun h₃ => h₃.trans h hy h₂ h₁.self_of_nhds⟩

end GlobalTheory.ShFam.Hor.Mark
