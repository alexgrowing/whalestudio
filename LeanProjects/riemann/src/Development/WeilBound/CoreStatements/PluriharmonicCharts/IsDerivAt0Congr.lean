import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ChartPeriods
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsIsDerivAt0Loc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open scoped Matrix ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

theorem valAt_cst {X : Scheme.{0}} {Ω O R : Type} [Field Ω] [CommRing O] [CommRing R] [IsLocalRing R]
    {ξ : Sp Ω ⟶ X} {z : Sp R ⟶ X} (h : genPt ξ ⤳ centre z) (q : X ⟶ Sp O) {α : O →+* Ω} {β : O →+* R}
    (hα : ξ ≫ q = spMap α) (hβ : z ≫ q = spMap β) (a : O) : ValAt ξ z (α a) (β a) := by
  let gm := Spec.preimage (X.fromSpecStalk (centre z) ≫ q)
  have hgm : Spec.map gm = X.fromSpecStalk (centre z) ≫ q := Spec.map_preimage _
  refine ⟨h, gm.hom a, ?_, ?_⟩
  · have e : Spec.map (CommRingCat.ofHom ((genMap ξ (⟨centre z, h⟩ : Cpt ξ)).comp gm.hom)) = spMap α := by
      calc Spec.map (CommRingCat.ofHom ((genMap ξ (⟨centre z, h⟩ : Cpt ξ)).comp gm.hom))
          = Spec.map (CommRingCat.ofHom (genMap ξ (⟨centre z, h⟩ : Cpt ξ))) ≫ Spec.map gm := Spec.map_comp gm _
        _ = ξ ≫ q := by
          rw [hgm, ← Category.assoc]
          exact congrArg (· ≫ q) (LieTangent.spec_genMap ξ _)
        _ = spMap α := hα
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    exact DFunLike.congr_fun this a
  · have e : Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo z).hom.comp gm.hom)) = spMap β := by
      calc Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo z).hom.comp gm.hom))
          = Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo z).hom) ≫ Spec.map gm := Spec.map_comp gm _
        _ = z ≫ q := by
          erw [hgm, ← Category.assoc]
          exact congrArg (· ≫ q) (LieTangent.spec_centre z)
        _ = spMap β := hβ
    have := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    exact DFunLike.congr_fun this a

theorem lieValAt_end {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {V : Type} [AddCommGroup V] [Module Ω V] {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f] {A : V →ₗ[Ω] V} (hA : M.IsDiffOf f A) {e : V}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hc, v, ⟨h1, h2⟩, h3⟩ := h
  refine ⟨hc, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · unfold IsTanAt at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  · rw [hA e, Over.comp_left, Over.comp_left, h2]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left, h3]
    exact Category.assoc _ _ _

theorem isDerivAt0_congr {g : ℕ} {X : Scheme.{0}} {e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (h : IsDerivAt0 e w v) (he : ∀ᶠ z in nhds 0, e' z = e z) : IsDerivAt0 e' w v := by
  refine ⟨h.1.trans he.self_of_nhds.symm, fun U hU f => (h.2 U hU f).trans ?_⟩
  have : (fun z => valAt' (e' z) U f) =ᶠ[nhds 0] fun z => valAt' (e z) U f := he.mono fun z hz => by simp only [hz]
  rw [this.fderiv_eq]

theorem hom_dual_const {F : Type} [Field F] [NumberField F] (δ : F →+* DualNumber ℂ) :
    δ = (algebraMap ℂ (DualNumber ℂ)).comp ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ) := by
  have hu : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have h := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom
    ⟨2, by
      rw [Submodule.zero_eq_bot, eq_bot_iff, sq, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩
    δ.toRatAlgHom ((algebraMap ℂ (DualNumber ℂ)).comp ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp δ)).toRatAlgHom
    (fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  exact RingHom.ext fun x => DFunLike.congr_fun h x

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem model_periods {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    {A : Type} [Fintype A] (b : A → 𝔐.Li) {n : ℕ} (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (τ : c.F →+* ℂ)
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hc : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)))
    (hi : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u))
    (hlat : ∀ a, b a ∈ 𝔐.M.lat ⟨centre (p 0), 𝔐.all _⟩) :
    ∃ (i : Fin FU.n) (ρ : ℝ) (B : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)))
      (W : A → (Fin n → ℂ) → Fin g → ℂ) (G : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), 0 < ρ ∧ ρ ≤ 1 ∧
      IsOpen B ∧ 0 ∈ B ∧ B ⊆ Metric.ball 0 1 ∧ IsHolPeriods (FU.Di i) ty B P ∧
      (∀ a, DifferentiableOn ℂ (W a) B) ∧ (∀ u ∈ B,
        ((G u).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (G u) z z).re) ∧
          ∀ x y, (hermForm (G u) (P u x) (P u y)).im = (FU.Di i).EF x y) ∧
        (∀ (r : ℕ) (f : Fin r → A), 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (fun k => b (f k))
          (Matrix.of fun i j => (Real.pi : ℂ) * hermForm (G u) (W (f j) u) (W (f i) u))) ∧
        ∀ a s, b a ∈ 𝔐.Vgen s → ∀ (t : 𝓞 E) j, ty j (t : E) * W a u j = τ (labelEmb c s t) * W a u j) ∧
      ∀ v, (∀ (U : Xo.X.Opens) (f : Γ(Xo.X, U)), ⊤ ≤ FU.u i (P 0) ⁻¹ᵁ U →
          fderiv ℂ (fun u => valAt' (FU.u i (P u)) U f) 0 v = 0) →
        ∃ V : Sp (DualNumber ℂ) ⟶ 𝔐.X, IsDerivAt0 (fun u => p ((ρ : ℂ) • u)) v V ∧
          V ≫ 𝔐.f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 ≫ 𝔐.f := by
  classical
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  let ea := Fintype.equivFin A
  obtain ⟨W, hW, v, hq, htan, hval⟩ := GlobalTheory.T.lattice_tangent_vectors_affine_open 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ⟨centre (p 0), 𝔐.all _⟩ _
    (fun k => b (ea.symm k)) 𝔐.tie.gen (fun k => hlat _)
  have hW0 : ⊤ ≤ p 0 ⁻¹ᵁ W := fun x _ => by
    have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst this
    exact hq
  obtain ⟨ρ₁, ψ, hρ₁, hρ₁', hψ, hψp⟩ := GlobalTheory.T.holomorphic_disc_in_affine_open 𝔐.X W hW n p hp hW0
  have hp₁ : IsHolTo (Metric.ball 0 1) (fun u => spMap (ψ u)) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap Metric.isOpen_ball hψ.2
  obtain ⟨tW, ⟨mW⟩⟩ := exists_sab hW.fromSpec 𝔐.t
  obtain ⟨mY, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp 𝔐.m mW
  obtain ⟨ρ₂, C, h, κ, hρ₂, hρ₂', ⟨mC⟩, hκ₁, hκ₂, hC⟩ := exists_chart Y _ (hW.fromSpec ≫ 𝔐.f) tW mY τ n
    (fun u => spMap (ψ u)) hp₁
    (fun u hu => by
      have := hc _ (FramePeriods.smul_mem_ball' hρ₁ hρ₁' hu)
      rw [← hψp u hu] at this
      simpa using this)
    (fun u hu x hx => FramePeriods.interior_range 𝔐 _ (hi _ (FramePeriods.smul_mem_ball' hρ₁ hρ₁' hu.1)) x (by
      rw [hx, ← hψp u hu.1, Category.assoc]))
  obtain ⟨θ, hθ⟩ : ∃ θ : Γ(𝔐.X, W) →+* C.R, spMap θ = h := ⟨(Spec.preimage h).hom, Spec.map_preimage _⟩
  subst hθ
  obtain ⟨mX, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mW mC
  obtain ⟨x, hx⟩ := GlobalTheory.T.abelian_map_tangent_coordinates E H 𝔐.X 𝔐.t Γ(𝔐.X, W) hW.fromSpec _ v C.R C.t θ mX C.g C.M htan
  have hw : ∀ z : Fin n → ℂ, ∃ w : A → (epsAt (spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec) ⟶ 𝔐.t.G),
      (∀ k, 𝔐.M.ValAt _ (b k) (w k)) ∧
      ∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x (ea k))).left ≫ mX.φ := fun z => by
    have e : spMap ((C.ψ z).comp θ) ≫ hW.fromSpec = spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec := by
      rw [← Category.assoc]; congr 1; exact Spec.map_comp _ _
    choose w hw1 hw2 using hval ((C.ψ z).comp θ) _ e (𝔐.all _)
    refine ⟨fun k => w (ea k), fun k => by simpa using hw1 (ea k), fun k => ?_⟩
    rw [hw2, FramePeriods.dualMap_comp', hx, Category.assoc]
  have hpt : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ spMap θ ≫ hW.fromSpec =
      p (((ρ₁ * ρ₂ : ℝ) : ℂ) • z) := fun z hz => by
    rw [← Category.assoc, hC z hz, hψp _ (FramePeriods.smul_mem_ball' hρ₂ hρ₂' hz), smul_smul]
    push_cast
    rfl
  have hρ : 0 < ρ₁ * ρ₂ := mul_pos hρ₁ hρ₂
  have hρ' : ρ₁ * ρ₂ ≤ 1 := mul_le_one₀ hρ₁' hρ₂.le hρ₂'
  obtain ⟨i, B, P, Wv, G, hB, h0, hsub, hP, hWv, hall⟩ := chart_periods C FU fun a => x (ea a)
  have hpu : punct n 0 1 = Metric.ball 0 1 := by ext z; simp [punct]
  refine ⟨i, ρ₁ * ρ₂, B, P, Wv, G, hρ, hρ', hB, h0, hsub, hP, hWv, fun u hu => ⟨(hall u hu).2.1, fun r f => ?_,
    fun a s hs t => ?_⟩, fun v hv => ?_⟩
  · obtain ⟨Hm, hR, hH⟩ := (hall u hu).2.2.1
    obtain ⟨w, hw1, hw2⟩ := hw u
    have hg := GlobalTheory.T.chart_lattice_tangent_coordinates E H D l Xo _ n 0 C 𝔐.X 𝔐.t _ mX Ω 𝔐.ξ 𝔐.Li 𝔐.M r (fun k => b (f k))
      (fun k => x (ea (f k))) u Hm (fun k => w (f k)) hR (fun k => hw1 _) (fun k => hw2 _)
    rw [← hpt u (hsub hu)]
    convert hg using 4 with _ i' _ j'
    rw [← hH]
    rfl
  · obtain ⟨w, hw1, hw2⟩ := hw u
    refine (hall u hu).2.2.2 a t _ ?_
    have hint : _root_.IsIntegral ℤ (labelEmb c s t) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) t).map (labelEmb c s).toIntAlgHom
    obtain ⟨h1, st, hst, hst'⟩ := valAt_cst (z := spMap (C.ψ u) ≫ spMap θ ≫ hW.fromSpec) (𝔐.all _) (𝔐.f ≫ Y.s)
      𝔐.cst_over (by
        rw [hpt u (hsub hu)]
        exact hc _ (FramePeriods.smul_mem_ball' hρ hρ' (hsub hu))) ⟨_, hint⟩
    have h2 := (hw1 a).smul h1 st
    haveI := 𝔐.t.act.hom t
    have h3 := lieValAt_end (𝔐.act t) (hw1 a)
    have h4 : 𝔐.ρ t (b a) = 𝔐.emb s t • b a := sub_eq_zero.1 ((Submodule.mem_iInf _).1 hs t)
    have h5 : genMap 𝔐.ξ ⟨_, h1⟩ st = 𝔐.emb s t := hst
    have h6 : (Scheme.stalkClosedPointTo (spMap (C.ψ u) ≫ spMap θ ≫ hW.fromSpec)).hom st =
      τ (labelEmb c s t) := hst'
    rw [h5, ← h4, h6] at h2
    have h7 := congrArg CommaMorphism.left (h3.unique 𝔐.tie.gen h2)
    obtain ⟨vv, hvv⟩ := RiemGram.exists_value C.M (C.ψ u) (x (ea a))
    rw [← hvv]
    have h8 : (w a).left = vv.left ≫ mX.φ := by rw [hw2, hvv, Category.assoc]
    refine mX.cart.1.hom_ext ?_ ?_
    · have h9 : (w a).left ≫ (𝔐.t.act.act t).left = spMap (Tor.epsMul (τ (labelEmb c s t))) ≫ (w a).left := h7
      rw [h8, Category.assoc] at h9
      rw [Category.assoc, Category.assoc]
      exact (congrArg (vv.left ≫ ·) (mX.act t)).trans h9
    · exact (Over.w (vv ≫ C.t.act.act t)).trans (Over.w (LieTangent.epsScale _ (τ (labelEmb c s t)) ≫ vv)).symm
  · have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
    obtain ⟨v', hv'⟩ := exists_isDerivAt0_loc (Marking.isHolTo_pt C) (hpu ▸ hb0) v
    have hn : B ∈ nhds (0 : Fin n → ℂ) := hB.mem_nhds h0
    have hpj : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, C.pt u ≫ C.j ≫ spMap θ ≫ hW.fromSpec =
        p (((ρ₁ * ρ₂ : ℝ) : ℂ) • u) := fun u hu => by
      rw [← Category.assoc, (C.pt_eq u (hpu ▸ hu)).1, hpt u hu]
    refine ⟨v' ≫ C.j ≫ spMap θ ≫ hW.fromSpec, isDerivAt0_congr (PullbackSections.ExpRows.isDerivAt0_comp_hom hv' _)
      (Filter.eventually_of_mem hn fun u hu => (hpj u (hsub hu)).symm), ?_⟩
    have h1 : IsDerivAt0 (fun u => FU.u i (P u)) v (v' ≫ C.k) :=
      isDerivAt0_congr (PullbackSections.ExpRows.isDerivAt0_comp_hom hv' _)
        (Filter.eventually_of_mem hn fun u hu => (hall u hu).1)
    have h2 := PullbackSections.ExpRows.isDerivAt0_unique h1 (GlobalTheory.LocalLift.isDerivAt0_const _ v hv)
    have h3 : v' ≫ κ = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ C.pt 0 ≫ κ := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hκ₂]
        rw [h2, (hall 0 h0).1]
      · obtain ⟨δ, hδ⟩ : ∃ δ : c.F →+* DualNumber ℂ, spMap δ = v' ≫ κ ≫ pullback.snd _ _ :=
          ⟨(Spec.preimage (v' ≫ κ ≫ pullback.snd _ _)).hom, Spec.map_preimage _⟩
        haveI : FiniteDimensional ℚ c.F := c.fin
        haveI : NumberField c.F := ⟨⟩
        have h4 : C.pt 0 = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' := hv'.1.symm
        simp only [Category.assoc, h4, ← hδ]
        conv_lhs => rw [hom_dual_const δ]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have h5 := hpj 0 hb0
    rw [smul_zero] at h5
    have h6 : C.j ≫ spMap θ ≫ hW.fromSpec ≫ 𝔐.f = κ ≫ Y.j := hκ₁.symm
    rw [← h5]
    simp only [Category.assoc, h6]
    rw [← Category.assoc, h3]
    simp only [Category.assoc]

end PositivityTheory.Xgp.c_bm_exists_period
