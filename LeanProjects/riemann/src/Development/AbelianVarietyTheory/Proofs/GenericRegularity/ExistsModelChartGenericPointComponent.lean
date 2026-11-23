import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericChart

theorem exists_sec_ne_zero_of_iso {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (s : A.Sec) (j : A.ι) (hj : s.f j ≠ 0) : ∃ (s' : B.Sec) (k : B.ι), s'.f k ≠ 0 := by
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullId B) (chartPullPull A (𝟙 X) (𝟙 X) rfl) h.symm
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) hA hB s
  refine ⟨s', ?_⟩
  by_contra hn
  push Not at hn
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨k, hk⟩ := exists_chart hB x
  have e := hs' X (𝟙 X) x j k hx hk
  rw [hn k, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero, mul_zero, Category.comp_id] at e
  rw [e, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]

theorem exists_secOn_of_isOpenImmersion {X₀ X : Scheme.{0}} (q : X₀ ⟶ X) [IsOpenImmersion q] (L : LB X)
    (V₀ : X₀.Opens) (V : X.Opens) (hV : V ≤ q.opensRange) (hV₀ : q ⁻¹ᵁ V ≤ V₀)
    (θ : ∀ J, Γ(X₀, V₀ ⊓ (L.pull q).U J)) (hθ : θ ∈ secOn (L.pull q) V₀) :
    ∃ θ' ∈ secOn L V, ∀ (z : X₀) (i : L.ι), q z ∈ V → z ∈ X₀.basicOpen (θ fun _ => i) →
      q z ∈ X.basicOpen (θ' i) := by
  have bij : ∀ W : X.Opens, W ≤ V → Function.Bijective (q.app W).hom := fun W hW =>
    have := q.isIso_app W (hW.trans hV)
    ConcreteCategory.bijective_of_isIso (q.app W)
  have le : ∀ i, q ⁻¹ᵁ (V ⊓ L.U i) ≤ V₀ ⊓ (L.pull q).U (fun _ => i) := fun i z hz => ⟨hV₀ hz.1, mem_pull.2 hz.2⟩
  choose θ' hθ' using fun i => (bij (V ⊓ L.U i) inf_le_left).2 (resG X₀ (le i) (θ fun _ => i))
  have val : ∀ i z, q z ∈ V ⊓ L.U i → gs q z _ (θ' i) = gs (𝟙 X₀) z _ (θ fun _ => i) := fun i z hz => by
    have e := gs_pull (𝟙 X₀) q z _ hz (θ' i)
    rw [Category.id_comp, hθ'] at e
    exact e.symm.trans (gs_res (𝟙 X₀) z (le i) hz _)
  refine ⟨θ', fun i j => (bij _ (inf_le_left.trans inf_le_left)).1 (fn_ext fun z hz => ?_), fun z i hz hb => ?_⟩
  · have hz' : q z ∈ V ⊓ L.U i ⊓ L.U j := hz
    refine (gs_pull (𝟙 X₀) q z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 X₀) q z _ hz' _).symm)
    have hm : (𝟙 X₀ : X₀ ⟶ X₀) z ∈ V₀ ⊓ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) :=
      ⟨le i hz'.1, mem_pull.2 hz'.2⟩
    have e := congrArg (gs (𝟙 X₀) z _) (hθ (fun _ => i) (fun _ => j))
    rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm,
      gs_unit _ z ((L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j)) ⟨hm.1.2, hm.2⟩,
      gm_pull_g L q (𝟙 X₀) z _ _ hm.1.2 hm.2, Category.id_comp] at e
    rw [Category.id_comp, gs_res _ z _ hz', gs_mul _ z _ hz', gs_res _ z _ hz', gs_res _ z _ hz',
      gs_unit _ z (L.U i ⊓ L.U j) ⟨hz'.1.2, hz'.2⟩, val i z hz'.1, val j z ⟨hz'.1.1, hz'.2⟩]
    exact e
  · have hi : q z ∈ V ⊓ L.U i := ⟨hz, mem_pull.1 (X₀.basicOpen_le _ hb).2⟩
    show z ∈ q ⁻¹ᵁ X.basicOpen (θ' i)
    rw [Scheme.preimage_basicOpen]
    refine (congrArg (fun a => z ∈ X₀.basicOpen a) (hθ' i)).mpr ?_
    exact (X₀.basicOpen_res (θ fun _ => i) (homOfLE (le i)).op).ge ⟨hi, hb⟩

theorem exists_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_genPt_of_specializes (Z : Comp Xo c) {ξ : Xo.XF c} (h : ξ ⤳ genPt Z) : ξ = genPt Z := by
  have h1 : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
    (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2))
  have h2 : (Z : Set (Xo.XF c)) ⊆ closure {ξ} := h1 ▸ specializes_iff_closure_subset.1 h
  have h3 : closure {ξ} ⊆ (Z : Set (Xo.XF c)) := Z.2.2 isIrreducible_singleton.closure h2
  exact (h.antisymm (specializes_iff_closure_subset.2 (h1 ▸ h3))).eq

theorem exists_section (hT : Out.SecTwistSt) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c)
    [IsNoetherianRing (𝓞 c.F)] [IsFractionRing (𝓞 c.F) c.F] :
    ∃ V : Y.X.Opens, Y.j (genPt Z) ∈ V ∧ ∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i) := by
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  obtain ⟨W, hxW, hW⟩ := ModelChart.exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hU : IsAffineOpen U := hU
  have := hW U hxU hUW
  let R : Type := Γ(Y.X, U)
  let K : Type := FractionRing R
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have b₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 this)
  have := Y.jQ_open
  have a₁ : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁
  have a₂ : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip b₂
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance

  have hgen : hU.fromSpec (⊥ : PrimeSpectrum R) = Y.j (genPt Z) := by
    obtain ⟨p, hp⟩ : Y.j (genPt Z) ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have s₀ : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have s₁ : hU.fromSpec (⊥ : PrimeSpectrum R) ⤳ Y.j (genPt Z) := hp ▸ s₀.map hU.fromSpec.continuous
    obtain ⟨ξ, h₁, h₂⟩ := Flat.generalizingMap Y.j s₁
    rw [← h₂, eq_genPt_of_specializes Z h₁]
  have hK : spMap (algebraMap R K) (IsLocalRing.closedPoint K) = (⊥ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
  obtain ⟨z, hz⟩ := exists_lift_of_isPreimmersion Y.j (spMap (algebraMap R K) ≫ hU.fromSpec) (genPt Z)
    (by rw [← hgen, ← hK]; rfl)
  obtain ⟨t₀, ⟨m₀⟩⟩ := (ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp R) hU.fromSpec
  obtain ⟨t', ⟨m₂⟩⟩ : ∃ t' : SAB H (Sp K), Nonempty (SABMap t' t₀ (spMap (algebraMap R K))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap R K)) t₀
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₂
  have cancel : ∀ (p : Sp K ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre hT amplePt Y.oF m₃
  obtain ⟨k, hk⟩ : ∃ k, b.f k ≠ 0 := by
    by_contra h0
    push Not at h0
    obtain ⟨a, -, ha⟩ := hb b
    exact zero_ne_one ((ha 0 fun i => by rw [h0, mul_zero]).trans (ha 1 fun i => by rw [h0, mul_zero]).symm)
  obtain ⟨w, hw, -⟩ := n.lin
  have iso : LBIso t'.PP.L ((Y.t.PP.L.pull m₀.φ).pull m₂.φ) := LBIso.chartPull (chartPullId _) (chartPullLinComb Y.t.PP.L m₀.φ (K := PUnit) (fun _ => m₂.φ)
    (fun _ => n.φ) (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]; exact hn.symm)) ⟨w, hw⟩
  have hL₀ := pull_isLB Y.t.PP.isLB m₀.φ
  obtain ⟨h, h0, θ, hθ, nz⟩ := SecSpread.main R t₀.G t₀.semi _ hL₀ K _ m₂.φ _ m₂.cart.1
    (exists_sec_ne_zero_of_iso t'.PP.isLB (pull_isLB hL₀ _) iso b k hk)
  have : IsOpenImmersion m₀.φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₀.cart.1.flip inferInstance
  have pre : ∀ p : Sp R, hU.fromSpec p ∈ Y.X.basicOpen h ↔ p ∈ PrimeSpectrum.basicOpen h := fun p =>
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen h) p
  have sq : ∀ g, Y.t.G.hom (m₀.φ g) = hU.fromSpec (t₀.G.hom g) := fun g => congr($(m₀.cart.1.w) g)
  have rg : ∀ y ∈ Y.X.basicOpen h, ∃ p : Sp R, hU.fromSpec p = y := fun y hy => by
    show y ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]; exact Y.X.basicOpen_le h hy
  obtain ⟨θ', hθ', nz'⟩ := exists_secOn_of_isOpenImmersion m₀.φ Y.t.PP.L _ (Y.t.G.hom ⁻¹ᵁ Y.X.basicOpen h)
    (fun g hg => by
      obtain ⟨p, hp⟩ := rg _ hg
      obtain ⟨g', h₁, -⟩ := Scheme.exists_preimage_of_isPullback m₀.cart.1 g p hp.symm
      exact ⟨g', h₁⟩)
    (fun g hg => (pre _).1 (sq g ▸ hg)) θ hθ
  refine ⟨Y.X.basicOpen h, ?_, θ', hθ', fun y hy => ?_⟩
  · rw [← hgen]
    exact (pre _).2 h0
  · obtain ⟨p, rfl⟩ := rg y hy
    obtain ⟨g, i, rfl, hg⟩ := nz p ((pre p).1 hy)
    exact ⟨m₀.φ g, i PUnit.unit, sq g, nz' g _ (show Y.t.G.hom (m₀.φ g) ∈ _ from sq g ▸ hy) hg⟩

open ModelChart in

theorem exists_chart_genPt : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  intro hT E _ _ _ H Dw l Xo c Y Z
  have := c.fin
  have : NumberField c.F := {}
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := Y.t.semi.smooth
  obtain ⟨W, hxW, hW⟩ := exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨V, hxV, θ, hθ, nz⟩ := exists_section hT Y Z
  obtain ⟨U, hU, hxU, hUW, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G _ (W ⊓ V) ⟨hxW, hxV⟩
  have hUV : U ≤ V := hUW.trans inf_le_right
  have nz' : ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen
      (resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hUV)) (θ i)) := fun y hy => by
    obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp Γ(Y.X, U)) hU.fromSpec
  have c₀ : IsGrpPullback t₀.G Y.t.G (spMap (RingHom.id Γ(Y.X, U)) ≫ hU.fromSpec) m₀.φ := by
    have e : spMap (RingHom.id Γ(Y.X, U)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    exact m₀.cart
  obtain ⟨u, hu, hb⟩ := hv _ (RingHom.id _) t₀.G m₀.φ c₀
  simp only [spMap_dualMapR_id, Category.id_comp] at hu
  have ex : ∀ a j, ∃ r : Fin n → Γ(Y.X, U), IsLieComb r u (u j ≫ t₀.act.act a) := fun a j =>
    have := t₀.act.hom a
    (hb.2 _ (isTangent_comp_hom (hb.1 j) _)).exists
  choose r hr using ex
  refine ⟨⟨U, hU, hW U hxU (hUW.trans inf_le_left), _, res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, nz', n, v₀,
    fun a i j => r a j i, fun R' _ f t' m => ?_⟩, hxU⟩
  obtain ⟨v', hv', hb'⟩ := hv R' f t'.G m.φ m.cart
  refine ⟨v', hv', hb', fun a j => ?_⟩
  have hp := m₀.cart.1
  let F : t'.G.left ⟶ t₀.G.left := hp.lift m.φ (t'.G.hom ≫ spMap f) (by rw [m.cart.1.w, Category.assoc])
  have hF : F ≫ m₀.φ = m.φ := hp.lift_fst _ _ _
  have hw : F ≫ t₀.G.hom = t'.G.hom ≫ spMap f := hp.lift_snd _ _ _
  have hc : IsGrpPullback t'.G t₀.G (spMap f) F := m₀.cart.cancel (hF ▸ m.cart) hw
  have lies : ∀ (w' : epsR R' ⟶ t'.G) (w : epsR Γ(Y.X, U) ⟶ t₀.G),
      w'.left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ≫ m₀.φ →
      w'.left ≫ F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left := fun w' w h => by
    apply hp.hom_ext
    · rw [Category.assoc, hF, h, Category.assoc]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over f).symm
  refine (GlobalTheory.lieComb_baseChange _ _ f t₀.G t'.G F hc n u _ (r a j) v' _
    (fun k => lies _ _ (by rw [hv', hu])) (hr a j)).1 (lies _ _ ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, m.act, m₀.act, ← Category.assoc, hv',
    ← Category.assoc (u j).left, hu, Category.assoc]

end GlobalTheory.GenericChart
