import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.SemiPosBir

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

open ReciprocityTheory.L2DbarEstimates in

theorem continuousAt_levi {g : V D → ℂ} {x : V D} (hg : ContDiffAt ℝ 2 g x) (ξ : Fin D → ℂ) :
    ContinuousAt (fun v => leviV D g v ξ) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have h2 : ∀ l, ContDiffAt ℝ 1 (wdb D l g) x := fun l =>
    ((h1.clm_apply contDiffAt_const).add
      (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))).div_const 2
  have h3 : ∀ j l, ContinuousAt (wd D j (wdb D l g)) x := fun j l => by
    have h4 : ContinuousAt (fderiv ℝ (wdb D l g)) x :=
      ((h2 l).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((h4.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (h4.clm_apply continuousAt_const))).div_const 2
  unfold leviV
  exact tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun l _ =>
    ((h3 j l).mul continuousAt_const).mul continuousAt_const

theorem ae_mem [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (c : AlgChart p σ D)
    {U : X.Opens} (hU : (U : Set X).Nonempty) :
    ∀ᵐ v : V D, v ∈ c.e.target → c.e.symm v ∈ ptsIn p σ U := by
  rcases c.e.source.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · exact .of_forall fun v hv => absurd (c.e.map_target hv) (h ▸ notMem_empty _)
  have hy' := mem_ptsIn.1 (c.source_subset hy)
  obtain ⟨x, hx, hx'⟩ := nonempty_preirreducible_inter U.isOpen c.U.isOpen hU ⟨_, hy'⟩
  obtain ⟨a, ha, ha'⟩ := c.affine.exists_basicOpen_le (V := U) ⟨x, hx⟩ hx'
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at ha'
    exact ha'
  have : Nonempty c.U := ⟨⟨_, hy'⟩⟩
  let φ := MvPolynomial.eval₂Hom (algX p c.U) c.x
  let : Algebra (MvPolynomial (Fin D) k) Γ(X, c.U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin D) k) Γ(X, c.U) := c.etale
  have h₁ := isAlgebraic_of_flat_of_formallyUnramified (MvPolynomial (Fin D) k) Γ(X, c.U)
  obtain ⟨r, hr, b, hb⟩ := (h₁.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hr' : MvPolynomial.map σ r ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ hσ)).2 hr
  filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (V D))
    (WithLp.linearEquiv 2 ℂ (Fin D → ℂ)) _ hr'] with v hv hvt
  have hs := c.e.map_target hvt
  have hz := c.source_subset hs
  refine ptsIn_mono ha ((mem_ptsIn_basicOpen hz a).2 fun e => hv ?_)
  have e₁ : (evHom hz).comp φ = (MvPolynomial.eval (WithLp.linearEquiv 2 ℂ (Fin D → ℂ) v)).comp
      (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        MvPolynomial.eval_C, ← ev_eq, ev_algX hz]
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        MvPolynomial.eval_X, ← ev_eq, ← c.apply_eq _ hs, c.e.right_inv hvt]
      rfl
  have e₂ : φ r = a * b := hb
  refine (RingHom.congr_fun e₁ r).symm.trans ?_
  rw [RingHom.comp_apply, e₂, ← ev_eq, ev_mul, e, zero_mul]

variable (D) in

def PosOn (f : CxPts p σ → ℝ) (S : Set (CxPts p σ)) : Prop :=
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source ∩ S, ∀ ξ : Fin D → ℂ,
    0 ≤ (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

theorem PosOn.of_inter [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ)
    {f : CxPts p σ → ℝ} {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y)
    {U : X.Opens} (hU : (U : Set X).Nonempty) (h : PosOn D f (S ∩ ptsIn p σ U)) :
    PosOn D f S := fun c y hy ξ => by
  have ho := (isOpen_over c.e hS).mem_nhds (mem_over c.e hy.1 hy.2)
  have hd : ContDiffAt ℝ 2 (fun v => f (c.e.symm v)) (c.e y) :=
    ((contDiffOn_chart hf c).contDiffAt ho).of_le (by norm_cast)
  have hc := Complex.continuous_re.continuousAt.comp
    (continuousAt_levi (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd) ξ)
  have hfr := (mem_closure_iff_frequently.1 ((Measure.dense_of_ae (ae_mem hσ c hU)) (c.e y)))
  refine isClosed_Ici.mem_of_frequently_of_tendsto ((hfr.and_eventually ho).mono ?_) hc
  rintro v ⟨h₁, h₂, h₃⟩
  have := h c _ ⟨c.e.map_target h₂, h₃, h₁ h₂⟩ ξ
  rwa [c.e.right_inv h₂] at this

theorem levi_pull {j : Z ⟶ X} (hj : j ≫ p = q) (f : CxPts p σ → ℝ) (c : AlgChart p σ D)
    (c' : AlgChart q σ D) (e : c'.U ≤ j ⁻¹ᵁ c.U) (hx : ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a))
    {z : CxPts q σ} (hz : z ∈ c'.e.source) (hz' : PtsOver.map j hj _ z ∈ c.e.source)
    (ξ : Fin D → ℂ) :
    leviV D (fun v => (f (PtsOver.map j hj _ (c'.e.symm v)) : ℂ)) (c'.e z) ξ =
      leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e (PtsOver.map j hj _ z)) ξ := by
  have he (w) (hw : w ∈ c'.e.source) (hw' : PtsOver.map j hj (spMap σ) w ∈ c.e.source) :
      c'.e w = c.e (PtsOver.map j hj (spMap σ) w) := by
    ext a
    rw [c'.apply_eq w hw, c.apply_eq _ hw', hx]
    exact valR_appLE w.1 j e (c'.source_subset hw) _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map j hj (spMap σ) ⁻¹' c.e.source) :=
    c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map j hj _))
  rw [← he z hz hz']
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ
  filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv
  have e₁ : c.e.symm v = PtsOver.map j hj _ (c'.e.symm v) := by
    have := he _ hv.2.1 hv.2.2
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)
  rw [e₁]

theorem appLE_comp_eval {j : Z ⟶ X} (hj : j ≫ p = q) {U : X.Opens} {W : Z.Opens}
    (e : W ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)) :
    (j.appLE U W e).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) =
      MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE U W e).hom (x a) := by
  subst hj
  refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact congrArg (fun g : Γ(Sp k, ⊤) ⟶ Γ(Z, W) => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom t))
      (Scheme.Hom.appLE_comp_appLE j p ⊤ U W le_top e)
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem exists_map_eq (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ j.opensRange) : ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  have H : Set.range y.1 ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hy (x := x) trivial
  refine ⟨⟨IsOpenImmersion.lift j y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

theorem PosOn.pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (h : PosOn D f S) :
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  fun c' z hz ξ => by
  have e : c'.U ≤ j ⁻¹ᵁ j ''ᵁ c'.U := (j.preimage_image_eq _).ge
  have hi : IsIso (j.appLE _ _ e) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (j.appLE _ _ e)
  choose x hx using fun a => hb.2 (c'.x a)
  have h₁ := appLE_comp_eval hj e x
  have h₂ : (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x).Etale := by
    refine (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)) (j.appLE _ _ e)).1 ?_
    change ((j.appLE _ _ e).hom.comp (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)).Etale
    rw [h₁, show (fun a => (j.appLE _ _ e).hom (x a)) = c'.x from funext hx]
    exact c'.etale
  obtain ⟨c, hc, hU, hcx⟩ := AlgChart.exists_of_etale (y := PtsOver.map j hj (spMap σ) z)
    (c'.affine.image_of_isOpenImmersion j) x h₂
    (mem_ptsIn.2 ⟨_, mem_ptsIn.1 (c'.source_subset hz.1), rfl⟩)
  have key : ∀ (U : X.Opens) (hU : c.U = U) (e : c'.U ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)),
      c.x = hU ▸ x → (∀ a, (j.appLE _ _ e).hom (x a) = c'.x a) →
      ∃ e : c'.U ≤ j ⁻¹ᵁ c.U, ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a) := by
    rintro _ rfl e x h₁ h₂
    exact ⟨e, fun a => by rw [h₁]; exact (h₂ a).symm⟩
  obtain ⟨e', hx'⟩ := key _ hU e x hcx hx
  rw [levi_pull hj f c c' e' hx' hz.1 hc]
  exact h c _ ⟨hc, hz.2⟩ ξ

theorem PosOn.of_pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ j.opensRange) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq j hj hy.2.2
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

theorem posOn_iff_pull [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (j : Z ⟶ X)
    [IsOpenImmersion j] [Nonempty Z] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y) : PosOn D f S ↔
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  ⟨fun h => h.pull j hj, fun h => (h.of_pull j hj).of_inter hσ hS hf (range_nonempty _)⟩

theorem semiPos_iff_pull : ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∀ L : HermLB p, (L.SemiPos D ↔ (L.pull π hπ).SemiPos D) := by
  intro k _ X X' p q D hp hq π hπ U hU hi L
  have := hp.isDomain
  have := hp.finite
  have := hp.isIntegral
  have := hq.isIntegral
  refine forall_congr' fun σ => ?_
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Nonempty U.toScheme := hU.to_subtype
  have : Nonempty (π ⁻¹ᵁ U).toScheme := (π ∣_ U).surjective.nonempty
  have : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have key (i : L.B.ι) : PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i)) ↔
      PosOn D (fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w))
        (PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i)) := by
    rw [posOn_iff_pull hσ ((π ⁻¹ᵁ U).ι ≫ π) rfl (isOpen_ptsIn _) (L.cInf σ i),
      posOn_iff_pull hσ (π ⁻¹ᵁ U).ι (q := ((π ⁻¹ᵁ U).ι ≫ π) ≫ p) (by rw [Category.assoc, hπ])
        ((isOpen_ptsIn _).preimage (PtsOver.continuous_map π hπ _))
        fun y hy => CInfAt.pull π hπ (L.cInf σ i _ hy)]
    have e (w : CxPts (((π ⁻¹ᵁ U).ι ≫ π) ≫ p) σ) : PtsOver.map ((π ⁻¹ᵁ U).ι ≫ π) rfl _ w =
        PtsOver.map π hπ _ (PtsOver.map (π ⁻¹ᵁ U).ι (by rw [Category.assoc, hπ]) _ w) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [funext e]
    simp only [e]
    rfl
  have e₁ (J : (L.B.pull π).ι) : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U (J PUnit.unit)) := Set.ext fun z => by
    rw [mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => mem_iInter.1 h PUnit.unit, fun h => mem_iInter.2 fun _ => h⟩
  have e₂ (J : (L.B.pull π).ι) : ((L.φ σ).pull π hπ).φ J =
      fun w => (L.φ σ).φ (J PUnit.unit) (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  change (∀ i, PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))) ↔
    ∀ J, PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J))
  simp only [e₁, e₂, key]
  exact ⟨fun h J => h _, fun h i => h fun _ => i⟩

end GlobalTheory.SemiPosBir
