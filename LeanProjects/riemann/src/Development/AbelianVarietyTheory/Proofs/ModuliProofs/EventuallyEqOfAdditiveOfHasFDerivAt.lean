import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.TendstoUniformlyOnDoublingLogOfContraction

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelExp

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}

def HolAt (a : E → (Sp ℂ ⟶ Z)) (w₀ : E) : Prop := ∃ W, IsOpen W ∧ w₀ ∈ W ∧ IsHolTo W a

theorem isHolTo_mono {a : E → (Sp ℂ ⟶ Z)} {W W' : Set E} (h : IsHolTo W a) (hW' : IsOpen W') (hs : W' ⊆ W) :
    IsHolTo W' a := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.mono fun w hw => ⟨hs hw.1, hw.2⟩⟩
  convert hW'.inter h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hs hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem HolAt.const (x : Sp ℂ ⟶ Z) (w₀ : E) : HolAt (fun _ => x) w₀ := by
  refine ⟨Set.univ, isOpen_univ, trivial, fun U f => ⟨?_, differentiableOn_const _⟩⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U <;> simp [h]

namespace HolAt

variable {a a' : E → (Sp ℂ ⟶ Z)} {w₀ : E}

theorem eventually_mem (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) : ∀ᶠ w in 𝓝 w₀, ⊤ ≤ a w ⁻¹ᵁ U := by
  obtain ⟨W, -, hw, h⟩ := h
  filter_upwards [(h U 0).1.mem_nhds ⟨hw, hU⟩] with w hw using hw.2

theorem analyticAt [FiniteDimensional ℂ E] (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) (f : Γ(Z, U)) :
    AnalyticAt ℂ (fun w => valAt' (a w) U f) w₀ := by
  obtain ⟨W, -, hw, h⟩ := h
  exact SCV.analyticAt_of_differentiableOn (h U f).2 ((h U f).1.mem_nhds ⟨hw, hU⟩)

theorem analyticAt_pi [FiniteDimensional ℂ E] (h : HolAt a w₀) {U : Z.Opens} (hU : ⊤ ≤ a w₀ ⁻¹ᵁ U) {κ : Type}
    [Fintype κ] (f : κ → Γ(Z, U)) : AnalyticAt ℂ (fun w i => valAt' (a w) U (f i)) w₀ :=
  analyticAt_pi_iff.mpr fun i => h.analyticAt hU (f i)

theorem eventually (h : HolAt a w₀) : ∀ᶠ w in 𝓝 w₀, HolAt a w := by
  obtain ⟨W, hW, hw, h⟩ := h
  filter_upwards [hW.mem_nhds hw] with w hw using ⟨W, hW, hw, h⟩

theorem congr (h : HolAt a w₀) (e : a =ᶠ[𝓝 w₀] a') : HolAt a' w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1 e
  have h' := isHolTo_mono h (hW.inter hSo) Set.inter_subset_left
  refine ⟨W ∩ S, hW.inter hSo, ⟨hw, hS0⟩, fun U f => ?_⟩
  have : {b ∈ W ∩ S | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ W ∩ S | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [hS b hb.2]
  rw [this]
  exact ⟨(h' U f).1, (h' U f).2.congr fun b hb => by rw [hS b hb.1.2]⟩

theorem comp [CompleteSpace E] {φ : E' → E} {v₀ : E'} (h : HolAt a (φ v₀)) (hφ : AnalyticAt ℂ φ v₀) :
    HolAt (fun v => a (φ v)) v₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  obtain ⟨S, hS, hSo, hS0⟩ := eventually_nhds_iff.1
    (hφ.eventually_analyticAt.and (hφ.continuousAt.eventually (hW.mem_nhds hw)))
  have hd : DifferentiableOn ℂ φ S := fun v hv => (hS v hv).1.differentiableAt.differentiableWithinAt
  refine ⟨S, hSo, hS0, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hd.mono fun w hw => hw.1) fun w hw => ⟨(hS w hw.1).2, hw.2⟩⟩
  convert hd.continuousOn.isOpen_inter_preimage hSo h1 using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, (hS w hw.1).2, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩

theorem post (h : HolAt a w₀) (q : Z ⟶ Y) : HolAt (fun w => a w ≫ q) w₀ := by
  obtain ⟨W, hW, hw, h⟩ := h
  refine ⟨W, hW, hw, fun U f => ?_⟩
  obtain ⟨h1, h2⟩ := h (q ⁻¹ᵁ U) ((q.app U).hom f)
  exact ⟨h1, h2.congr fun w _ => (valAt'_comp _ _ _ _).symm⟩

end HolAt

theorem isHolTo_of_holAt {a : E → (Sp ℂ ⟶ Z)} {W : Set E} (hW : IsOpen W) (h : ∀ w ∈ W, HolAt a w) :
    IsHolTo W a := by
  intro U f
  have key : ∀ w ∈ {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U}, {b ∈ W | ⊤ ≤ a b ⁻¹ᵁ U} ∈ 𝓝 w := fun w hw =>
    Filter.Eventually.and (hW.mem_nhds hw.1) ((h w hw.1).eventually_mem hw.2)
  refine ⟨isOpen_iff_mem_nhds.2 key, fun w hw => ?_⟩
  obtain ⟨W', -, hw', h'⟩ := h w hw.1
  exact ((h' U f).2.differentiableAt ((h' U f).1.mem_nhds ⟨hw', hw.2⟩)).differentiableWithinAt

theorem holAt_of_isPullback {S X : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)} {w₀ : E} (ha : HolAt (fun w => c w ≫ p) w₀)
    (hb : HolAt (fun w => c w ≫ q) w₀) : HolAt c w₀ := by
  obtain ⟨W₁, hW₁, hw₁, ha⟩ := ha
  obtain ⟨W₂, hW₂, hw₂, hb⟩ := hb
  have hW := hW₁.inter hW₂
  replace ha := isHolTo_mono ha hW Set.inter_subset_left
  replace hb := isHolTo_mono hb hW Set.inter_subset_right
  refine ⟨W₁ ∩ W₂, hW, ⟨hw₁, hw₂⟩, fun U f => ?_⟩
  generalize W₁ ∩ W₂ = W at ha hb
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨S₀, hS₀, hx₀, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := (c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ)) trivial
  obtain ⟨U₁, hU₁, hx₁, h₁⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := s ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ p) (default : PrimeSpectrum ℂ)) hx₀
  obtain ⟨U₂, hU₂, hx₂, h₂⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := t ⁻¹ᵁ S₀)
    (x := (c w₀ ≫ q) (default : PrimeSpectrum ℂ)) (by rw [H.w] at hx₀; exact hx₀)
  have h₁' : U₁ ≤ s ⁻¹ᵁ S₀ := h₁
  have h₂' : U₂ ≤ t ⁻¹ᵁ S₀ := h₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hS₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁'
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := S₀) (UT := U₂) (UX := U₁) h₂' h₁' hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hS₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
      · exact ((hb U₂ y).2.mono fun w hw => ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE _ _ _ _ _ _ hw.2
    | zero => simp only [valAt'_zero]; exact differentiableOn_const _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simp only [valAt'_add]; exact hx.add hy
    | neg x _ hx => simp only [valAt'_neg]; exact hx.neg
    | mul x y _ _ hx hy => simp only [valAt'_mul]; exact hx.mul hy

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : E → (Sp ℂ ⟶ X)} {w₀ : E}

theorem HolAt.mul {a b : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀)
    (hb : HolAt (Z := G.left) (fun w => (b w).left) w₀) :
    HolAt (Z := G.left) (fun w => (a w * b w).left) w₀ := by
  have h1 : ∀ w, (lift (a w) (b w)).left ≫ (fst G G).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have h2 : ∀ w, (lift (a w) (b w)).left ≫ (snd G G).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  have H : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback G.hom G.hom
  exact (holAt_of_isPullback H (c := fun w => (lift (a w) (b w)).left)
    (ha.congr (Eventually.of_forall fun w => (h1 w).symm))
    (hb.congr (Eventually.of_forall fun w => (h2 w).symm))).post μ[G].left

theorem HolAt.inv {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) :
    HolAt (Z := G.left) (fun w => ((a w)⁻¹).left) w₀ :=
  ha.post (GrpObj.inv (X := G)).left

theorem HolAt.one (hy : HolAt y w₀) : HolAt (Z := G.left) (fun w => (1 : Over.mk (y w) ⟶ G).left) w₀ :=
  hy.post η[G].left

theorem HolAt.pow {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) (n : ℕ) :
    HolAt (Z := G.left) (fun w => (a w ^ n).left) w₀ := by
  induction n with
  | zero => simpa only [pow_zero, mul_inv_cancel] using ha.mul ha.inv
  | succ n ih => simpa only [pow_succ] using ih.mul ha

end Group

section Additive

variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]

theorem exists_addMonoidHom_eqOn_ball {g : V → A} {r : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ Metric.ball (0 : V) r, ∀ x' ∈ Metric.ball (0 : V) r, g (x + x') = g x + g x') :
    ∃ e : V →+ A, ∀ x ∈ Metric.ball (0 : V) r, e x = g x := by
  obtain ⟨e, he⟩ := exists_addMonoidHom_eventuallyEq (g := g) (by
    filter_upwards [prod_mem_nhds (Metric.ball_mem_nhds (0 : V) hr) (Metric.ball_mem_nhds (0 : V) hr)] with p hp
    exact hg _ hp.1 _ hp.2)
  refine ⟨e, fun x hx => ?_⟩
  have hball : ∀ k : ℕ, (2⁻¹ : ℝ) ^ k • x ∈ Metric.ball (0 : V) r := fun k => by
    rw [mem_ball_zero_iff] at hx ⊢
    rw [norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (by norm_num))).trans_lt hx
  have hstep : ∀ k : ℕ, e ((2⁻¹ : ℝ) ^ k • x) = g ((2⁻¹ : ℝ) ^ k • x) → e x = g x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro h
      apply ih
      have : (2⁻¹ : ℝ) ^ k • x = (2⁻¹ : ℝ) ^ (k + 1) • x + (2⁻¹ : ℝ) ^ (k + 1) • x := by
        rw [← add_smul, pow_succ]; congr 1; ring
      rw [this, map_add, hg _ (hball _) _ (hball _), h]
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const x
  obtain ⟨k, hk⟩ := (ht.eventually he).exists
  exact hstep k hk

end Additive

theorem eventuallyEq_of_additive_of_hasFDerivAt {ζ : E → E'} {T : E →L[ℂ] E'} (hT : HasFDerivAt ζ T 0)
    (hζ : ∀ᶠ p in 𝓝 (0 : E × E), ζ (p.1 + p.2) = ζ p.1 + ζ p.2) : ζ =ᶠ[𝓝 0] T := by
  obtain ⟨l, hl⟩ := exists_addMonoidHom_eventuallyEq (V := E) hζ
  have h1 : HasFDerivAt l T 0 := hT.congr_of_eventuallyEq hl
  have hc : Continuous l := continuous_of_continuousAt_zero l h1.continuousAt
  have h2 : (l.toRealLinearMap hc) = T.restrictScalars ℝ :=
    (l.toRealLinearMap hc).hasFDerivAt.unique (h1.restrictScalars ℝ)
  filter_upwards [hl] with v hv
  rw [← hv]
  exact DFunLike.congr_fun h2 v

end GlobalTheory.RelExp
