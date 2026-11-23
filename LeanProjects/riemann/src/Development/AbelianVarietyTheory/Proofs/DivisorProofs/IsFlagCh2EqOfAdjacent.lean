import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricCombUnitOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityInequalityLogOneSubCosSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMetricNormProductFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecDetDualTensorSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricRestrictionVanishingLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfCompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionMetricCompatStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.AdjFlag

open GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem height_eq {D : ℕ} (hX : IsArithVar p D) {L M : HermLB p} {h h' : X → ℝ}
    (H : L.IsArithHeight h) (H' : M.IsArithHeight h') {Z : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] (e : (L.restr i).Isometric (M.restr i)) :
    h (i (genericPoint Z)) = h' (i (genericPoint Z)) := by
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, d, hd⟩
  · obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    have ⟨w, hw, _⟩ := e
    have e' : topSelfIntersection (ZMod ℓ) (L.B.pull i) d = topSelfIntersection (ZMod ℓ) (M.B.pull i) d :=
      interNum_congr_lbIso _ _ (fun _ => (L.restr i).isLB) (fun _ => (M.restr i).isLB)
        fun _ => ⟨w, hw⟩
    rw [H.vertical Z i (ZMod ℓ) d hd, H'.vertical Z i (ZMod ℓ) d hd, e']
  · have hZ := hX.of_isClosedImmersion i hc hd
    exact (e.isSelfInter hZ (H.isSelfInter_restrict hX i rfl)).unique hZ
      (H'.isSelfInter_restrict hX i rfl)

theorem selfInter_sub [IsIntegral X] [IsLocallyNoetherian X] (hC : Published.ArCalc)
    (hX : IsArithVar p 1) {L Q L' Q' : HermLB p} (e : (L.tens Q).Isometric (L'.tens Q'))
    {x y x' y' a a' : ℝ} (hx : L.IsSelfInter x) (hy : Q.IsSelfInter y) (hx' : L'.IsSelfInter x')
    (hy' : Q'.IsSelfInter y') (ha : (L'.dual.tens Q).IsInter L a)
    (ha' : (L'.dual.tens Q).IsInter L' a') : x + y - x' - y' = -2 * (a - a') := by
  let T : Fin 3 → HermLB p := ![L, Q, L']
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k X p 1 hX).2 (Fin 3) T).1
  have e' : L.icls + Q.icls = L'.icls + Q'.icls := HermLB.icls_eq_iff.2 e
  have c₀ : (comb T ![1, 0, 0]).Isometric L := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₁ : (comb T ![0, 1, 0]).Isometric Q := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₂ : (comb T ![0, 0, 1]).Isometric L' := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T])
  have c₃ : (comb T ![1, 1, -1]).Isometric Q' := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T, e'])
  have c₄ : (comb T ![0, 1, -1]).Isometric (L'.dual.tens Q) := HermLB.icls_eq_iff.1 (by
    simp [icls_comb, Fin.sum_univ_three, T, HermLB.icls_tens, HermLB.icls_dual, add_comm])
  have I₀ := HermLB.isInter_of_comb hC.arExists hC.arMix hC.arIso hX hΨ c₄ c₀
  have I₂ := HermLB.isInter_of_comb hC.arExists hC.arMix hC.arIso hX hΨ c₄ c₂
  rw [hx.unique hX (c₀.isSelfInter hX (hΨ.1 _)), hy.unique hX (c₁.isSelfInter hX (hΨ.1 _)),
    hx'.unique hX (c₂.isSelfInter hX (hΨ.1 _)), hy'.unique hX (c₃.isSelfInter hX (hΨ.1 _)),
    ha.unique hX I₀, ha'.unique hX I₂, neg_mul, two_mul, ← map_add, ← map_sub, ← map_sub,
    ← map_sub, ← map_add, ← map_neg]
  congr 1
  simp [lin, Fin.sum_univ_three]
  ring

section Dens

variable [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)]
  {ρ ρ' : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem total_add_sub (hR : Nonempty (AnRead p σ 1)) (h : IsDens ρ) (h' : IsDens ρ') :
    total (fun c y => ρ c y + ρ' c y) = total ρ + total ρ' ∧
      total (fun c y => ρ c y - ρ' c y) = total ρ - total ρ' := by
  obtain ⟨ν, w, _, -, h₁, h₂⟩ := T.finite_measure_density_exists k X p σ hR
  obtain ⟨g, hg, e⟩ := h₁ ρ h
  obtain ⟨g', hg', e'⟩ := h₁ ρ' h'
  have i := hg.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  have i' := hg'.integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  rw [(h₂ ρ g hg e).2, (h₂ ρ' g' hg' e').2, ← integral_add i i', ← integral_sub i i']
  exact ⟨(h₂ _ _ (hg.add hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.add_apply, add_mul]).2,
    (h₂ _ _ (hg.sub hg') fun c y hy => by rw [e c y hy, e' c y hy, Pi.sub_apply, sub_mul]).2⟩

end Dens

theorem form_frame_pos {L : X.Modules} (g : Met p σ L 1) {U : X.Opens} {t : Γ(L, U)}
    (ht : IsFrame fun _ : Fin 1 => t) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    0 < (g.form t t y).re := by
  have := g.form_frame ⟨U, _, ht⟩ hy 0 0
  rw [show g.form t t y = _ from this]
  exact (Complex.pos_iff.1 ((g.posDef ⟨U, _, ht⟩ y hy).diag_pos)).1

theorem exists_frames {L L' : X.Modules} (hL : IsVB L 1) (hL' : IsVB L' 1) (y : CxPts p σ) :
    ∃ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), (IsFrame fun _ : Fin 1 => t) ∧
      (IsFrame fun _ : Fin 1 => t') ∧ y ∈ ptsIn p σ U := by
  have key {F : X.Modules} (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) :
      IsFrame fun _ : Fin 1 => Twist.resM F h (c.e 0) := fun V hV => by
    convert c.isFrame V (hV.trans h) using 3
    funext i
    rw [Twist.resM_resM, Subsingleton.elim i 0]
  exact ⟨_, _, _, key (hL.pick y) inf_le_left, key (hL'.pick y) inf_le_right,
    mem_ptsIn_inf.2 ⟨hL.mem_pick y, hL'.mem_pick y⟩⟩

section RankTwo

variable {V L Q L' Q' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0}
  {l' : L' ⟶ V} {m' : V ⟶ Q'} {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
  (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')

include hl hl' hL' in

theorem div_eq_one_sub (h : Met p σ V (1 + 1)) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v)
    {U : X.Opens} {t : Γ(L, U)} {t' : Γ(L', U)} (ht : IsFrame fun _ : Fin 1 => t)
    (ht' : IsFrame fun _ : Fin 1 => t') {y : CxPts p σ} (hU : y ∈ ptsIn p σ U) :
    ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t') ((l' ≫ m).app U t') y).re /
      ((h.restrict hl' hL').form t' t' y).re = 1 - v y := by
  have p₁ := form_frame_pos (h.restrict hl hL) ht hU
  have p₂ := form_frame_pos (h.restrict hl' hL') ht' hU
  have p₃ : ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t') ((l' ≫ m).app U t')
      y).re * (h.form (l.app U t) (l.app U t) y).re =
      (h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2 :=
    T.quotient_metric_norm_product_formula k X p σ (.mk l m w) h hS hL hQ U t (l'.app U t') ht y hU
  rw [div_eq_iff p₂.ne']
  rw [h.form_restrict hl hL t t hU] at p₁
  rw [h.form_restrict hl' hL' t' t' hU]
  refine mul_right_cancel₀ p₁.ne' (p₃.trans ?_)
  rw [hv U t t' y hU]
  ring

theorem green_log [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (hR : Nonempty (AnRead p σ 1)) (h : Met p σ V (1 + 1))
    (H : h.IsCInf) {S : Set (CxPts p σ)} (ho : IsOpen S) (hf : Sᶜ.Finite) {f : CxPts p σ → ℝ}
    (hn : ∀ y ∈ S, ∀ (U : X.Opens) (t : Γ(L', U)), (IsFrame fun _ : Fin 1 => t) → y ∈ ptsIn p σ U →
      0 < ((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t) ((l' ≫ m).app U t) y).re ∧
      f y = Real.log (((Met.quot (S := .mk l m w) h hS hL hQ).form ((l' ≫ m).app U t)
        ((l' ≫ m).app U t) y).re / ((h.restrict hl' hL').form t t y).re) / 2)
    (j₁ : (h.restrict hl hL).detWeight.ChernIntegrableOn 1 S f)
    (j₂ : (h.restrict hl' hL').detWeight.ChernIntegrableOn 1 S f) :
    2 * ((h.restrict hl hL).detWeight.chernInt 1 S f - (h.restrict hl' hL').detWeight.chernInt 1 S f) =
      (Met.bcMeas (S := .mk l m w) h hS hL hQ Set.univ).toReal -
        (Met.bcMeas (S := .mk l' m' w') h hS' hL' hQ' Set.univ).toReal := by
  obtain ⟨v, hv, hc, hb⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ h l l' H hl hl' hL hL'
  have d₁ := isDens_bcDens (S := .mk l m w) hS hL hQ H
  have d₂ := isDens_bcDens (S := .mk l' m' w') hS' hL' hQ' H
  rw [Weight.ChernIntegrableOn, (chernPart_eq _).1, (chernPart_eq _).2] at j₁ j₂
  rw [← total_bcDens (S := .mk l m w) hS hL hQ H,
    ← total_bcDens (S := .mk l' m' w') hS' hL' hQ' H, ← (total_add_sub hR d₁ d₂).2,
    Weight.chernInt, Weight.chernInt, (chernPart_eq _).1, (chernPart_eq _).2,
    (chernPart_eq _).1, (chernPart_eq _).2]
  refine T.density_inequality_log_one_sub_cosSq k X p σ hR _ _ _ ((T.chernDens_detWeight_eq_neg_levi_log k X p σ).1 _ _ (H.restrict hl hL).detWeight)
    ((T.chernDens_detWeight_eq_neg_levi_log k X p σ).1 _ _ (H.restrict hl' hL').detWeight) (d₁.sub d₂) v f S hc hb ho hf
    (fun y hy => ?_) j₁.1 j₁.2 j₂.1 j₂.2
    (T.line_pair_extension_cosSq_bound k X p σ hR V L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H v hv)
  obtain ⟨U, t, t', ht, ht', hU⟩ := exists_frames hL hL' y
  obtain ⟨n₁, n₂⟩ := hn y hy U t' ht' hU
  have e := div_eq_one_sub hS hL hQ hL' hl hl' h hv ht ht' hU
  have := div_pos n₁ (form_frame_pos (h.restrict hl' hL') ht' hU)
  rw [e] at this n₂
  exact ⟨by linarith, n₂⟩

variable [IsIntegral X] {h : VMetric p V (1 + 1)} (H : h.IsCInf)

theorem rank_two (hC : Published.ArCalc) (hX : IsRegSurf p) {x y x' y' : ℝ}
    (hx : (VMetric.det (H.restrict hl hL)).IsSelfInter x)
    (hy : (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)).IsSelfInter y)
    (hx' : (VMetric.det (H.restrict hl' hL')).IsSelfInter x')
    (hy' : (VMetric.det (VMetric.IsCInf.quot (S := .mk l' m' w') hS' hL' hQ' H)).IsSelfInter y') :
    x + y - VMetric.bcInt (S := .mk l m w) h hS hL hQ =
      x' + y' - VMetric.bcInt (S := .mk l' m' w') h hS' hL' hQ' := by
  have hA := hX.toIsArithVar
  by_cases hs : l' ≫ m = 0
  · obtain ⟨e, he⟩ := T.iso_of_equal_sublines_shortExact X V L Q L' Q' l m w l' m' w' hS hS' hQ hQ' hs
    obtain ⟨e₁, e₂⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk l' m' w') (.mk l m w) 1 1 h h H H hS' hS hL' hQ' hL hQ
      e (Iso.refl V) (he.trans (Category.comp_id _).symm) fun _ _ _ _ _ _ => rfl
    have e₃ := T.det_metric_isometric_of_isometry k X p L' L 1 (h.restrict hl' hL') (h.restrict hl hL) (H.restrict hl' hL')
      (H.restrict hl hL) e fun σ U s t y hy => by
        refine ((h.met σ).form_restrict hl hL _ _ hy).trans
          (Eq.trans ?_ ((h.met σ).form_restrict hl' hL' s t hy).symm)
        rw [← he]
        rfl
    rw [e₂, hx.unique hA (e₃.isSelfInter hA hx'), hy.unique hA (e₁.isSelfInter hA hy')]
  have := hA.isLocallyNoetherian
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  have e₀ := fun a a' => selfInter_sub (a := a) (a' := a') hC hA
    ((T.det_metric_shortExact_isometric k X p (.mk l m w) 1 1 h H hS hL hQ hl).trans
      (T.det_metric_shortExact_isometric k X p (.mk l' m' w') 1 1 h H hS' hL' hQ' hl').symm) hx hy hx' hy'
  generalize (VMetric.det (H.restrict hl' hL')).dual.tens (VMetric.det HQ) = P at *
  obtain ⟨a, ha⟩ := (isInter_calculus hC k X p hA P P (VMetric.det (H.restrict hl hL))).1
  obtain ⟨a', ha'⟩ := (isInter_calculus hC k X p hA P P (VMetric.det (H.restrict hl' hL'))).1
  replace e₀ := e₀ a a' ha ha'
  obtain ⟨g, G, ha⟩ := ha
  obtain ⟨g', G', ha'⟩ := ha'
  obtain ⟨i₁, rfl⟩ := ha r hr
  obtain ⟨i₂, rfl⟩ := ha' r hr
  have e₁ : ∑ᶠ z, ((P.div hr).mult z : ℝ) * g z = ∑ᶠ z, ((P.div hr).mult z : ℝ) * g' z :=
    finsum_congr fun z => by
      by_cases hz : (P.div hr).mult z = 0
      · simp [hz]
      obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      rw [height_eq hA G G' i (T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i
        (hv _ (CartierDiv.mem_supp_of_mult_ne_zero hz)))]
  have key (σ : k →+* ℂ) :=
    have := hA.compactSpace σ
    have := CxPts.secondCountableTopology_of_isProjOver σ hA.isProjOver
    have := CxPts.t2Space_cxPts_of_isProjOver σ hA.isProjOver
    green_log hS hS' hL hQ hL' hQ' hl hl' ((RegGenSmooth.genSmooth_of_isRegSurf k X p hX).1 σ)
      (h.met σ) (H σ) (isOpen_offSupp (P.div hr))
      (SurfacePoints.finite_compl_ptsIn k X p hA _ (P.div hr).genericPoint_notMem_supp σ)
      (hn σ) (i₁ σ) (i₂ σ)
  have := hA.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have e₂ := Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => key σ
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at e₂
  rw [HermLB.archInt, HermLB.archInt, finsum_eq_sum_of_fintype (α := k →+* ℂ),
    finsum_eq_sum_of_fintype (α := k →+* ℂ)] at e₀
  rw [VMetric.bcInt, VMetric.bcInt, finsum_eq_sum_of_fintype (α := k →+* ℂ),
    finsum_eq_sum_of_fintype (α := k →+* ℂ)]
  change 2 * (∑ σ, ((VMetric.det (H.restrict hl hL)).φ σ).chernInt 1 _ _ -
    ∑ σ, ((VMetric.det (H.restrict hl' hL')).φ σ).chernInt 1 _ _) = _ at e₂
  linarith

end RankTwo

theorem isSelfInter_congr [IsIntegral X] {E : X.Modules} {r : ℕ} {h h' : VMetric p E r} (e : h = h')
    {H : h.IsCInf} {H' : h'.IsCInf} {x : ℝ} (hx : (VMetric.det H').IsSelfInter x) :
    (VMetric.det H).IsSelfInter x := by
  subst e
  exact hx

section ThreeStep

variable [IsIntegral X] {A B V : X.Modules} {u : A ⟶ B} {q₂ : B ⟶ V} {w₂ : u ≫ q₂ = 0}
  (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) {n : ℕ} (hA : IsVB A n) (hV : IsVB V (1 + 1))
  {h : VMetric p B (n + 1 + 1)} (H : h.IsCInf)
  {M L Q : X.Modules} {f : A ⟶ M} {g : M ⟶ B} {q₀ : M ⟶ L} {q₁ : B ⟶ Q} {w₀ : f ≫ q₀ = 0}
  {w₁ : g ≫ q₁ = 0} (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact)
  (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hM : IsVB M (n + 1)) (hL : IsVB L 1)
  (hQ : IsVB Q 1) (hg : IsSubbundle g)

omit [IsIntegral X] in
include H in

theorem three_step (hX : IsRegSurf p) (hu : f ≫ g = u) :
    ∃ (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact)
      (hl : IsSubbundle l),
      (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL =
        VMetric.quot (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧
      VMetric.quot (S := .mk l m w₃)
          (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ =
        VMetric.quot (S := .mk g q₁ w₁) h hS₁ hM hQ ∧
      VMetric.bcInt (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
          VMetric.bcInt (S := .mk g q₁ w₁) h hS₁ hM hQ =
        VMetric.bcInt (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV +
          VMetric.bcInt (S := .mk l m w₃)
            (VMetric.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ := by
  obtain ⟨l, m, w₃, hS₃, e₁, e₂⟩ := T.exists_shortExact_of_composition X A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ hu
  have hl : IsSubbundle l := isSubbundle_of_shortExact hS₃ hQ
  have key (σ : k →+* ℂ) := T.shortExact_composition_compatibility k X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁ hS₂ l m
    w₃ hS₃ n hA hM hL hQ hV hg (h.met σ) hu e₁ e₂ hl
  refine ⟨l, m, w₃, hS₃, hl, VMetric.ext (funext fun σ => (key σ).1),
    VMetric.ext (funext fun σ => (key σ).2), ?_⟩
  have hX' := hX.toIsArithVar
  have := hX'.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [VMetric.bcInt, finsum_eq_sum_of_fintype, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := hX'.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX'.isProjOver
  have hR := (RegGenSmooth.genSmooth_of_isRegSurf k X p hX).1 σ
  have H₀ := (H σ).restrict hg hM
  have H₃ := Met.IsCInf.quot (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ)
  have t₀ := total_bcDens (S := .mk f q₀ w₀) hS₀ hA hL H₀
  have t₁ := total_bcDens (S := .mk g q₁ w₁) hS₁ hM hQ (H σ)
  have t₂ := total_bcDens (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ)
  have t₃ := total_bcDens (S := .mk l m w₃) hS₃ hL hQ H₃
  have s₁ := (total_add_sub hR (isDens_bcDens (S := .mk f q₀ w₀) hS₀ hA hL H₀)
    (isDens_bcDens (S := .mk g q₁ w₁) hS₁ hM hQ (H σ))).1
  have s₂ := (total_add_sub hR
    (isDens_bcDens (S := .mk u q₂ w₂) (r := n) (s := 1 + 1) hS₂ hA hV (H σ))
    (isDens_bcDens (S := .mk l m w₃) hS₃ hL hQ H₃)).1
  rw [t₀, t₁] at s₁
  rw [t₂, t₃] at s₂
  exact s₁.symm.trans ((total_congr (T.shortExact_composition_metric_compat k X p σ A M B L Q V f g u q₀ q₁ q₂ w₀ w₁ w₂ hS₀ hS₁
    hS₂ l m w₃ hS₃ n hA hM hL hQ hV hg (h.met σ) hu e₁ e₂ (H σ))).trans s₂)

variable {M' L' Q' : X.Modules} {f' : A ⟶ M'} {g' : M' ⟶ B} {q₀' : M' ⟶ L'} {q₁' : B ⟶ Q'}
  {w₀' : f' ≫ q₀' = 0} {w₁' : g' ≫ q₁' = 0} (hS₀' : (ShortComplex.mk f' q₀' w₀').ShortExact)
  (hS₁' : (ShortComplex.mk g' q₁' w₁').ShortExact) (hM' : IsVB M' (n + 1)) (hL' : IsVB L' 1)
  (hQ' : IsVB Q' 1) (hg' : IsSubbundle g')

theorem two_steps (hC : Published.ArCalc) (hX : IsRegSurf p) (hu : f ≫ g = f' ≫ g') {x y x' y' : ℝ}
    (hx : (VMetric.det (VMetric.IsCInf.quot (S := .mk f q₀ w₀) hS₀ hA hL
      (H.restrict hg hM))).IsSelfInter x)
    (hy : (VMetric.det (VMetric.IsCInf.quot (S := .mk g q₁ w₁) hS₁ hM hQ H)).IsSelfInter y)
    (hx' : (VMetric.det (VMetric.IsCInf.quot (S := .mk f' q₀' w₀') hS₀' hA hL'
      (H.restrict hg' hM'))).IsSelfInter x')
    (hy' : (VMetric.det (VMetric.IsCInf.quot (S := .mk g' q₁' w₁') hS₁' hM' hQ' H)).IsSelfInter y') :
    x + y - (VMetric.bcInt (S := .mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL +
        VMetric.bcInt (S := .mk g q₁ w₁) h hS₁ hM hQ) =
      x' + y' - (VMetric.bcInt (S := .mk f' q₀' w₀') (h.restrict hg' hM') hS₀' hA hL' +
        VMetric.bcInt (S := .mk g' q₁' w₁') h hS₁' hM' hQ') := by
  have m₀ : Mono f := hS₀.mono_f
  have m₁ : Mono g := hS₁.mono_f
  have hS₂ : (ShortComplex.mk (f ≫ g) _ (Limits.cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hV : IsVB (Limits.cokernel (f ≫ g)) (1 + 1) := by
    obtain ⟨l, m, w₃, hS₃, -⟩ := T.exists_shortExact_of_composition X A M B L Q _ f g _ q₀ q₁ _ w₀ w₁ _ hS₀ hS₁ hS₂ rfl
    exact (VBExt.isVB_and_cls_det_of_shortExact X _ 1 1 hS₃ hL hQ).1
  obtain ⟨l, m, w₃, hS₃, hl, e₁, e₂, e₃⟩ := three_step hS₂ hA hV H hS₀ hS₁ hM hL hQ hg hX rfl
  obtain ⟨l', m', w₃', hS₃', hl', e₁', e₂', e₃'⟩ :=
    three_step hS₂ hA hV H hS₀' hS₁' hM' hL' hQ' hg' hX hu.symm
  have HV := VMetric.IsCInf.quot (S := .mk (f ≫ g) _ (Limits.cokernel.condition _)) (r := n)
    (s := 1 + 1) hS₂ hA hV H
  have aux {a a' b c c' d d' : ℝ} (e : d = b + c) (e' : d' = b + c') (k : a - c = a' - c') :
      a - d = a' - d' := by linarith
  exact aux e₃ e₃' (rank_two hS₃ hS₃' hL hQ hL' hQ' hl hl' HV hC hX (isSelfInter_congr e₁ hx)
    (isSelfInter_congr e₂ hy) (isSelfInter_congr e₁' hx') (isSelfInter_congr e₂' hy'))

end ThreeStep

section Flags

open VMetric

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) {fl fl' : Vert.Flag E r}

noncomputable abbrev stepBc (h : VMetric p E r) (fl : Vert.Flag E r) (i : Fin r) : ℝ :=
  (h.stepMet fl i).bcInt (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)

theorem isIsometry_restrict {F F' : X.Modules} {s : ℕ} {i : F ⟶ E} {i' : F' ⟶ E}
    (hi : IsSubbundle i) (hi' : IsSubbundle i') (hF : IsVB F s) (hF' : IsVB F' s) (e : F ≅ F')
    (he : e.hom ≫ i' = i) : (h.restrict hi hF).IsIsometry (h.restrict hi' hF') e :=
  fun σ U s t y hy => by
    refine ((h.met σ).form_restrict hi' hF' _ _ hy).trans
      (Eq.trans ?_ ((h.met σ).form_restrict hi hF s t hy).symm)
    rw [← he]
    rfl

theorem step_eq {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
    (grLB fl i H).Isometric (grLB fl' i H) ∧ stepBc h fl i = stepBc h fl' i := by
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₁, h₁⟩ := h₁
  refine T.det_metric_shortExact_iso_isometric k X p (stepSeq fl i) (stepSeq fl' i) i 1 (h.stepMet fl i) (h.stepMet fl' i)
    (H.restrict _ _) (H.restrict _ _) _ _ _ _ _ _ e₀ e₁ ?_ (isIsometry_restrict _ _ _ _ e₁ h₁)
  rw [← cancel_mono (fl'.ι i.succ)]
  simp only [Category.assoc, Vert.Flag.step_ι, h₀, h₁]

theorem mid_eq [IsIntegral X] (hC : Published.ArCalc) (hX : IsRegSurf p) {n : ℕ} (hn : n + 1 < r)
    (h₀ : fl.SameStep fl' (Fin.castSucc ⟨n, by omega⟩)) (h₂ : fl.SameStep fl' (Fin.succ ⟨n + 1, hn⟩))
    {x y x' y' : ℝ} (hx : (grLB fl ⟨n, by omega⟩ H).IsSelfInter x)
    (hy : (grLB fl ⟨n + 1, hn⟩ H).IsSelfInter y) (hx' : (grLB fl' ⟨n, by omega⟩ H).IsSelfInter x')
    (hy' : (grLB fl' ⟨n + 1, hn⟩ H).IsSelfInter y') :
    x + y - (stepBc h fl ⟨n, by omega⟩ + stepBc h fl ⟨n + 1, hn⟩) =
      x' + y' - (stepBc h fl' ⟨n, by omega⟩ + stepBc h fl' ⟨n + 1, hn⟩) := by
  have hA := hX.toIsArithVar
  set i₀ : Fin r := ⟨n, by omega⟩
  set i₁ : Fin r := ⟨n + 1, hn⟩
  obtain ⟨e₀, h₀⟩ := h₀
  obtain ⟨e₂, h₂⟩ := h₂
  let g : fl.F i₀.succ ⟶ fl.F i₁.succ := fl.step i₁
  let f' : fl.F i₀.castSucc ⟶ fl'.F i₀.succ := e₀.hom ≫ fl'.step i₀
  let g' : fl'.F i₀.succ ⟶ fl.F i₁.succ := fl'.step i₁ ≫ e₂.inv
  let q' : fl.F i₁.succ ⟶ fl'.gr i₁ := e₂.hom ≫ fl'.π i₁
  have w₀' : f' ≫ fl'.π i₀ = 0 := by
    simp only [f', Category.assoc]
    rw [show fl'.step i₀ ≫ fl'.π i₀ = 0 from Limits.cokernel.condition _, Limits.comp_zero]
  have w₁' : g' ≫ q' = 0 := by
    simp only [g', q', Category.assoc, Iso.inv_hom_id_assoc]
    exact Limits.cokernel.condition _
  have hS₀' : (ShortComplex.mk f' _ w₀').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₀) e₀.symm (Iso.refl _) (Iso.refl _)
      (by simp [f']) (by simp)) (stepSeq_shortExact fl' i₀)
  have hS₁' : (ShortComplex.mk g' q' w₁').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl' i₁)
      (Iso.refl _) e₂.symm (Iso.refl _)
      (by simp [g']) (by simp [q'])) (stepSeq_shortExact fl' i₁)
  have hg : IsSubbundle g := isSubbundle_of_shortExact (stepSeq_shortExact fl i₁) (fl.isVB_gr i₁)
  have hg' : IsSubbundle g' := isSubbundle_of_shortExact hS₁' (fl'.isVB_gr i₁)
  have gι : g ≫ fl.ι i₁.succ = fl.ι i₀.succ := fl.step_ι i₁
  have gι' : g' ≫ fl.ι i₁.succ = fl'.ι i₀.succ := by
    rw [← h₂, Category.assoc, Iso.inv_hom_id_assoc]
    exact fl'.step_ι i₁
  have hu : fl.step i₀ ≫ g = f' ≫ g' := by
    rw [← cancel_mono (fl.ι i₁.succ), Category.assoc, Category.assoc, gι, gι', fl.step_ι,
      Category.assoc, fl'.step_ι, h₀]
  have HB : (h.stepMet fl i₁).IsCInf := H.restrict _ _
  have res {F : X.Modules} {a : F ⟶ fl.F i₁.succ} {b : F ⟶ E} (ha : IsSubbundle a)
      (hb : IsSubbundle b) (hF : IsVB F (n + 1)) (e : a ≫ fl.ι i₁.succ = b) :
      ((h.stepMet fl i₁).restrict ha hF).IsIsometry (h.restrict hb hF) (Iso.refl F) :=
    fun σ U s t y hy => by
      refine ((h.met σ).form_restrict hb hF _ _ hy).trans (Eq.trans ?_
        ((((h.stepMet fl i₁).met σ).form_restrict ha hF s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle i₁.succ) (fl.isVB i₁.succ) _ _ hy)).symm)
      rw [← e]
      rfl
  obtain ⟨a₁, b₁⟩ := T.det_metric_shortExact_iso_isometric k X p (stepSeq fl i₀) (stepSeq fl i₀) n 1 _ (h.stepMet fl i₀)
    (HB.restrict hg (fl.isVB i₀.succ)) (H.restrict _ _) (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₀) (fl.isVB i₀.castSucc) (fl.isVB_gr i₀) (fl.isVB i₀.castSucc)
    (fl.isVB_gr i₀) (Iso.refl _) (Iso.refl _) (by simp) (res hg _ _ gι)
  obtain ⟨a₂, b₂⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk f' _ w₀') (stepSeq fl' i₀) n 1 _ (h.stepMet fl' i₀)
    (HB.restrict hg' (fl'.isVB i₀.succ)) (H.restrict _ _) hS₀'
    (stepSeq_shortExact fl' i₀) (fl.isVB i₀.castSucc) (fl'.isVB_gr i₀) (fl'.isVB i₀.castSucc)
    (fl'.isVB_gr i₀) e₀ (Iso.refl _) (Category.comp_id _).symm (res hg' _ _ gι')
  obtain ⟨a₃, b₃⟩ := T.det_metric_shortExact_iso_isometric k X p (.mk g' q' w₁') (stepSeq fl' i₁) (n + 1) 1 _ (h.stepMet fl' i₁)
    HB (H.restrict _ _) hS₁' (stepSeq_shortExact fl' i₁) (fl'.isVB i₀.succ) (fl'.isVB_gr i₁)
    (fl'.isVB i₁.castSucc) (fl'.isVB_gr i₁) (Iso.refl _) e₂ (by simp [g'])
    (isIsometry_restrict _ _ _ _ e₂ h₂)
  have key := two_steps (fl.isVB i₀.castSucc) HB (stepSeq_shortExact fl i₀)
    (stepSeq_shortExact fl i₁) (fl.isVB i₀.succ) (fl.isVB_gr i₀) (fl.isVB_gr i₁) hg hS₀' hS₁'
    (fl'.isVB i₀.succ) (fl'.isVB_gr i₀) (fl'.isVB_gr i₁) hg' hC hX hu
    (a₁.symm.isSelfInter hA hx) hy (a₂.symm.isSelfInter hA hx') (a₃.symm.isSelfInter hA hy')
  exact (congrArg (fun t => x + y - (t + stepBc h fl i₁)) b₁).symm.trans
    (key.trans (congrArg₂ (fun s t => x' + y' - (s + t)) b₂ b₃))

theorem sameStep_of_end {j : Fin (r + 1)} (hj : j = 0 ∨ j = Fin.last r) : fl.SameStep fl' j := by
  rcases hj with rfl | rfl
  · have z := isVB_zero_iff.1 (fl.isVB 0)
    exact ⟨z.iso (isVB_zero_iff.1 (fl'.isVB 0)), z.eq_of_src _ _⟩
  · have := fl.isIso_last
    have := fl'.isIso_last
    exact ⟨asIso (fl.ι _) ≪≫ (asIso (fl'.ι _)).symm, by simp⟩

end Flags

theorem isFlagCh2_eq_of_adjacent : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    (p : X ⟶ Sp k) [IsIntegral X], IsRegSurf p → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r)
    (H : h.IsCInf) (fl fl' : Vert.Flag E r), fl.Adjacent fl' → ∀ a b : ℝ,
    VMetric.IsFlagCh2 H fl a → VMetric.IsFlagCh2 H fl' b → a = b := by
  rintro hC k _ X p _ hX E r h H fl fl' ⟨j, hj⟩ _ _ ⟨-, x, hx, rfl⟩ ⟨-, x', hx', rfl⟩
  have hA := hX.toIsArithVar
  have same {i : Fin r} (h₀ : fl.SameStep fl' i.castSucc) (h₁ : fl.SameStep fl' i.succ) :
      x i - stepBc h fl i - (x' i - stepBc h fl' i) = 0 := by
    obtain ⟨e₁, e₂⟩ := step_eq H h₀ h₁
    rw [e₂, (e₁.isSelfInter hA (hx i)).unique hA (hx' i), sub_self]
  suffices e : ∑ i, (x i - stepBc h fl i - (x' i - stepBc h fl' i)) = 0 by
    simp only [Finset.sum_sub_distrib] at e
    rw [← Finset.sum_div, ← Finset.sum_div, VMetric.flagBc, VMetric.flagBc]
    linarith
  by_cases he : j = 0 ∨ j = Fin.last r
  · have all (i) : fl.SameStep fl' i := by
      by_cases hi : i = j
      · exact hi ▸ sameStep_of_end he
      · exact hj i hi
    exact Finset.sum_eq_zero fun i _ => same (all _) (all _)
  obtain ⟨_ | n, hn⟩ := j
  · exact absurd (.inl rfl) he
  have hn' : n + 1 < r := by
    have : n + 1 ≠ r := fun e => he (.inr (Fin.ext e))
    omega
  rw [Fintype.sum_eq_add (⟨n, by omega⟩ : Fin r) (⟨n + 1, hn'⟩ : Fin r) (by simp) fun i hi => same (i := i)
    (hj _ fun e => hi.2 (Fin.ext (congrArg Fin.val e :)))
    (hj _ fun e => hi.1 (Fin.ext (Nat.succ_injective (congrArg Fin.val e :))))]
  have := mid_eq H hC hX hn' (hj _ (by simp [Fin.ext_iff])) (hj _ (by simp [Fin.ext_iff]))
    (hx _) (hx _) (hx' _) (hx' _)
  linarith

end GlobalTheory.AdjFlag
