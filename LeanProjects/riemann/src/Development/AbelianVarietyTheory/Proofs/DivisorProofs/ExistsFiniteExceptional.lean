import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExistsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory.FlagPull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open MeasureTheory VMetric
open scoped ENNReal

theorem exists_open_finite_etale : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q →
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 →
    ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧
      (π.app U).hom.Etale ∧
      (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) =
        π.residueDegree (genericPoint Y) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd
  obtain ⟨U₁, x, hU₁, hg₁, hx⟩ := GlobalTheory.T.etale_coordinate_near_generic_point k X p hp
  obtain ⟨U, hle, hU, hgU, hV, h₁, h₂, h₃⟩ := GlobalTheory.T.finite_affine_neighbourhood_exists k X p Y q hp hq π hπ hg hd U₁ hg₁
  have hres := Scheme.Hom.etale_appLE (𝟙 X) hU₁ hU hle
  refine ⟨U, fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a), hU, hgU, ?_, hV, h₁, h₂, h₃⟩
  have hw : 𝟙 X ≫ p = p ≫ spMap (RingHom.id k) := by
    rw [show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id, Category.id_comp]
  have e : (MvPolynomial.eval₂Hom (algX p U) fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a)) =
      (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom.comp (MvPolynomial.eval₂Hom (algX p U₁) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := p) (φ := 𝟙 X)
        (σ := RingHom.id k) hw (V := U₁) (W := U) hle) a
      simpa using this.symm
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ hx hres

theorem exists_finite_exceptional : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ σ : k →+* ℂ,
    ∃ T : Set (CxPts p σ), T.Finite ∧ (PtsOver.map π hπ (spMap σ) ⁻¹' T).Finite ∧
      (∀ x ∉ T, (PtsOver.map π hπ (spMap σ) ⁻¹' {x}).encard = π.residueDegree (genericPoint Y)) ∧
      ∀ z, PtsOver.map π hπ (spMap σ) z ∉ T → ∃ (c : AlgChart p σ 1) (c' : AlgChart q σ 1),
        z ∈ c'.e.source ∧ PtsOver.map π hπ (spMap σ) z ∈ c.e.source ∧
        ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source →
          c'.e w = c.e (PtsOver.map π hπ (spMap σ) w) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd σ
  obtain ⟨U, x, hU, hgU, hx, hV, hfin, het, hr⟩ := exists_open_finite_etale k X p Y q hp hq π hπ hg hd
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have hgV : genericPoint Y ∈ π ⁻¹ᵁ U := show π (genericPoint Y) ∈ U from hg ▸ hgU
  set m := PtsOver.map π hπ (spMap σ) with hm
  have hmem (z : CxPts q σ) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := Iff.rfl
  have hCx (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
    have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
      rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
    have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
      (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [hCx]
    · simp
  have hx' : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)).Etale := by
    rw [hcx]
    exact RingHom.Etale.stableUnderComposition _ _ hx het
  refine ⟨(ptsIn p σ U)ᶜ, GlobalTheory.T.complex_points_off_open_finite k X p hp U hgU σ, GlobalTheory.T.complex_points_off_open_finite k Y q hq _ hgV σ, fun y hy => ?_, fun z hz => ?_⟩
  · have hy' : y ∈ ptsIn p σ U := not_not.1 hy
    have hc := GlobalTheory.T.etale_fibre_embeddings_card Γ(X, U) Γ(Y, π ⁻¹ᵁ U) (π.app U).hom hfin het (evHom hy')
    rw [hr] at hc
    rw [← hc]
    have hz (z : m ⁻¹' {y}) : z.1 ∈ ptsIn q σ (π ⁻¹ᵁ U) := (hmem z.1).2 (by rw [z.2]; exact hy')
    have hev (z : m ⁻¹' {y}) (a) : ev q σ _ ((π.app U).hom a) z.1 = ev p σ U a y := by
      exact (ev_app π hπ U a z.1).trans (congrArg _ z.2)
    refine Set.encard_congr (Equiv.ofBijective (fun z => ⟨evHom (hz z), RingHom.ext fun a => ?_⟩) ⟨?_, ?_⟩)
    · simp only [RingHom.comp_apply, ← ev_eq]
      exact hev z a
    · intro z z' h
      refine Subtype.ext (Subtype.ext (ext_of_valR hV (hz z) (hz z') fun a => ?_))
      have := RingHom.congr_fun (congrArg Subtype.val h) a
      exact (ev_eq (hz z) a).trans (this.trans (ev_eq (hz z') a).symm)
    · rintro ⟨ψ, hψ⟩
      have hC (a : k) : ψ (algX q (π ⁻¹ᵁ U) a) = σ a := by
        have e₁ : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := hCx a
        rw [e₁]
        exact (RingHom.congr_fun hψ _).trans ((ev_eq hy' _).symm.trans (ev_algX hy' a))
      have hzz := ofHom_mem hV ψ hC
      have hy₂ : m (ofHom hV ψ hC) = y := by
        refine Subtype.ext (ext_of_valR hU hzz hy' fun a => ?_)
        exact ((ev_app π hπ U a _).symm.trans (ev_ofHom hV ψ hC _)).trans
          ((RingHom.congr_fun hψ a).trans (ev_eq hy' a).symm)
      refine ⟨⟨ofHom hV ψ hC, hy₂⟩, Subtype.ext (RingHom.ext fun a => ?_)⟩
      exact (ev_eq hzz a).symm.trans (ev_ofHom hV ψ hC a)
  · have hz' : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := not_not.1 hz
    obtain ⟨c, hc, hcU, hcx⟩ := AlgChart.exists_of_etale hU x hx (σ := σ) (hmem z |>.1 hz')
    obtain ⟨c', hc', hcU', hcx'⟩ := AlgChart.exists_of_etale hV _ hx' hz'
    refine ⟨c, c', hc', hc, fun w hw hw' => ?_⟩
    have key₁ : ∀ (U' : X.Opens) (h : U' = U) (x' : Fin 1 → Γ(X, U')), x' = h ▸ x → ∀ a y,
        ev p σ U' (x' a) y = ev p σ U (x a) y := by
      rintro U' rfl x' rfl a y
      rfl
    have key₂ : ∀ (U' : Y.Opens) (h : U' = π ⁻¹ᵁ U) (x' : Fin 1 → Γ(Y, U')),
        x' = h ▸ (fun a => π.app U (x a)) → ∀ a y,
        ev q σ U' (x' a) y = ev q σ (π ⁻¹ᵁ U) (π.app U (x a)) y := by
      rintro U' rfl x' rfl a y
      rfl
    ext a
    rw [c'.apply_eq w hw a, c.apply_eq _ hw' a, key₂ _ hcU' _ hcx', key₁ _ hcU _ hcx]
    exact ev_app π hπ U _ w

theorem bcMeas_pullStep {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
    {q : Y ⟶ Sp k} [IsIntegral Y] (hp : IsArithVar p 1) (hq : IsArithVar q 1) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)
    {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (σ : k →+* ℂ) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcMeas (stepSeq_shortExact (fl.pull π) i)
        ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) univ =
      π.residueDegree (genericPoint Y) * ((h.stepMet fl i).met σ).bcMeas (stepSeq_shortExact fl i)
        (fl.isVB i.castSucc) (fl.isVB_gr i) univ := by
  obtain ⟨T, hT, hT', hf, hc⟩ := exists_finite_exceptional k X p Y q hp hq π hπ hg hd σ
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  refine GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq 1 one_ne_zero (CxPts p σ) (CxPts q σ) (AlgChart p σ 1) (AlgChart q σ 1) _ _ _ _
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    _ (PtsOver.continuous_map π hπ _) T hT hT' _ hd hf fun z hz => ?_
  · rw [Met.bcDens_trans _ _ _ c c' (H₁ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [Met.bcDens_trans _ _ _ c c' (H₂ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, c', h₁, h₂, h₃⟩ := hc z hz
    exact ⟨c, c', h₁, h₂, fun w hw hw' => ⟨h₃ w hw hw', congrArg _ (bcDens_pullStep H hπ c c' hw hw' h₃)⟩⟩

theorem exists_isSelfInter (hA : Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (hp : IsArithVar p 1) (L : HermLB p) : ∃ x, L.IsSelfInter x := by
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p 1 hp).2 PUnit fun _ => L).1
  exact ⟨_, ((hA.arIso k X p 1 hp).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

theorem isFlagCh2_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r), ∃ fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) r, ∀ a : ℝ, VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) fl' (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl
  refine ⟨fl.pull π, fun a => ?_⟩
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull
