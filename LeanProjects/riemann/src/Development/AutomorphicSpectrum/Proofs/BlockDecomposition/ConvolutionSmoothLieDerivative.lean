import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffIntegralDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionContinuousCompactSupport
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def psi (v : GA E a) : Lie E a := toL (GeneralLinearGroup.map (pInf E) v⁻¹).val

def wt (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g : GA E a) : GA E a → ℂ :=
  Set.indicator {v | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} fun v => F (g * v)

open Classical in

theorem wt_apply (U : Subgroup (GL (Fin a) (Af E))) (F : GA E a → ℂ) (g v : GA E a) :
    wt U F g v = if GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U then F (g * v) else 0 := by
  simp only [wt, Set.indicator_apply, Set.mem_setOf_eq]

def hb (β : Lie E a → ℂ) (q : Lie E a × Lie E a) : ℂ := β (toL (Matrix.of q.2 * Matrix.of q.1))

theorem continuous_psi : Continuous (psi (E := E) (a := a)) :=
  ((Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp ((ContAut.continuous_map_pInf E a).comp continuous_inv))

theorem contDiff_mul_lie : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) i j) =
      fun q => ∑ k, q.2 i k * q.1 k j := by
    funext q; simp [toL, Matrix.mul_apply]
  rw [e]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_snd)).mul
      ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

theorem contDiff_hb {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (hb (E := E) (a := a) β) :=
  hβ.comp contDiff_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_compact_of_mul_mem_tsupport : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β →
    ∀ x₀ ∈ invSet E a, ∃ Kc : Set (Lie E a), IsCompact Kc ∧ Kc ⊆ invSet E a ∧ ∃ N ∈ 𝓝 x₀,
      ∀ y x : Lie E a, x ∈ N → toL (Matrix.of y * Matrix.of x) ∈ tsupport β → y ∈ Kc := by
  intro E _ _ _ a β hβ x₀ hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) x₀ hx₀
  set N := Metric.closedBall x₀ (δ / 2)
  have hNs : N ⊆ invSet E a := (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hNc : IsCompact N := isCompact_closedBall x₀ (δ / 2)
  have hN' := isCompact_setOf_toL_mem (E := E) (a := a) hNc hNs
  have hB' := isCompact_setOf_toL_mem (E := E) (a := a) hβ.compact hβ.support
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Cinf E) => toL (p.1 * p.2⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (continuous_fst.mul continuous_snd.inv)
  refine ⟨_, (hB'.prod hN').image hcont, ?_, N, Metric.closedBall_mem_nhds x₀ (half_pos hδ), ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact val_mem_invSet _
  · intro y x hx hm
    obtain ⟨u, hu⟩ := hNs hx
    obtain ⟨b, hb⟩ := hβ.support hm
    refine ⟨(b, u), ⟨?_, ?_⟩, ?_⟩
    · change toL b.val ∈ tsupport β
      rw [hb]
      exact hm
    · change toL u.val ∈ N
      rw [hu]
      exact hx
    · change toL (b * u⁻¹).val = y
      have e : (b * u⁻¹).val = Matrix.of y := by
        rw [Units.val_mul, hb]
        change Matrix.of y * Matrix.of x * u⁻¹.val = Matrix.of y
        rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [e]
      rfl

theorem measurableSet_integrableOn_wt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) →
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ →
    ∀ Kc : Set (Lie E a), IsCompact Kc → Kc ⊆ invSet E a → ∀ g : GA E a,
      MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ∧
      IntegrableOn (wt U Fl g) {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} μ := by
  intro E _ _ _ a μ _ U hU hUc Fl hFl Kc hKc hKs g
  have hS : IsOpen {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U} :=
    hU.preimage ((ContAut.continuous_map_pFin E a).comp continuous_inv)
  have hm : MeasurableSet {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} :=
    hS.measurableSet.inter (hKc.isClosed.preimage continuous_psi).measurableSet
  refine ⟨hm, ?_⟩
  have hK' := isCompact_setOf_toL_mem (E := E) (a := a) hKc hKs
  have hcont : Continuous fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹ :=
    ((GlobalTheory.CuspQuot.continuous_infGL.comp continuous_fst).mul
      ((GlobalTheory.BlockLevel.continuous_finGL a).comp continuous_snd)).inv
  have hD := (hK'.prod hUc).image hcont
  have hCD : {v : GA E a | GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U ∧ psi v ∈ Kc} ⊆
      (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) => (infGL E a p.1 * finGL E a p.2)⁻¹) ''
        ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    rintro v ⟨hvU, hvK⟩
    exact ⟨(GeneralLinearGroup.map (pInf E) v⁻¹, GeneralLinearGroup.map (pFin E) v⁻¹), ⟨hvK, hvU⟩,
      by simp only [infGL_mul_finGL, inv_inv]⟩
  have hDg := hD.image (continuous_const_mul g)
  have hi : IntegrableOn (fun v => Fl (g * v)) ((fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      (infGL E a p.1 * finGL E a p.2)⁻¹) '' ({y : GL (Fin a) (Cinf E) | toL y.val ∈ Kc} ×ˢ
        (U : Set (GL (Fin a) (Af E))))) μ := by
    have := ((measurePreserving_mul_left μ g).integrableOn_comp_preimage
      (MeasurableEquiv.mulLeft g).measurableEmbedding).2 (hFl.integrableOn_isCompact hDg)
    rwa [Set.preimage_image_eq _ (mul_right_injective g)] at this
  exact (hi.mono_set hCD).indicator hS.measurableSet

theorem convR_tst_mul_infGL (μ : Measure (GA E a)) [μ.IsMulLeftInvariant] (U : Subgroup (GL (Fin a) (Af E)))
    (β : Lie E a → ℂ) (Fl : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    convR μ (tst U β) Fl (g * infGL E a y) = ∫ v, hb β (toL y.val, psi v) * wt U Fl g v ∂μ := by
  rw [← integral_mul_left_eq_self (fun v => hb β (toL y.val, psi v) * wt U Fl g v) (infGL E a y)]
  unfold convR
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hf : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pFin E) v⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  have hi : GeneralLinearGroup.map (pInf E) (infGL E a y * v)⁻¹ = GeneralLinearGroup.map (pInf E) v⁻¹ * y⁻¹ := by
    simp [_root_.mul_inv_rev, map_mul, map_inv]
  show _ = hb β (toL y.val, psi (infGL E a y * v)) * wt U Fl g (infGL E a y * v)
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∈ U := hf ▸ h
    simp only [tst, ker, if_pos h, if_pos h', hb, psi, hi]
    simp [toL, mul_assoc]
  · have h' : GeneralLinearGroup.map (pFin E) (infGL E a y * v)⁻¹ ∉ U := hf ▸ h
    simp only [tst, ker, if_neg h, if_neg h']
    simp
end GlobalTheory.CompanionTheory.SmoothRep.TstConv

namespace GlobalTheory.CompanionTheory.SmoothRep.TstConv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem fderiv_hb_one {β : Lie E a → ℂ} (hβ : ContDiff ℝ ∞ β) (y X : Lie E a) :
    fderiv ℝ (fun q => hb β (q, y)) (oneL E a) X = dTest X β y := by
  have e : (fun q => hb β (q, y)) = β ∘ lmul y := rfl
  have e1 : lmul y (oneL E a) = y := mul_one (Matrix.of y)
  rw [e, fderiv_comp _ (by rw [e1]; exact (hβ.differentiable (by simp)).differentiableAt)
    (lmul y).differentiableAt, e1, ContinuousLinearMap.fderiv]
  rfl

theorem exists_local {μ : Measure (GA E a)} [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E))))
    {β : Lie E a → ℂ} (hβ : IsTest β) {Fl : GA E a → ℂ} (hFl : LocallyIntegrable Fl μ) (g : GA E a)
    {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ∃ C : Set (GA E a), ∃ K : Set (Lie E a), ∃ N ∈ 𝓝 x₀, MeasurableSet C ∧ IsCompact K ∧ (∀ v ∈ C, psi v ∈ K) ∧
      IntegrableOn (wt U Fl g) C μ ∧
      ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β := by
  obtain ⟨Kc, hKc, hKs, N, hN, hNK⟩ := exists_compact_of_mul_mem_tsupport E a β hβ x₀ hx₀
  obtain ⟨hCm, hCi⟩ := measurableSet_integrableOn_wt E a μ U hU hUc Fl hFl Kc hKc hKs g
  exact ⟨_, Kc, N, hN, hCm, hKc, fun v hv => hv.2, hCi, fun v hv hvU x hx hm => hv ⟨hvU, hNK _ _ hx hm⟩⟩

theorem integrand_eq_zero {U : Subgroup (GL (Fin a) (Af E))} {β : Lie E a → ℂ} {Fl : GA E a → ℂ} {g : GA E a}
    {C : Set (GA E a)} {N : Set (Lie E a)}
    (hC : ∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N, toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β)
    {x : Lie E a} (hx : x ∈ N) (v : GA E a) (hv : v ∉ C) : hb β (x, psi v) * wt U Fl g v = 0 := by
  rw [wt_apply]
  by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
  · rw [hb, image_eq_zero_of_notMem_tsupport (hC v hv h x hx), zero_mul]
  · rw [if_neg h, mul_zero]

end GlobalTheory.CompanionTheory.SmoothRep.TstConv

open GlobalTheory.CompanionTheory.SmoothRep.TstConv in

theorem GlobalTheory.CompanionTheory.SmoothRep.convR_tst_mem_Sm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ β : Lie E a → ℂ, IsTest β → ∀ Fl : GA E a → ℂ, LocallyIntegrable Fl μ → convR μ (tst U β) Fl ∈ Sm E a ∧ ∀ (X : Lie E a) (g : GA E a), lieD X (convR μ (tst U β) Fl) g = convR μ (tst U (dTest X β)) Fl g := by
  intro E _ _ _ a μ _ _ U hU hUc β hβ Fl hFl

  have hchart : ∀ g, ∀ x ∈ invSet E a,
      chart (convR μ (tst U β) Fl) g x = ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := by
    intro g x hx
    obtain ⟨u, hu⟩ := id hx
    have e : x = toL u.val := hu.symm
    subst e
    rw [chart_val, convR_tst_mul_infGL]
  have hev : ∀ g, ∀ x ∈ invSet E a, chart (convR μ (tst U β) Fl) g =ᶠ[𝓝 x]
      fun x => ∫ v, hb β (x, psi v) * wt U Fl g v ∂μ := fun g x hx =>
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) (hchart g)

  have hloc : ∀ g, ∀ x₀ ∈ invSet E a, ∃ C : Set (GA E a), ∃ N ∈ 𝓝 x₀,
      (∀ x ∈ N, (∫ v, hb β (x, psi v) * wt U Fl g v ∂μ) = ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      ContDiff ℝ ∞ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) ∧
      (∀ p X, fderiv ℝ (fun x => ∫ v in C, hb β (x, psi v) * wt U Fl g v ∂μ) p X =
        ∫ v in C, fderiv ℝ (fun q => hb β (q, psi v)) p X * wt U Fl g v ∂μ) ∧
      (∀ v ∉ C, GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U → ∀ x ∈ N,
        toL (Matrix.of (psi v) * Matrix.of x) ∉ tsupport β) := by
    intro g x₀ hx₀
    obtain ⟨C, K, N, hN, hCm, hK, hCK, hCi, hvan⟩ := exists_local hU hUc hβ hFl g hx₀
    have P := GlobalTheory.CompanionTheory.SmoothParam.contDiff_integral_density (GA E a) (Lie E a) (Lie E a) (μ.restrict C)
      (wt U Fl g) psi K hCi continuous_psi.aestronglyMeasurable hK
      ((ae_restrict_iff' hCm).2 (Filter.Eventually.of_forall hCK)) (hb β) (contDiff_hb hβ.contDiff)
    exact ⟨C, N, hN, fun x hx => (setIntegral_eq_integral_of_forall_compl_eq_zero
      (integrand_eq_zero hvan hx)).symm, P.1, P.2, hvan⟩
  refine ⟨fun g x hx => ?_, fun X g => ?_⟩
  · obtain ⟨C, N, hN, heq, hcd, -, -⟩ := hloc g x hx
    exact (hcd.contDiffAt.congr_of_eventuallyEq
      ((hev g x hx).trans (Filter.eventually_of_mem hN heq))).contDiffWithinAt
  · have h1 : oneL E a ∈ invSet E a := isUnit_one
    obtain ⟨C, N, hN, heq, hcd, hder, hvan⟩ := hloc g _ h1
    rw [lieD, ((hev g _ h1).trans (Filter.eventually_of_mem hN heq)).fderiv_eq, hder]
    simp_rw [fderiv_hb_one hβ.contDiff]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
    · unfold convR
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      show dTest X β (psi v) * wt U Fl g v = tst U (dTest X β) v * Fl (g * v)
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · simp only [tst, ker, if_pos h, psi]
      · simp only [tst, ker, if_neg h, mul_zero, zero_mul]
    · intro v hv
      rw [wt_apply]
      by_cases h : GeneralLinearGroup.map (pFin E) v⁻¹ ∈ U
      · have hn : psi v ∉ tsupport β := by
          have := hvan v hv h (oneL E a) (mem_of_mem_nhds hN)
          simpa [toL] using this
        have h0 : fderiv ℝ β (psi v) = 0 := by
          by_contra h0
          exact hn (support_fderiv_subset ℝ h0)
        rw [dTest, h0, ContinuousLinearMap.zero_apply, zero_mul]
      · rw [if_neg h, mul_zero]
