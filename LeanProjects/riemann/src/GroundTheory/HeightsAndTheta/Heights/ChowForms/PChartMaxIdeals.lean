import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartMax
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProperSymm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartMaxIdeals

variable {F : Type} [Field F] {n e : ℕ}

theorem chartIncIdeal_eq_sup {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    chartIncIdeal W t e = chartIncIdeal I t e ⊔ W.map (rename Sum.inl) := by
  unfold chartIncIdeal
  apply le_antisymm
  · refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw [Ideal.map_sup]
    exact sup_le le_sup_right (((Ideal.map_mono le_sup_right).trans le_sup_left).trans le_sup_left)
  · refine sup_le (sup_le ?_ le_sup_right) ?_
    · exact (Ideal.map_mono (sup_le_sup_right h _)).trans le_sup_left
    · exact (Ideal.map_mono le_sup_left).trans le_sup_left

theorem chartIncIdeal_le {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    chartIncIdeal I t e ≤ chartIncIdeal W t e :=
  le_sup_left.trans_eq (chartIncIdeal_eq_sup h t).symm

def toSub {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) (e : ℕ) :
    ChartInc I t e →+* ChartInc W t e :=
  Ideal.Quotient.factor (chartIncIdeal_le h t)

theorem ker_toSub {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    RingHom.ker (toSub h t e) = W.map (chartX I t e) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    have hy : y ∈ chartIncIdeal W t e := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [chartIncIdeal_eq_sup h t, Submodule.mem_sup] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have hb' : Ideal.Quotient.mk (chartIncIdeal I t e) b ∈ W.map (chartX I t e) := by
      have hle : W.map (rename Sum.inl) ≤ (W.map (chartX I t e)).comap (Ideal.Quotient.mk (chartIncIdeal I t e)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro w hw
        exact Ideal.mem_map_of_mem (chartX I t e) hw
      exact hle hb
    have ha' : Ideal.Quotient.mk (chartIncIdeal I t e) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [map_add, ha', zero_add]
    exact hb'
  · rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show Ideal.Quotient.mk (chartIncIdeal W t e) (rename Sum.inl w) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, chartIncIdeal_eq_sup h t]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hw)

theorem toSub_comp_chartX {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (toSub h t e).comp (chartX I t e) = chartX W t e :=
  RingHom.ext fun _ => rfl

theorem toSub_comp_algebraMap {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (toSub h t e).comp (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e) :=
  RingHom.ext fun _ => rfl

theorem comap_chartX_map {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (W.map (chartX I t e)).comap (chartX I t e) = RingHom.ker (chartX W t e) := by
  rw [← ker_toSub h t, RingHom.comap_ker, toSub_comp_chartX]

theorem comap_algebraMap_map {I W : Ideal (MvPolynomial (Fin n) F)} (h : I ≤ W) (t : Fin n → F) :
    (W.map (chartX I t e)).comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc W t e)) := by
  rw [← ker_toSub h t, RingHom.comap_ker, toSub_comp_algebraMap]

theorem disjoint_iff {I : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    {p : Ideal (MvPolynomial (Fin e × Fin n) F)} [p.IsPrime] (P : Ideal (ChartInc I t e)) :
    Disjoint (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Set (ChartInc I t e)) (P : Set _) ↔
      P.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) ≤ p := by
  constructor
  · intro hd s hs
    by_contra hsp
    exact Set.disjoint_left.mp hd ⟨s, hsp, rfl⟩ hs
  · intro hle
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hle hmem)

theorem le_of_sup_le (hD : ChartDehomog.Statement) {W₁ W₂ : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    (hh₁ : IsHomogIdeal W₁) (h₂ : W₂.IsPrime) (hh₂ : IsHomogIdeal W₂) (ht₂ : linForm t ∉ W₂)
    (h : W₁ ⊔ Ideal.span {linForm t - 1} ≤ W₂ ⊔ Ideal.span {linForm t - 1}) : W₁ ≤ W₂ := by
  intro g hg
  rw [← sum_homogeneousComponent g]
  refine Ideal.sum_mem _ fun d _ => ?_
  exact hD F n W₂ t _ d h₂ hh₂ ht₂ (homogeneousComponent_isHomogeneous d g)
    (h (Ideal.mem_sup_left (hh₁ g hg d)))

end ChartMaxIdeals

open ChartMaxIdeals in

theorem ChartMaxIdeals.proof (h₁ : ConeDimOfChowForm.Statement) (h₂ : ConeDimComponent.Statement)
    (h₆ : SpecFirstMemIncIdeal.Statement) (h₇ : ChartFinite.Statement) (h₈ : ChartIncDomain.Statement)
    (h₉ : ChartKernel.Statement) (hH : ChartHomogenise.Statement) (hD : ChartDehomog.Statement)
    (hC : ComponentOfIncIdeal.Statement) : ChartMaxIdeals.Statement := by
  intro F _ n e I f t u q p _ hI hf hu hq hp hqt
  classical
  have hdim := h₁ F n (e + 1) I f hI hf
  have hpt : specFirst f t ∉ p := by rw [hp, Ideal.mem_span_singleton]; exact hqt
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₇ F n e I f t p hI hf hpt
  have : Algebra.IsIntegral (Localization.AtPrime p) (ChartLoc I t e p) := Algebra.IsIntegral.of_finite _ _
  have hsupp : ∀ W, W ∈ (divCycle I u).support ↔
      W ∈ relComps (I ⊔ Ideal.span {linForm u}) ∧ localMult (I ⊔ Ideal.span {linForm u}) W ≠ 0 := by
    intro W
    rw [Finsupp.mem_support_iff, divCycle, fundCycle, Finsupp.onFinset_apply]
    split_ifs with h <;> simp [h]
  have htower : (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) =
      (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

  have key : ∀ W : Ideal (MvPolynomial (Fin n) F), IsProjPrime W → linForm t ∉ W → I ≤ W → incIdeal W e = p →
      (chartIdeal I t e p W).IsMaximal ∧
        (chartIdeal I t e p W).comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) = W.map (chartX I t e) ∧
        (W.map (chartX I t e)).comap (chartX I t e) = W ⊔ Ideal.span {linForm t - 1} := by
    intro W hW ht hIW hWp
    obtain ⟨hdom, hker⟩ := h₈ F n e W t hW ht
    have hk := h₉ F n e W t hW ht
    have hprime : (W.map (chartX I t e)).IsPrime := by
      rw [← ker_toSub hIW t]; exact RingHom.ker_isPrime _
    have hcS : (W.map (chartX I t e)).comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = p := by
      rw [comap_algebraMap_map hIW t, hk, hWp]
    have hdisj := (disjoint_iff (p := p) (W.map (chartX I t e))).mpr hcS.le
    have h𝔓 : (chartIdeal I t e p W).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hprime hdisj
    have hc𝔓 : (chartIdeal I t e p W).comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) =
        W.map (chartX I t e) :=
      IsLocalization.under_map_of_isPrime_disjoint _ _ hprime hdisj
    have hO : ((chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p))).comap
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) = p := by
      rw [Ideal.comap_comap, htower, ← Ideal.comap_comap, hc𝔓, hcS]
    have hmaxO : (chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← IsLocalization.map_under p.primeCompl (Localization.AtPrime p)
        ((chartIdeal I t e p W).comap (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)))]
      change Ideal.map _ (Ideal.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) _) = _
      rw [hO, Localization.AtPrime.map_eq_maximalIdeal]
    refine ⟨Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Localization.AtPrime p) _ ?_, hc𝔓, ?_⟩
    · rw [hmaxO]; exact IsLocalRing.maximalIdeal.isMaximal _
    · rw [comap_chartX_map hIW t, hker]

  have hmem : ∀ W ∈ {W | W ∈ (divCycle I u).support ∧ Ideal.span {q} = incIdeal W e},
      IsProjPrime W ∧ linForm t ∉ W ∧ I ≤ W ∧ linForm u ∈ W ∧ incIdeal W e = p := by
    rintro W ⟨hWs, hWq⟩
    obtain ⟨hrel, -⟩ := (hsupp W).mp hWs
    obtain ⟨hWproj, -⟩ := h₂ F n e I W u hI hdim hu hrel
    have hJW : I ⊔ Ideal.span {linForm u} ≤ W := hrel.1.1.2
    have hIW : I ≤ W := le_sup_left.trans hJW
    have ht : linForm t ∉ W := by
      intro htW
      have := h₆ F n e I W f t hf hIW htW
      rw [← hWq, Ideal.mem_span_singleton] at this
      exact hqt this
    exact ⟨hWproj, ht, hIW, hJW (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)), hWq.symm.trans hp.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨hWp, ht, hIW, huW, hinc⟩ := hmem W hW
    refine ⟨(key W hWp ht hIW hinc).1, ?_⟩
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ huW)
  · intro W₁ hW₁ W₂ hW₂ heq
    obtain ⟨hp₁, ht₁, hI₁, -, hinc₁⟩ := hmem W₁ hW₁
    obtain ⟨hp₂, ht₂, hI₂, -, hinc₂⟩ := hmem W₂ hW₂
    obtain ⟨-, hc₁, hx₁⟩ := key W₁ hp₁ ht₁ hI₁ hinc₁
    obtain ⟨-, hc₂, hx₂⟩ := key W₂ hp₂ ht₂ hI₂ hinc₂
    have h12 : W₁ ⊔ Ideal.span {linForm t - 1} = W₂ ⊔ Ideal.span {linForm t - 1} := by
      rw [← hx₁, ← hx₂, ← hc₁, ← hc₂]
      rw [heq]
    exact le_antisymm (le_of_sup_le hD hp₁.isHomog hp₂.isPrime hp₂.isHomog ht₂ h12.le)
      (le_of_sup_le hD hp₂.isHomog hp₁.isPrime hp₁.isHomog ht₁ h12.ge)
  · rintro 𝔓 ⟨hmax, hθ⟩
    have := hmax.isPrime
    set P := 𝔓.comap (algebraMap (ChartInc I t e) (ChartLoc I t e p)) with hPdef
    set Q := P.comap (chartX I t e) with hQdef
    have hzero : ∀ g ∈ I ⊔ Ideal.span {linForm t - 1}, chartX I t e g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg))
    have hLQ : linForm t - 1 ∈ Q := by
      show chartX I t e (linForm t - 1) ∈ P
      rw [hzero _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))]
      exact P.zero_mem
    have hIQ : I ≤ Q := fun g hg => by
      show chartX I t e g ∈ P
      rw [hzero g (Ideal.mem_sup_left hg)]
      exact P.zero_mem
    have huQ : linForm u ∈ Q := hθ
    obtain ⟨W, hWp, ht, hWQ, hWmax⟩ := hH F n Q t inferInstance hLQ
    have hJW : I ⊔ Ideal.span {linForm u} ≤ W :=
      hWmax _ (isHomogIdeal_sup_span_linForm hI.isHomog u)
        (sup_le hIQ (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact huQ))
    have hIW : I ≤ W := le_sup_left.trans hJW
    have hPW : W.map (chartX I t e) ≤ P := Ideal.map_le_iff_le_comap.mpr (le_sup_left.trans hWQ.le)
    have hPp : P.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) ≤ p := by
      intro s hs
      by_contra hsp
      have hunit : IsUnit (algebraMap (ChartInc I t e) (ChartLoc I t e p)
          (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) s)) :=
        IsLocalization.map_units (ChartLoc I t e p) (⟨_, s, hsp, rfl⟩ :
          Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl)
      exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hunit)
    have hincle : incIdeal W e ≤ Ideal.span {q} := by
      rw [← hp, ← h₉ F n e W t hWp ht, ← comap_algebraMap_map hIW t]
      exact (Ideal.comap_mono hPW).trans hPp
    obtain ⟨hrel, hinc⟩ := hC F n e I W u q hI hdim hu hWp hJW hq hincle
    refine ⟨W, ⟨(hsupp W).mpr ⟨hrel, localMult_ne_zero_of_mem_minimalPrimes hrel.1⟩, hinc.symm⟩, ?_⟩
    have hmaxW := (key W hWp ht hIW (hinc.trans hp.symm)).1
    have hle : chartIdeal I t e p W ≤ 𝔓 := by
      rw [chartIdeal, Ideal.map_le_iff_le_comap]
      exact hPW
    exact hmaxW.eq_of_le hmax.ne_top hle

end

end GroundTheory.Heights₂.Heights
