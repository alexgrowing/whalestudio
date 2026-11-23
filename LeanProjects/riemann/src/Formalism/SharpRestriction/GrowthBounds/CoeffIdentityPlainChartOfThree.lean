import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

open MaximalIdealCongruence

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem sg_lin (X : RawChart C d I κ) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    X.sg (fun i => ∑ q, m q * u q i) = ∑ q, m q • X.sg (u q) := by
  apply MvPowerSeries.ext
  intro μ
  rw [map_sum]
  simp only [MvPowerSeries.coeff_smul]
  show -∑ i, (∑ q, m q * u q i) * _ = ∑ q, m q * -∑ i, u q i * _
  simp only [Finset.sum_mul, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem alongCv_lin {γ : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {ι : Type} [Fintype ι]
    (m : ι → C) (f : ι → MvPowerSeries κ C) : alongCv γ (∑ q, m q • f q) = ∑ q, m q • alongCv γ (f q) := by
  have hS : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  unfold alongCv
  simp only [← MvPowerSeries.substAlgHom_apply hS, map_sum, map_smul]

theorem phi_lin (X : RawChart C d I κ) (l : ℕ) (hl : 0 < l) (ζ : C) {γ δ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hδ : ∀ i, PowerSeries.constantCoeff (δ i) = 0) {ι : Type} [Fintype ι] (m : ι → C) (u : ι → κ → C) :
    phi X l ζ γ δ (fun i => ∑ q, m q * u q i) = ∑ q, m q • phi X l ζ γ δ (u q) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])
  unfold phi
  rw [sg_lin, alongCv_lin hγ, alongCv_lin hδ]
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  · simp only [← PowerSeries.coe_substAlgHom hS, map_sum, map_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext n
    simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
    ring

theorem ge_of_mm {V : VF C} {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.MM at h
  unfold VF.Ge
  exact_mod_cast le_of_lt h

theorem mm_pow_sub {V : VF C} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (h : V.MM (a - b)) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  rw [← geom_sum₂_mul]
  exact mm_mul_ge' (VF.Ge.sum fun i _ => by simpa using (ha.pow i).mul (hb.pow (n - 1 - i))) h

theorem coeffIdentity_plainChart_of_three [IsAlgClosed C] [CharZero C] (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g)
    (hA : StepA X V H) (hB : StepB X V) (hC : LemC X V) : IndependenceBoundPlain.PlainCoefficientIdentity X H := by
  intro _ g a _
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have hl0 : 0 < V.l := V.l_prime.pos
  choose z ε m hz hε hrel hz1 hε1 hm using hB ζ hζ g
  refine ⟨fun q' q => m q q', fun w x hg hV => ?_⟩
  obtain ⟨γ, δ, hγ, hδ, hrel', hmm, hq⟩ := hA ζ hζ g a w x hg hV
  refine ⟨fun q' => (V.l : C) * x 2 (Sum.inr q'), fun q hne => ?_, fun q => ?_⟩
  · have h2 := hg.1.2.2 2 (Sum.inr q) (by
      show X.ty (1 - g) q ≠ a + ((2 : ℕ) : ZMod d)
      simpa using hne)
    show (V.l : C) * x 2 (Sum.inr q) = 0
    rw [h2, mul_zero]
  · have h1 := hC ζ hζ γ δ (z q) (ε q) hγ hδ (hz q) (hε q) hrel' (hrel q) hmm
    rw [funext (hz1 q), funext (hε1 q), phi_lin X V.l hl0 ζ (fun i => (hγ i).1) (fun i => (hδ i).1), map_sum] at h1
    simp only [PowerSeries.coeff_smul, smul_eq_mul] at h1
    obtain ⟨hc0, hcA, _⟩ := hq q
    have hAint : V.Ge 0 (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q))) := by
      have := (ge_of_mm hcA).add hc0
      simpa using this
    have h3 := mm_pow_sub hAint hc0 hcA V.l
    have h4 : V.MM (∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
        (V.l : C) * x 2 (Sum.inr q'))) := mm_sum _ _ fun q' _ => mm_mul_ge' (hm q q') (hq q').2.2
    have e : (RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' =
        -(PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l - (RawChart.cart (H g)).c0' x q ^ V.l) +
        ((PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) ^ V.l -
          ∑ q', m q q' * PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q'))) +
        ∑ q', m q q' * (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q')) -
          (V.l : C) * x 2 (Sum.inr q'))) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      have : ∑ q', (V.l : C) * x 2 (Sum.inr q') * m q q' = ∑ q', m q q' * ((V.l : C) * x 2 (Sum.inr q')) :=
        Finset.sum_congr rfl fun q' _ => by ring
      rw [this]
      ring
    rw [e]
    exact mm_add (mm_neg h3) (mm_add h1 h4)

end SelfConjCharts

section Self

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

theorem FBChart.rawSelf_axis1 (Y : FBChart C V O dd) (p : SelfData Y d I0) (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
    (he : ∀ s ∈ e.support, s.1 ≠ 1) : MvPowerSeries.coeff e (Y.rawSelf p).h = 0 := by
  show MvPowerSeries.coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 1 Y.h (gauge_axes Y 1)) e he

theorem FBChart.rawSelf_basic (Y : FBChart C V O dd) (p : SelfData Y d I0) : SelfConjCharts.Basic (Y.rawSelf p) V where
  lg0 := Y.self_chart_log_constantCoeff p
  exlg := Y.rawSelf_exlg p
  lin := Y.rawSelf_lin p
  axis0 := Y.rawSelf_axis0 p
  axis1 := Y.rawSelf_axis1 p
  uint := Y.rawSelf_u_integral p
  hmis := hStabSelf_holds C V O dd Y d I0 p

end Self

theorem coeffIdentity_selfConj_of_four (hA : GoodCurveClosed) (hB : OtherGroupCurvesClosed) (hC : MixedCoefficientClosed) (hD : BiadditiveOnColumns) : CoefficientIdentitySelfConjugate := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p _ H
  have := Y.algClosed
  have hb := Y.rawSelf_basic p
  exact SelfConjCharts.coeffIdentity_plainChart_of_three (Y.rawSelf p) V H (hA C V d _ _ _ hb H) (hB C V d _ _ _ hb H)
    (hC C V d _ _ _ hb (hD C V O dd Y d I0 p))

end Formalism.L2.FormalSeriesBounds
