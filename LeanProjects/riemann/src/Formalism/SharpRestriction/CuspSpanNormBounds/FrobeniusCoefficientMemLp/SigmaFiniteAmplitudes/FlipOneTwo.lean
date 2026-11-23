import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstParts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem pairMaj_nonneg (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (b : ℝ) (p : PairSp k r) :
    0 ≤ Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p :=
  Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _

theorem amp_core' (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs}
    (hbe1 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ t w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ t w0)))
    (hbe2 : ∀ t ∈ UH (Hpk k r), Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ t w0) v' =
      (innerSL ℂ (l' v')).smulRight (l' (L.σ t w0)))
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  have hσR : SigmaFinite μR := hμR.1
  have hσνR : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hσν : SigmaFinite ν := sigmaFinite_nu L hγ hμR hOQ hNI hpm
  have hσW : SigmaFinite L.μW := L.hμW.1.1
  have hσW' : SigmaFinite L.μW' := L.hμW'.1.1
  have hWi := mp_inv_W_sk L.hz.1 L.hz.2 L.hμW.1
  have hWi' := mp_inv_W_sk L.hz'.1 L.hz'.2 L.hμW'.1
  have hNi : MeasurePreserving Formalism.FourierDecayAlt.P.B7.invM L.μN L.μN :=
    ⟨hinv.measurable, map_inv_haarLieN L.κN⟩
  have hWae : ∀ᵐ x ∂L.μW, Matrix.of x ∈ UWset k r L.z := ae_mem_sk L.hμW.1
  have hWae' : ∀ᵐ x ∂L.μW', Matrix.of x ∈ UWset k r L.z' := ae_mem_sk L.hμW'.1
  have hNae : ∀ᵐ x ∂L.μN, Matrix.of x ∈ Nset k r := ae_mem_haarLieN L.κN
  have hsm : StronglyMeasurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable
      (((measurable_mStab γ).comp measurable_fst).prodMk measurable_snd)
  have hF : Integrable (fun q : (PairSp k r × Mt k r) × Mt k r =>
      PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)) ((ν.prod μR).prod νR) := by
    refine ⟨hsm.aestronglyMeasurable, ?_⟩
    have hmeas : Measurable (fun q : (PairSp k r × Mt k r) × Mt k r =>
        ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ) := hsm.measurable.enorm
    have hmeas2 : Measurable (fun pa : PairSp k r × Mt k r =>
        ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR) :=
      hmeas.lintegral_prod_right'
    show ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR) < ⊤
    calc ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ q.1, q.2)‖ₑ ∂((ν.prod μR).prod νR)
        = ∫⁻ pa, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)‖ₑ ∂νR ∂(ν.prod μR) :=
          lintegral_prod _ hmeas.aemeasurable
      _ = ∫⁻ p, ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR ∂ν :=
          lintegral_prod _ hmeas2.aemeasurable
      _ = ∫⁻ p, ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG ∂ν := by
          refine lintegral_congr_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp
      _ ≤ ∫⁻ p, ENNReal.ofReal ((‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) *
            ∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
              Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) ∂ν := by
          refine lintegral_mono_ae ((ae_inPair_nu L hμR hOQ).mono fun p hp => ?_)
          exact lint_G_bound L hμG hNI hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp
      _ < ⊤ := (hpm.const_mul _).lintegral_lt_top
  have hmap := pairMeas_eq_map L hμR hOQ
  have hL : ∀ᵐ x ∂νR, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
      (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) =
      ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) := by
    filter_upwards [ae_uh_nuR hγ hμG hμR hQ, hF.prod_left_ae] with x hx hix
    have hgx : γ * Matrix.of x ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hγ hx
    have hsmx : StronglyMeasurable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable (measurable_id.prodMk measurable_const)
    have hPM : (fun q => Psi L w0 v v' ξ ξ' γ q x) =ᵐ[pairMeas L]
        (fun q => PsiM L w0 v v' ξ ξ' γ (q, x)) :=
      (ae_inPair_pair L).mono fun q hq => (PsiM_eq L w0 v v' ξ ξ' hγ hq hx).symm
    have hintM : Integrable (fun q : PairSp k r => PsiM L w0 v v' ξ ξ' γ (q, x)) (pairMeas L) := by
      rw [hmap]
      exact (integrable_map_measure hsmx.aestronglyMeasurable (measurable_mStab γ).aemeasurable).2 hix
    rw [← pair_split L hWi hWi' hNi hWae hWae' hNae w0 v v' ξ ξ' l l' hx hgx (hbe1 _ hgx)
      (hbe2 _ hx) (hintM.congr hPM.symm), integral_congr_ae hPM, hmap,
      integral_map (measurable_mStab γ).aemeasurable hsmx.aestronglyMeasurable]
  have hsch : ∀ᵐ p ∂ν, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR =
      ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p := by
    filter_upwards [ae_inPair_nu L hμR hOQ] with p hp
    have hs := schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp
    rw [int_cell L w0 v v' ξ ξ' hγ hrel hμG hμR hinv hQ hp hs.1, hs.2]
  calc (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
        ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ
      = ∫ x, (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) •
          (innerSL ℂ (l' (L.σ (Matrix.of x) w0))).smulRight (l (L.σ (γ * Matrix.of x) w0)) ∂νR := by
        rw [integral_smul]
        simp [ampJ]
    _ = ∫ x, ∫ pa, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂(ν.prod μR) ∂νR := integral_congr_ae hL
    _ = ∫ pa, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x) ∂νR ∂(ν.prod μR) :=
        (integral_integral_swap (f := fun pa x => PsiM L w0 v v' ξ ξ' γ (mStab γ pa, x)) hF).symm
    _ = ∫ p, ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR ∂ν :=
        integral_prod _ hF.integral_prod_left
    _ = ∫ p, ((d : ℂ)⁻¹) • besselIntg L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ p ∂ν :=
        integral_congr_ae hsch
    _ = ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
        rw [integral_smul]
        rfl

theorem amp_core (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ}
    (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (hl : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0, ∀ v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {μR νR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hμR : IsHaarOn (RStab k r γ) μR)
    (hOQ : IsOrbQuot L γ μR ν)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b) ν)
    {v v' : L.Hs} (hv : v ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0) (hv' : v' ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (ξ : L.Wp) (ξ' : L.Wq) :
    (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
      ((d : ℂ)⁻¹) • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L v v' ξ ξ') γ ν := by
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hl _ (Submodule.subset_span ⟨t, ht, rfl⟩) v hv)
    (fun t ht => hl' _ (Submodule.subset_span ⟨t, ht, rfl⟩) v' hv') hC1 hC2 ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
