import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.RealQuotProd

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.act (g * h) x = ActionCoordinates.act g (ActionCoordinates.act h x) := by
  unfold ActionCoordinates.act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : ActionCoordinates.Wsp P Q) : ActionCoordinates.act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_mul_inv {a : UpqT P Q} {x : ActionCoordinates.Wsp P Q} (ha : ActionCoordinates.act a x = x) (g : UpqT P Q) :
    ActionCoordinates.act (a * g)⁻¹ x = ActionCoordinates.act g⁻¹ x := by
  have : ActionCoordinates.act a⁻¹ x = x := by
    conv_lhs => rw [← ha]
    rw [← act_mul, inv_mul_cancel, act_one]
  rw [_root_.mul_inv_rev, act_mul, this]

theorem measurable_act_inv (x : ActionCoordinates.Wsp P Q) :
    Measurable fun g : UpqT P Q => ActionCoordinates.act g⁻¹ x := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  exact ((GlobalTheory.UpqTopology.continuous_mat.comp continuous_inv).matrix_mulVec
    continuous_const).measurable

theorem sigmaFinite_cd (c : CDHaar) (P Q : ℕ) : SigmaFinite (c.cd P Q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  haveI : (c.cd P Q).IsHaarMeasure := c.haar P Q
  infer_instance

theorem one_place (H : ActionCoordinates.QuotientMeasure) (c : CDHaar) {β : ℝ} (hβ : β = 1 ∨ β = -1)
    {x : ActionCoordinates.Wsp P Q} (hx : ActionCoordinates.qf x = β) {k : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q}
    {ι : UpqT P' Q' → UpqT P Q} (hk : ActionCoordinates.IsPerpFrame x k ι) {u : UpqT P Q → ℝ≥0∞}
    (hu : Measurable u) (hu' : ∀ g, Measurable (fun h => u (ι h * g)) ∧
      ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1)
    {fib : ℝ → Measure (ActionCoordinates.Wsp P Q)} (hfib : ActionCoordinates.IsDxDq β fib)
    {φ : ActionCoordinates.Wsp P Q → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ (ActionCoordinates.act g⁻¹ x) * u g ∂(c.cd P Q) =
      (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ y ∂(fib β) := by
  classical
  obtain ⟨h1, -, h3⟩ := H P Q β hβ x hx
  choose! s hs using h1
  have hae : ∀ᵐ y ∂(fib β), ActionCoordinates.qf y = β := by
    obtain ⟨U, B, -, -, -, hF⟩ := hfib
    have h1 : ∀ᵐ y ∂(fib β), y ∈ ActionCoordinates.qf ⁻¹' {id β} ∩ U := hF.1 β
    filter_upwards [h1] with y hy using hy.1
  rw [(h3 P' Q' k ι hk).2 c fib hfib s hs (fun g => φ (ActionCoordinates.act g⁻¹ x) * u g)
    ((hφ.comp (measurable_act_inv x)).mul hu),
    Measure.restrict_eq_self_of_ae_mem (s := {y | ActionCoordinates.qf y = β}) hae]
  congr 1
  refine lintegral_congr_ae (hae.mono fun y hy => ?_)
  have e : ∀ h, φ (ActionCoordinates.act (ι h * s y)⁻¹ x) = φ y := fun h => by
    rw [act_mul_inv (hk.2.2 h).1, hs y hy]
  simp only [e]
  rw [lintegral_const_mul _ (hu' _).1, (hu' _).2, mul_one]

theorem quot_integral_prod : ActionCoordinates.QuotientMeasure → ∀ (c : CDHaar) (T : Type) [Fintype T] (P Q P' Q' : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x : T → ActionCoordinates.Wsp P Q, (∀ ρ, ActionCoordinates.qf (x ρ) = β) → ∀ (k : T → (ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q)) (ι : T → UpqT P' Q' → UpqT P Q), (∀ ρ, ActionCoordinates.IsPerpFrame (x ρ) (k ρ) (ι ρ)) → ∀ u : T → UpqT P Q → ℝ≥0∞, (∀ ρ, Measurable (u ρ) ∧ ∀ g, Measurable (fun h => u ρ (ι ρ h * g)) ∧ ∫⁻ h, u ρ (ι ρ h * g) ∂(c.cd P' Q') = 1) → ∀ j : (T → UpqT P' Q') →* (T → UpqT P Q), (∀ b ρ, j b ρ = ι ρ (b ρ)) → ∀ ν : Measure (LatticeTensorUnfolding.RCosets j), LatticeTensorUnfolding.IsQuotMeasure j (Measure.pi fun _ => c.cd P Q) (Measure.pi fun _ => c.cd P' Q') ν → ∀ fib : ℝ → Measure (ActionCoordinates.Wsp P Q), ActionCoordinates.IsDxDq β fib → ∀ φ : T → ActionCoordinates.Wsp P Q → ℝ≥0∞, (∀ ρ, Measurable (φ ρ)) → ∫⁻ s : LatticeTensorUnfolding.RCosets j, ∏ ρ, φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) ∂ν = ∏ ρ, (ActionCoordinates.cM (P + Q))⁻¹ * ∫⁻ y, φ ρ y ∂(fib β) := by
  intro H c T _ P Q P' Q' β hβ x hx k ι hk u hu j hj ν hν fib hfib φ hφ
  haveI := sigmaFinite_cd c P Q
  haveI := sigmaFinite_cd c P' Q'
  let f : T → UpqT P Q → ℝ≥0∞ := fun ρ g => φ ρ (ActionCoordinates.act g⁻¹ (x ρ)) * u ρ g
  have hf : ∀ ρ, Measurable (f ρ) := fun ρ =>
    ((hφ ρ).comp (measurable_act_inv (x ρ))).mul (hu ρ).1
  have key := hν (fun g => ∏ ρ, f ρ (g ρ))
    (Finset.measurable_prod _ fun ρ _ => (hf ρ).comp (measurable_pi_apply ρ))
  rw [GlobalTheory.SnMass.Push.lintegral_fintype_prod f hf] at key
  rw [← Finset.prod_congr rfl fun ρ _ =>
    one_place H c hβ (hx ρ) (hk ρ) (hu ρ).1 (hu ρ).2 hfib (hφ ρ)]
  refine Eq.trans (lintegral_congr fun s => ?_) key.symm
  have e : ∀ h : T → UpqT P' Q', ∏ ρ, f ρ ((j h * s.out) ρ) =
      ∏ ρ, (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ)) ρ (h ρ) :=
    fun h => Finset.prod_congr rfl fun ρ _ => by
      simp only [f, Pi.mul_apply, hj]
      rw [act_mul_inv ((hk ρ).2.2 _).1]
  rw [lintegral_congr e, GlobalTheory.SnMass.Push.lintegral_fintype_prod
    (fun ρ b => φ ρ (ActionCoordinates.act (s.out ρ)⁻¹ (x ρ)) * u ρ (ι ρ b * s.out ρ))
    (fun ρ => (((hu ρ).2 _).1).const_mul _)]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [lintegral_const_mul _ ((hu ρ).2 _).1, ((hu ρ).2 _).2, mul_one]

end GlobalTheory.RealQuotProd
