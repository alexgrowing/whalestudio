import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.DifferentialAction.DifferentialActionLemma.DsigWSmul
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.S.Pv.SmoothIrredBK

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def BKSimple : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsHCParam lam → IsDSHpk k r ε lam σ → ∃ μG : Measure (Mt k r), IsHaarOn (UH (Hpk k r)) μG ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ u ∈ smoothVecs (k := k) (r := r) σ,
    ∃ f : Mt k r → ℂ, ∀ W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ W, InLieHpk k r X) →
      Integrable (fun x => f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w)) μG ∧
      dsigW (k := k) (r := r) σ W u = ∫ x, f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w) ∂μG

section Core

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

def smoothSub (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := smoothVecs (k := k) (r := r) σ
  add_mem' := fun ha hb => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_add ha hb
  zero_mem' := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero
  smul_mem' := fun c _ hx => Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul c hx

theorem core (hσ : IsDSHpk k r ε lam σ) {μG : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    {w : H} (hw : w ∈ smoothVecs (k := k) (r := r) σ) (m : H → ℂ)
    (hadd : ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ, m (v + v') = m v + m v')
    (hsm : ∀ (a : ℂ), ∀ v ∈ smoothVecs (k := k) (r := r) σ, m (a • v) = a • m v)
    (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)))
    (hWs : ∀ W ∈ Ws, ∀ X ∈ W, InLieHpk k r X)
    (hbd : ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖m v‖ ≤ C * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W v‖).sum)
    (hz : ∀ x ∈ UH (Hpk k r), m (σ x w) = 0) {u : H} (hu : u ∈ smoothVecs (k := k) (r := r) σ) (f : Mt k r → ℂ)
    (hf : ∀ W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ W, InLieHpk k r X) →
      Integrable (fun x => f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w)) μG ∧
      dsigW (k := k) (r := r) σ W u = ∫ x, f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w) ∂μG) :
    m u = 0 := by
  have hU : IsURepOn (UH (Hpk k r)) σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  set n := Ws.length with hn
  have hWi : ∀ i : Fin n, ∀ Y ∈ Ws.get i, InLieHpk k r Y := fun i => hWs _ (List.get_mem _ _)
  let ι : H → (Fin n → H) := fun v i => dsigW (k := k) (r := r) σ (Ws.get i) v
  let T : smoothSub (k := k) (r := r) σ →ₗ[ℂ] (Fin n → H) :=
    { toFun := fun s => ι s
      map_add' := fun a b => funext fun i => ReciprocityTheory.ChartRestriction.DS.Lap.DifferentialActionLinearity.CW.dsigW_add hU a.2 b.2 _ (hWi i)
      map_smul' := fun c a => funext fun i => ReciprocityTheory.ChartRestriction.DS.Lap.DifferentialActionLinearity.CW.dsigW_smul hU c a.2 _ (hWi i) }
  let M : smoothSub (k := k) (r := r) σ →ₗ[ℂ] ℂ :=
    { toFun := fun s => m s
      map_add' := fun a b => hadd _ a.2 _ b.2
      map_smul' := fun c a => hsm c _ a.2 }
  have hsum : ∀ v : H, (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W v‖).sum ≤ n * ‖ι v‖ := by
    intro v
    have h1 : ∀ x ∈ Ws.map (fun W => ‖dsigW (k := k) (r := r) σ W v‖), x ≤ ‖ι v‖ := by
      intro x hx
      obtain ⟨W, hW, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hW
      exact norm_le_pi_norm (ι v) i
    have := List.sum_le_card_nsmul _ _ h1
    rw [List.length_map, nsmul_eq_mul] at this
    exact this
  have hker : LinearMap.ker T ≤ LinearMap.ker M := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h0 : ι s = 0 := hs
    have hb := hbd s s.2
    have hz0 : (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W (s : H)‖).sum = 0 := by
      refine le_antisymm ?_ (List.sum_nonneg fun x hx => by
        obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _)
      have := hsum s
      rw [h0, norm_zero, mul_zero] at this
      exact this
    rw [hz0, mul_zero] at hb
    exact norm_le_zero_iff.1 hb
  let g : LinearMap.range T →ₗ[ℂ] ℂ := (LinearMap.ker T).liftQ M hker ∘ₗ T.quotKerEquivRange.symm.toLinearMap
  have hg : ∀ s : smoothSub (k := k) (r := r) σ, g ⟨T s, LinearMap.mem_range_self T s⟩ = m s := by
    intro s
    show (LinearMap.ker T).liftQ M hker (T.quotKerEquivRange.symm ⟨T s, _⟩) = m s
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hbound : ∀ p : LinearMap.range T, ‖g p‖ ≤ (|C| * n) * ‖p‖ := by
    rintro ⟨p, s, rfl⟩
    rw [hg s]
    have hb := hbd s s.2
    have h2 := hsum s
    have hS0 : 0 ≤ (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W (s : H)‖).sum :=
      List.sum_nonneg fun x hx => by obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have hp : ‖(⟨T s, LinearMap.mem_range_self T s⟩ : LinearMap.range T)‖ = ‖ι s‖ := rfl
    rw [hp]
    calc ‖m s‖ ≤ C * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W (s : H)‖).sum := hb
      _ ≤ |C| * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W (s : H)‖).sum :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      _ ≤ |C| * (n * ‖ι s‖) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = |C| * n * ‖ι s‖ := by ring
  let g' : LinearMap.range T →L[ℂ] ℂ := g.mkContinuous (|C| * n) hbound
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (LinearMap.range T) g'

  have key1 : m u = Λ (ι u) := by
    have h1 := hΛ ⟨T ⟨u, hu⟩, LinearMap.mem_range_self T _⟩
    have h2 : ((⟨T ⟨u, hu⟩, LinearMap.mem_range_self T _⟩ : LinearMap.range T) : Fin n → H) = ι u := rfl
    rw [h2] at h1
    rw [h1]
    exact (hg ⟨u, hu⟩).symm

  have hFint : Integrable (fun x => f x • ι (σ (Matrix.of x) w)) μG := by
    refine integrable_pi_iff.2 fun i => ?_
    exact (hf (Ws.get i) (hWi i)).1
  have key2 : ι u = ∫ x, f x • ι (σ (Matrix.of x) w) ∂μG := by
    funext i
    have e := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => H) i) hFint
    simp only [ContinuousLinearMap.proj_apply] at e
    rw [← e]
    exact (hf (Ws.get i) (hWi i)).2
  rw [key1, key2, ← ContinuousLinearMap.integral_comp_comm Λ hFint]
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ UH (Hpk k r) := by rw [ae_iff]; simpa using hG.2.2.1
  refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
  filter_upwards [hae] with x hx
  have hsx : σ (Matrix.of x) w ∈ smoothVecs (k := k) (r := r) σ := Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hU hw hx
  rw [map_smul]
  have h1 := hΛ ⟨T ⟨_, hsx⟩, LinearMap.mem_range_self T _⟩
  have h2 : ((⟨T ⟨_, hsx⟩, LinearMap.mem_range_self T _⟩ : LinearMap.range T) : Fin n → H) = ι (σ (Matrix.of x) w) := rfl
  rw [h2] at h1
  show f x • Λ (ι (σ (Matrix.of x) w)) = (0 : ℂ)
  have e3 : Λ (ι (σ (Matrix.of x) w)) = m (σ (Matrix.of x) w) := by
    rw [h1]
    exact hg ⟨_, hsx⟩
  rw [e3, hz _ hx, smul_zero]

end Core

def HCIrredAt {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ w : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ w → w ≠ 0 → ∀ u : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ u →
    u ∈ Submodule.span ℂ {y : H | ∃ (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ W, InLieHpk k r X) ∧
      g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) ∧ y = dsigW (k := k) (r := r) σ W (σ g w)}

def HCIrred : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsHCParam lam → IsDSHpk k r ε lam σ → HCIrredAt (k := k) (r := r) σ

def BKOfIrred : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsHCParam lam → IsDSHpk k r ε lam σ → HCIrredAt (k := k) (r := r) σ →
    ∃ μG : Measure (Mt k r), IsHaarOn (UH (Hpk k r)) μG ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ u ∈ smoothVecs (k := k) (r := r) σ,
    ∃ f : Mt k r → ℂ, ∀ W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ X ∈ W, InLieHpk k r X) →
      Integrable (fun x => f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w)) μG ∧
      dsigW (k := k) (r := r) σ W u = ∫ x, f x • dsigW (k := k) (r := r) σ W (σ (Matrix.of x) w) ∂μG

end Formalism.L2.S.Pv.SmoothIrredBK
