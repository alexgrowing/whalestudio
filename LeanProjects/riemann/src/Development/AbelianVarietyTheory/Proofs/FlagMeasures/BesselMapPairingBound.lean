import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KStableFiniteDimSmoothCompactRootStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriods

section

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma dsigW_eq (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

lemma isBesselMapSm_smul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π l) (a : ℂ) :
    Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π (fun v => a • l v) := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨fun v hv w hw => ?_, fun c v hv => ?_, fun g hg m hm v hv => ?_, ‖a‖ * C, Ws, h4, fun v hv => ?_⟩
  · simp only [h1 v hv w hw, smul_add]
  · simp only [h2 c v hv]; rw [smul_comm]
  · simp only [h3 g hg m hm v hv, map_smul]; rw [smul_comm]
  · simp only [dsigW_eq, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h5 v hv) (norm_nonneg _)

lemma l2SG_sqrt_smul_eq_ofReal_mul {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] (ν : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (n : ℕ) (c : ℝ)
    (h : l2SG ν F = ENNReal.ofReal c) :
    l2SG ν (fun g => ((Real.sqrt n : ℝ) : ℂ) • F g) = ENNReal.ofReal (c * n) := by
  have e : ∀ y : Wp, ((‖((Real.sqrt n : ℝ) : ℂ) • y‖₊ : ℝ≥0∞)) ^ 2 = (n : ℝ≥0∞) * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
    intro y
    have : ‖((Real.sqrt n : ℝ) : ℂ)‖₊ ^ 2 = (n : NNReal) := by
      apply NNReal.eq
      simp [Real.sq_sqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, this, ENNReal.coe_natCast]
  unfold l2SG at h ⊢
  simp only [e]
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n), h, mul_comm c, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end

theorem exists_goodS : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hR hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, isBesselMapSm_smul hl _, isBesselMapSm_smul hl' _, hvs, hv0, ⟨P, hP, ?_⟩,
    div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd, l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs),
    l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs), P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriods
