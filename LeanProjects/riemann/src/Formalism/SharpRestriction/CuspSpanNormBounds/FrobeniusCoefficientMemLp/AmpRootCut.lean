import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpUnif
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.LemmaJ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootJac : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsRootMeas L p g₀ (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

def RootHaar : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), L.c ≠ 0 → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsHaarOn (RStab k r g₀) (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

def OrbQuotEx : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsHaarOn (RStab k r g₀) μR →
    ∃ ν : Measure (PairSp k r), IsOrbQuot L g₀ μR ν

def RelAtPt : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    star L.c = L.c → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsRelStab L g₀

def CellRep : Prop :=
  ∀ (D : D7) (W : LocW D.R.k D.R.rS) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)) (θ' : ℝ)
    (νR : Measure (Mt D.R.k D.R.rS)), inWb D.R.k D.R.rS W.z → inWb D.R.k D.R.rS W.z' →
    0 < Tz D.R.k D.R.rS W.z → 0 < Tz D.R.k D.R.rS W.z' → RelPt D W.z W.z' γ p → RMeas D W γ θ' νR →
    ∃ n ∈ Nset D.R.k D.R.rS, ∃ n' ∈ Nset D.R.k D.R.rS, ∃ g₀ : MatKR D.R.k D.R.rS,
      γ = n * g₀ * n' ∧ g₀ ∈ UH (Hpk D.R.k D.R.rS) ∧ ZhatO D.R.k D.R.rS W.z W.z' g₀ = ptMat p ∧
      0 < Gf D.R.k D.R.rS W.z W.z' g₀ ∧ Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS W.z W.z' g₀) ∧
      ∃ μ₀ : Measure (Mt D.R.k D.R.rS),
        μ₀ {x | Matrix.of x ∉ Rset D.R.k D.R.rS g₀} = 0 ∧
        μ₀.map (rootCoords D.R.k D.R.rS W.z' p) =
          ENNReal.ofReal ((2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) • volume ∧
        IsQuotMeas W.μG (ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j)) νR

def AmpTransport : Prop :=
  ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W →
    ∀ (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam' A → 0 < Tr D w → 0 < Tr D w' →
    ∀ (n n' g₀ : MatKR D.R.k D.R.rS), n ∈ Nset D.R.k D.R.rS → n' ∈ Nset D.R.k D.R.rS → g₀ ∈ UH (Hpk D.R.k D.R.rS) →
    ∀ (θ' : ℝ), 0 < θ' → ∀ (μ₀ νR : Measure (Mt D.R.k D.R.rS)),
      μ₀ {x | Matrix.of x ∉ Rset D.R.k D.R.rS g₀} = 0 →
      IsQuotMeas W.μG (ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j)) νR →
      IsQuotMeas W.μG μ₀ (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) ∧
      ENNReal.ofReal (hsNormSq (A.J νR (n * g₀ * n'))) =
        ENNReal.ofReal (θ' ^ (-(2 : ℤ))) *
          ENNReal.ofReal (hsNormSq (A.J (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) g₀))

theorem conj_conj_id {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (fun x : Mt k r => fun i j => (g⁻¹ * Matrix.of (fun i j => (g * Matrix.of x * g⁻¹) i j) * g) i j) = id := by
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg
  funext x i j
  have e : Matrix.of (fun i j => (g * Matrix.of x * g⁻¹) i j) = g * Matrix.of x * g⁻¹ := rfl
  have e2 : g⁻¹ * (g * Matrix.of x * g⁻¹) * g = Matrix.of x := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  simp only [id, e, e2, Matrix.of_apply]

theorem measurable_conjL {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun x : Mt k r => fun i j => (a * Matrix.of x * b) i j) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem rootCmp_of (hCR : CellRep) (hTr : AmpTransport) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx)
    (hRA : RelAtPt) : RootCmp := by
  intro D τ w w' θ W hW lam' A hA hT hT' γ p hrel θ' hθ' νR hRM
  have hz : inWb D.R.k D.R.rS W.z := hW.2.2.1
  have hz' : inWb D.R.k D.R.rS W.z' := hW.2.2.2.1
  have hTz : Tz D.R.k D.R.rS W.z = Tr D w := hW.2.2.2.2.1
  have hTz' : Tz D.R.k D.R.rS W.z' = Tr D w' := hW.2.2.2.2.2.1
  obtain ⟨n, hn, n', hn', g₀, hγ, hg₀, hZ, hG, hMon, μ₀, hnull, hmap, hquot⟩ :=
    hCR D W γ p θ' νR hz hz' (hTz ▸ hT) (hTz' ▸ hT') hrel hRM
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    apply div_pos Real.pi_pos
    apply half_pos
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  have hgpos : (0:ℝ) < (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) :=
    mul_pos (Nat.cast_pos.2 (D.host.g_prime 0).pos) (Nat.cast_pos.2 (D.host.g_prime 1).pos)
  have hcpos : 0 < 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by positivity
  have hcnorm : ‖(toBessel D τ w w' θ W lam' A hW hA hT hT').c‖ = 2 * D.host.ka / gg D := by
    show ‖((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    rfl
  have hc0 : (toBessel D τ w w' θ W lam' A hW hA hT hT').c ≠ 0 := by
    intro h
    have h2 := congrArg (fun c : ℂ => ‖c‖) h
    simp only [norm_zero] at h2
    rw [hcnorm] at h2
    unfold gg at h2
    linarith
  have hstar : star (toBessel D τ w w' θ W lam' A hW hA hT hT').c = (toBessel D τ w w' θ W lam' A hW hA hT hT').c := by
    show star (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) = _
    rw [Complex.star_def]
    exact Complex.conj_ofReal _
  have hPt : IsPtRepO (toBessel D τ w w' θ W lam' A hW hA hT hT') p g₀ := ⟨hg₀, hZ⟩
  have hmap' : μ₀.map (rootCoords D.R.k D.R.rS (toBessel D τ w w' θ W lam' A hW hA hT hT').z' p) =
      ENNReal.ofReal ((‖(toBessel D τ w w' θ W lam' A hW hA hT hT').c‖ / (2 * Real.pi)) ^ (rootPat p).card) •
        volume := by
    rw [hcnorm]
    exact hmap
  have hRM' := hRJ D.R.k D.R.rS _ p g₀ μ₀ hPt hG hnull hmap'
  have hHaar := hRH D.R.k D.R.rS _ p g₀ μ₀ hc0 hPt hG hnull hmap'
  obtain ⟨ν, hν⟩ := hOQ D.R.k D.R.rS _ p g₀ _ hPt hG hHaar
  have hRel := hRA D.R.k D.R.rS _ p g₀ hstar hPt hG
  obtain ⟨hq0, hamp⟩ := hTr D τ w w' θ W hW lam' A hA hT hT' n n' g₀ hn hn' hg₀ θ' hθ' μ₀ νR hnull hquot
  refine ⟨g₀, μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j),
    ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j), ν,
    hPt, hG, hMon, hRel, hRM', hHaar, hν, ?_, ?_⟩
  · have hid : (fun x : Mt D.R.k D.R.rS => fun i j => (g₀⁻¹ * Matrix.of x * g₀) i j) ∘
        (fun x : Mt D.R.k D.R.rS => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j) = id :=
      conj_conj_id hg₀
    rw [Measure.map_map (measurable_conjL _ _) (measurable_conjL _ _), hid, Measure.map_id]
    exact hq0
  · rw [hγ]
    exact le_of_eq hamp

end Formalism.MainNotions.S.Pv.LemmaJ
