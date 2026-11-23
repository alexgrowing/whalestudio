import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DegreeL2RangeHypothesis
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionChange
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeGapDS
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound

open MeasureTheory Matrix Filter Topology Finset
open scoped InnerProductSpace ContDiff Convolution

noncomputable section

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

def thrE {n : ℕ} (ε : Fin n → Bool) : ℝ :=
  max (thrDS ε) (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℕ) + 8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)))

theorem thrE_le {n : ℕ} (ε : Fin n → Bool) (hn : (5 : ℝ) ≤ n) : thrE ε ≤ 4 * (n : ℝ) ^ 3 := by
  have hpn : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hm : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ≤ n := by exact_mod_cast (min_le_left _ _).trans hpn
  have hm0 : (0 : ℝ) ≤ ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 := thrDS_le ε
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  unfold thrE
  generalize ((min (pOf ε) (qOf ε) : ℕ) : ℝ) = q at hm hm0 ⊢
  have hs0 : 0 ≤ Real.sqrt (2 * q) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by linarith)
  have hsn : Real.sqrt (2 * q) ≤ n := by nlinarith
  apply max_le
  · linarith
  · have hnq : (n : ℝ) * q ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hm (by linarith)
    nlinarith

end Formalism.MainNotions.GapDS

namespace Formalism.MainNotions.BridgeCPX

open Formalism.MainNotions.S Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HCMultDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    Formalism.MainNotions.GapDS.thrDS ε < h → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

def HCAdmDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    Formalism.MainNotions.GapDS.thrDS ε < h → AdmProjAt ε σ

theorem HCAdmDSG_of (h : HCMultDSG) (hc : CompactProj) : HCAdmDSG := by
  intro n ε lam H _ _ _ σ hl hDS g hg hng x hx
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨S, hfd, hxS, hst⟩ := hx
  obtain ⟨e, he, hfix, hrange⟩ := hc (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  exact ⟨e, _, he, h n ε lam H σ hl hDS g hg hng S hfd hst, hrange, hfix x hxS⟩

theorem HCAdmDSG_of_mult (h : HCMultDSG) : HCAdmDSG := HCAdmDSG_of h compactProj

section Final

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData Formalism.BasicNotions

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Final

end Formalism.MainNotions.BridgeCPX

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def DiscreteSeriesExistsG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε < h →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

def LowKMultOneG : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
    ∀ S S' : Submodule ℂ H, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S → IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S'

end Formalism.MainNotions.DiscreteSeriesWeylDimension

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S

def deg_DSUniqG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsHCParam lam → IsDS ε lam σ → IsDS ε lam σ' → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x)

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions

def DiscreteSeriesUniqueBesselGapped : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ →
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (σ' : CayleySignature.Mat k r → (H' →L[ℂ] H')),
    IsDSHpk k r ε lam σ' →
  ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x)

end Formalism.MainNotions.LeviCoordinates

namespace Formalism.MainNotions.TheoremBConstants

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def LitFormalDegreeG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε < h →
      v ≠ 0 → fdegOf (Formalism.REAL.muG ε) σ v = c * fdegHC lam

end Formalism.MainNotions.TheoremBConstants

namespace Formalism.MainNotions.LowestKTypeMultiplicity

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def KFinSmoothG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end Formalism.MainNotions.LowestKTypeMultiplicity

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants
open Formalism.QuantumDeterminants.WeylGroupFacts

def KFinSmoothG : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)),
    IsDSHpk k r ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrDS ε < h →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

def gNear (D : D7) (Cg : ℝ) : ℝ :=
  Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)

end Formalism.MainNotions.DiscreteSeriesInnerProducts

end

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

noncomputable def thrX {n : ℕ} (ε : Fin n → Bool) : ℝ :=
  max (thrDS ε) (120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2))

theorem thrE_le_thrX {n : ℕ} (ε : Fin n → Bool) : thrE ε ≤ thrX ε := by
  have hpn : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  unfold thrE thrX
  refine max_le_max le_rfl ?_
  obtain ⟨m, hmd⟩ : ∃ m, min (pOf ε) (qOf ε) = m := ⟨_, rfl⟩
  have hmn : m ≤ n := hmd ▸ (min_le_left _ _).trans hpn
  rw [hmd]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, mul_zero, zero_add, Real.sqrt_zero]
    rw [Real.zero_rpow (by norm_num)]
    simp
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast h0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h0.trans_le hmn
    have hmr : (m : ℝ) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by
      calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    have hs0 : 0 ≤ Real.sqrt (2 * (m : ℝ)) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (2 * (m : ℝ)) ^ 2 = 2 * m := Real.sq_sqrt (by linarith)
    have hs : Real.sqrt (2 * (m : ℝ)) ≤ 2 * m := by nlinarith
    have hA := mul_le_mul_of_nonneg_left hmr (show (0 : ℝ) ≤ 120 * n by positivity)
    have hnm : (m : ℝ) ≤ n * m := by nlinarith
    nlinarith

theorem thrX_le {n : ℕ} (ε : Fin n → Bool) (hn : (900 : ℝ) ≤ n) : thrX ε ≤ 4 * (n : ℝ) ^ 3 := by
  have hpn : pOf ε ≤ n := (Finset.card_filter_le _ _).trans (by simp)
  have hmn : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ≤ n := by exact_mod_cast (min_le_left _ _).trans hpn
  have hm0 : (0 : ℝ) ≤ ((min (pOf ε) (qOf ε) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hm0 hmn (by norm_num)
  have hsplit : (n : ℝ) ^ ((3 : ℝ) / 2) = n * Real.sqrt n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have h30 : (30 : ℝ) ≤ Real.sqrt (n : ℝ) := by nlinarith
  have h1 := thrDS_le ε
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  unfold thrX
  apply max_le
  · linarith
  · rw [hsplit] at hpow
    have hB : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * n * (n * Real.sqrt n) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have hC : 120 * (n : ℝ) * (n * Real.sqrt n) ≤ 4 * (n : ℝ) ^ 3 := by
      generalize Real.sqrt (n : ℝ) = s at hs0 hs2 h30 ⊢
      rw [← hs2]
      nlinarith [mul_nonneg (pow_nonneg hs0 5) (sub_nonneg.2 h30)]
    linarith

end Formalism.MainNotions.GapDS

namespace Formalism.MainNotions.DiscreteSeriesWeylDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def DiscreteSeriesExistsFallback : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    Formalism.MainNotions.GapDS.thrX ε < h →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

theorem exists_fallback_of_exists_gapped (h : DiscreteSeriesExistsG) : DiscreteSeriesExistsFallback := by
  intro n ε lam hl g hg hlt
  exact h n ε lam hl g hg (lt_of_le_of_lt (Formalism.MainNotions.GapDS.thrE_le_thrX ε) hlt)

end Formalism.MainNotions.DiscreteSeriesWeylDimension

namespace Formalism.MainNotions.TheoremBConstants

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

def FormalDegreeProportionalOfGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H), IsHCParam lam → IsDS ε lam σ → ∀ h : ℝ,
      Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrX ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      v ≠ 0 → fdegOf (Formalism.REAL.muG ε) σ v = c * fdegHC lam

end Formalism.MainNotions.TheoremBConstants

namespace Formalism.MainNotions.DiscreteSeriesInnerProducts

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants
open Formalism.QuantumDeterminants.WeylGroupFacts

end Formalism.MainNotions.DiscreteSeriesInnerProducts

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.PlaceDegreeData

end Formalism.MainNotions.GapDS
