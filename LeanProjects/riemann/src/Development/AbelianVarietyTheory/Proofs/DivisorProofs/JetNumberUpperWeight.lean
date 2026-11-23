import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.JetsUb

open GlobalTheory.AllWt GlobalTheory.CompHS

theorem floorGaps_sub_le {N : ℕ} (a : ℕ) (m : ℤ) (v : Fin N → ℤ) (hv : Antitone v) {i j : Fin N} (hij : i ≤ j) :
    floorGaps a m v i - floorGaps a m v j ≤ v i - v j := by
  have hij' : (i : ℕ) ≤ j := hij
  have e1 : floorGaps a m v i - floorGaps a m v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k / m := by
    simp only [floorGaps, ofGaps]
    rw [← Finset.sum_range_add_sum_Ico _ hij']
    ring
  have e2 : v i - v j = ∑ k ∈ Finset.Ico (i : ℕ) j, gap v k := by
    have h1 := ofGaps_gap v i i
    have h2 := ofGaps_gap v i j
    simp only [ofGaps] at h1 h2
    rw [← Finset.sum_range_add_sum_Ico _ hij'] at h2
    linarith
  rw [e1, e2]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' := Finset.mem_Ico.1 hk
  have hN : k + 1 < N := by have := j.2; omega
  have h0 : 0 ≤ gap v k := by
    rw [gap, dif_pos hN]
    have := hv (show (⟨k, by omega⟩ : Fin N) ≤ ⟨k + 1, hN⟩ from Fin.mk_le_mk.2 (by omega))
    omega
  exact Int.ediv_le_self _ h0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem thA_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) (x : (E →+* ℂ) × ℕ) :
    thA Dw P.ub n x ≤ thA Dw P.u₁ n x := by
  have hd : ∀ τ (i j : Fin (Dw.p + Dw.q)), i ≤ j → P.ub τ i - P.ub τ j ≤ P.u₁ τ i - P.u₁ τ j :=
    fun τ i j h => floorGaps_sub_le _ _ _ (hu τ) h
  show (thExpZ Dw P.ub n x).toNat ≤ (thExpZ Dw P.u₁ n x).toNat
  apply Int.toNat_le_toNat
  obtain ⟨σ, i⟩ := x
  rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · by_cases hi : i < Dw.p
    · rw [thExpZ_big _ n τ i hi, thExpZ_big _ n τ i hi]
      have := hd τ ⟨i, by omega⟩ ⟨Dw.p - 1, by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_big_ge _ n τ i (by omega), thExpZ_big_ge _ n τ i (by omega)]
  · by_cases hi : i < Dw.q
    · rw [thExpZ_small _ n hp τ i hi, thExpZ_small _ n hp τ i hi]
      have := hd τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (Fin.mk_le_mk.2 (by omega))
      omega
    · rw [thExpZ_small_ge _ n τ i (by omega), thExpZ_small_ge _ n τ i (by omega)]

theorem DF_ub_le (P : WtPar Dw) (n : ℕ) (hp : 0 < Dw.p) (hu : ∀ τ, Antitone (P.u₁ τ)) :
    Formalism.L2.Pj.DF Dw (thA Dw P.ub n) ≤ Formalism.L2.Pj.DF Dw (thA Dw P.u₁ n) := by
  unfold Formalism.L2.Pj.DF
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => thA_ub_le P n hp hu (τ, i)

end GlobalTheory.RefSum.JetsUb

theorem GlobalTheory.RefSum.JetNum.of_le {D : Formalism.BasicNotions.D7} {d d' : ℕ} {c : ℝ} (h : GlobalTheory.RefSum.JetNum D d c) (hd : d' ≤ d) :
    GlobalTheory.RefSum.JetNum D d' c := fun k => by
  obtain ⟨h1, h2, h3⟩ := h k
  have hd' : (d' : ℝ) ≤ d := by exact_mod_cast hd
  have hr : 0 ≤ GlobalTheory.PtTie.rr0 D := by unfold GlobalTheory.PtTie.rr0; positivity
  refine ⟨by omega, ?_, le_trans ?_ h3⟩
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd' (by positivity)) h2
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (d' : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 2
    linarith

theorem GlobalTheory.RefSum.JetsUb.jetNum_ub : Size → Lifts fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub (GlobalTheory.RefSum.nCol (dat p i)))) (1 / 2500) := by
  intro hS
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and hS (GlobalTheory.T.weight_parameter_strict_antitone hS)) (GlobalTheory.RefSum.NumPt.numbers_at_point hS)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, _, hA⟩, ⟨_, _, hB⟩⟩, ⟨_, _, hC⟩⟩
  obtain ⟨x0, h⟩ := GlobalTheory.CovTop.EvTied.and (GlobalTheory.CovTop.EvTied.and hA hB) hC
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi => ?_⟩
  obtain ⟨⟨hA, hB⟩, hC⟩ := h x hx hle ι p hp
  obtain ⟨⟨u1, hu⟩, -⟩ := (hA i).2.2.2.2.2.2 hi
  obtain ⟨hp1, -, -, hq, hanti, -⟩ := hB i hi
  have j := (hC i hi u1 hu).1
  rw [hq u1 hu] at j
  exact j.of_le (GlobalTheory.RefSum.JetsUb.DF_ub_le _ _ hp1 fun τ => (hanti τ).1.antitone)
