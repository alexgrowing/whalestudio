import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FfHasInfChar
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

open MeasureTheory Matrix Finset
open Formalism.REAL Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped ENNReal

namespace Formalism.MainNotions.BridgeLocGrowth

variable {n : ℕ}

abbrev q0 (ε : Fin n → Bool) : ℕ := min (pOf ε) (qOf ε)

def SUJ (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | (toM g).det = 1}
  mul_mem' := by
    intro a b ha hb
    change (toM a * toM b).det = 1
    rw [Matrix.det_mul, show (toM a).det = 1 from ha, show (toM b).det = 1 from hb, one_mul]
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ).det = 1
    exact Matrix.det_one
  inv_mem' := by
    intro a ha
    have ha' : (toM a).det = 1 := ha
    have hm : toM a⁻¹ * toM a = 1 := Units.inv_mul (a : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    change (toM a⁻¹).det = 1
    have h := congrArg Matrix.det hm
    rw [Matrix.det_mul, ha', mul_one, Matrix.det_one] at h
    exact h

theorem continuous_toM (ε : Fin n → Bool) : Continuous (fun g : UJ ε => toM g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem isClosed_SUJ (ε : Fin n → Bool) : IsClosed (SUJ ε : Set (UJ ε)) :=
  isClosed_eq (continuous_toM ε).matrix_det continuous_const

instance instMeasurableSpaceSUJ (ε : Fin n → Bool) : MeasurableSpace (SUJ ε) := borel _

instance instBorelSpaceSUJ (ε : Fin n → Bool) : BorelSpace (SUJ ε) := ⟨rfl⟩

instance instLocallyCompactSUJ (ε : Fin n → Bool) : LocallyCompactSpace (SUJ ε) :=
  (isClosed_SUJ ε).isClosedEmbedding_subtypeVal.locallyCompactSpace

def KSU (ε : Fin n → Bool) : Subgroup (SUJ ε) := (KG ε).comap (SUJ ε).subtype

instance instCompactKSU (ε : Fin n → Bool) : CompactSpace (KSU ε) := by
  have hK : IsCompact (KG ε : Set (UJ ε)) := by
    have h := isCompact_range (continuous_subtype_val : Continuous (Subtype.val : KG ε → UJ ε))
    rwa [Subtype.range_coe] at h
  have h1 : IsCompact ((KG ε : Set (UJ ε)) ∩ SUJ ε) := hK.inter_right (isClosed_SUJ ε)
  have he : Topology.IsEmbedding (fun k : KSU ε => ((k : SUJ ε) : UJ ε)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have himg : (fun k : KSU ε => ((k : SUJ ε) : UJ ε)) '' Set.univ = (KG ε : Set (UJ ε)) ∩ SUJ ε := by
    ext g
    constructor
    · rintro ⟨k, -, rfl⟩
      exact ⟨k.2, (k : SUJ ε).2⟩
    · rintro ⟨hk, hs⟩
      exact ⟨⟨⟨g, hs⟩, hk⟩, trivial, rfl⟩
  rw [← himg] at h1
  exact isCompact_univ_iff.mp (he.isInducing.isCompact_iff.mpr h1)

instance instMeasurableSpaceKSU (ε : Fin n → Bool) : MeasurableSpace (KSU ε) := borel _

instance instBorelSpaceKSU (ε : Fin n → Bool) : BorelSpace (KSU ε) := ⟨rfl⟩

def muKS (ε : Fin n → Bool) : Measure (KSU ε) := Measure.haarMeasure ⊤

def cartanH {m : ℕ} (ι κ : Fin m → Fin n) (t : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => ∑ i, if (a = κ i ∧ b = ι i) ∨ (a = ι i ∧ b = κ i) then ((t i : ℝ) : ℂ) else 0

theorem cartanH_conjTranspose {m : ℕ} (ι κ : Fin m → Fin n) (t : Fin m → ℝ) :
    (cartanH ι κ t)ᴴ = cartanH ι κ t := by
  ext a b
  simp only [cartanH, conjTranspose_apply, of_apply, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (b = κ i ∧ a = ι i) ∨ (b = ι i ∧ a = κ i)
  · have h2 : (a = κ i ∧ b = ι i) ∨ (a = ι i ∧ b = κ i) := by
      rcases h1 with ⟨h, h'⟩ | ⟨h, h'⟩
      exacts [Or.inr ⟨h', h⟩, Or.inl ⟨h', h⟩]
    rw [if_pos h1, if_pos h2, Complex.star_def, Complex.conj_ofReal]
  · have h2 : ¬((a = κ i ∧ b = ι i) ∨ (a = ι i ∧ b = κ i)) := by
      rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      exacts [h1 (Or.inr ⟨h', h⟩), h1 (Or.inl ⟨h', h⟩)]
    rw [if_neg h1, if_neg h2, star_zero]

theorem cartanH_anti {m : ℕ} {ε : Fin n → Bool} {ι κ : Fin m → Fin n} (hs : ∀ i j, ε (ι i) ≠ ε (κ j))
    (t : Fin m → ℝ) : cartanH ι κ t * Jm ε = -(Jm ε * cartanH ι κ t) := by
  ext a b
  simp only [Jm, mul_diagonal, diagonal_mul, Matrix.neg_apply, cartanH, of_apply]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : (a = κ i ∧ b = ι i) ∨ (a = ι i ∧ b = κ i)
  · rw [if_pos h1]
    have hab : ε a ≠ ε b := by
      rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [fun h => hs i i h.symm, hs i i]
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;> simp [ha, hb] at hab ⊢
  · rw [if_neg h1]
    simp

theorem cartanH_inP {m : ℕ} {ε : Fin n → Bool} {ι κ : Fin m → Fin n} (hs : ∀ i j, ε (ι i) ≠ ε (κ j))
    (t : Fin m → ℝ) : inP ε (cartanH ι κ t) :=
  (mem_cartanP_iff ε _).2 ⟨cartanH_conjTranspose ι κ t, cartanH_anti hs t⟩

def cartanU (ε : Fin n → Bool) {m : ℕ} (ι κ : Fin m → Fin n) (hs : ∀ i j, ε (ι i) ≠ ε (κ j)) (t : Fin m → ℝ) :
    UJ ε :=
  ⟨⟨NormedSpace.exp (cartanH ι κ t), NormedSpace.exp (-cartanH ι κ t), matrix_exp_mul_exp_neg _,
    matrix_exp_neg_mul_exp _⟩, f1alg_exp_inUJ ε _ (cartanH_inP hs t).1⟩

def cartanA (ε : Fin n → Bool) {m : ℕ} (ι κ : Fin m → Fin n) (hs : ∀ i j, ε (ι i) ≠ ε (κ j)) (t : Fin m → ℝ) :
    SUJ ε :=
  ⟨cartanU ε ι κ hs t, Formalism.MainNotions.LeviCoordinates.ff_det_exp ε (cartanH_inP hs t)⟩

def aPlus (m : ℕ) : Set (Fin m → ℝ) := {t | (∀ i j, i ≤ j → t j ≤ t i) ∧ ∀ i, 0 ≤ t i}

def cartanDen (n m : ℕ) (t : Fin m → ℝ) : ℝ :=
  (∏ i, ∏ j, if i < j then (Real.sinh (t i - t j) * Real.sinh (t i + t j)) ^ 2 else 1) *
    ∏ i, (Real.sinh (2 * t i) * Real.sinh (t i) ^ (2 * (n - 2 * m)))

def CartanIntegrationFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), 1 ≤ q0 ε →
    ∃ (ι κ : Fin (q0 ε) → Fin n) (_ : Function.Injective ι) (_ : Function.Injective κ)
      (hs : ∀ i j, ε (ι i) ≠ ε (κ j)),
      ∀ μ : Measure (SUJ ε), μ.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧
        ∀ F : SUJ ε → ℝ, Continuous F → HasCompactSupport F → (∀ g, 0 ≤ F g) →
          ∫⁻ g, ENNReal.ofReal (F g) ∂μ = ENNReal.ofReal c *
            ∫⁻ k₁ : KSU ε, ∫⁻ t in aPlus (q0 ε), ∫⁻ k₂ : KSU ε,
              ENNReal.ofReal (F ((k₁ : SUJ ε) * cartanA ε ι κ hs t * (k₂ : SUJ ε)) * cartanDen n (q0 ε) t)
                ∂muKS ε ∂volume ∂muKS ε

section Entries

variable {m : ℕ} {ε : Fin n → Bool} {ι κ : Fin m → Fin n}

theorem cartanH_κι (hκ : Function.Injective κ) (hsg : ∀ i j, ε (ι i) ≠ ε (κ j)) (t : Fin m → ℝ) (i : Fin m) :
    cartanH ι κ t (κ i) (ι i) = t i := by
  simp only [cartanH, of_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
  · intro j _ hji
    rw [if_neg]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hji (hκ h1).symm
    · exact hsg j i (by rw [h1])
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem cartanH_ικ (hι : Function.Injective ι) (hsg : ∀ i j, ε (ι i) ≠ ε (κ j)) (t : Fin m → ℝ) (i : Fin m) :
    cartanH ι κ t (ι i) (κ i) = t i := by
  simp only [cartanH, of_apply]
  rw [Finset.sum_eq_single i]
  · rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
  · intro j _ hji
    rw [if_neg]
    rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · exact hsg i j (by rw [h1])
    · exact hji (hι h1).symm
  · intro h
    exact absurd (Finset.mem_univ i) h

end Entries

end Formalism.MainNotions.BridgeLocGrowth
