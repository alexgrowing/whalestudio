import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {ι : Type}

abbrev Fn (X : ι → Data E r) : Type := ∀ c : ι, Frame (X c).Ψ r → ℂ

abbrev FamWt (X : ι → Data E r) : Type := ∀ c : ι, Wt (X c).Ψ r

def constWt {X : ι → Data E r} {Ψ : Finset (E →+* ℂ)} (hΨ : ∀ c, (X c).Ψ = Ψ) (la : Wt Ψ r) :
    FamWt X :=
  fun c τ i => la ⟨τ.1, hΨ c ▸ τ.2⟩ i

abbrev FramePt (X : ι → Data E r) : Type := Σ c : ι, (X c).dom

def ptNorm {X : ι → Data E r} (la : FamWt X) (F : Fn X) (p : FramePt X) : ℝ :=
  (X p.1).pnorm (la p.1) (F p.1) p.2.1

def IsCuspSec {X : ι → Data E r} (la : FamWt X) (F : Fn X) : Prop :=
  (∀ c, F c ∈ (X c).SS (la c)) ∧ ∃ C : ℝ, ∀ p : FramePt X, ptNorm la F p ≤ C

def ZeroOff {X : ι → Data E r} (F : Fn X) : Prop :=
  ∀ c, ∀ x, x ∉ (X c).dom → F c x = 0

theorem ptNorm_add_le {X : ι → Data E r} (la : FamWt X) (F G : Fn X) (p : FramePt X) :
    ptNorm la (F + G) p ≤ ptNorm la F p + ptNorm la G p := by
  unfold ptNorm Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _)

theorem ptNorm_smul {X : ι → Data E r} (la : FamWt X) (a : ℂ) (F : Fn X) (p : FramePt X) :
    ptNorm la (a • F) p = ‖a‖ * ptNorm la F p := by
  unfold ptNorm Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]

def cuspSpace {X : ι → Data E r} (la : FamWt X) : Submodule ℂ (Fn X) where
  carrier := {F | IsCuspSec la F ∧ ZeroOff F}
  zero_mem' := by
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.1, 0, fun p => ?_⟩, fun _ _ _ => rfl⟩
    simp [ptNorm, Data.pnorm]
  add_mem' := by
    rintro F G ⟨⟨hF, C, hC⟩, hF0⟩ ⟨⟨hG, D, hD⟩, hG0⟩
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.1 _ (hF c) _ (hG c), C + D,
      fun p => (ptNorm_add_le la F G p).trans (add_le_add (hC p) (hD p))⟩, fun c x hx => ?_⟩
    simp [hF0 c x hx, hG0 c x hx]
  smul_mem' := by
    rintro a F ⟨⟨hF, C, hC⟩, hF0⟩
    refine ⟨⟨fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.2 a _ (hF c), ‖a‖ * C,
      fun p => ?_⟩, fun c x hx => ?_⟩
    · rw [ptNorm_smul]
      exact mul_le_mul_of_nonneg_left (hC p) (norm_nonneg a)
    · simp [hF0 c x hx]

def supE {X : ι → Data E r} (la : FamWt X) (F : Fn X) : ℝ≥0∞ :=
  ⨆ p : FramePt X, ENNReal.ofReal (ptNorm la F p)

def supN {X : ι → Data E r} (la : FamWt X) (F : cuspSpace la) : ℝ :=
  (supE la (F : Fn X)).toReal

theorem isCuspSec_iff_of_finite [Finite ι] {X : ι → Data E r} (la : FamWt X) (F : Fn X) :
    IsCuspSec la F ↔ ∀ c, F c ∈ (X c).SS (la c) := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  choose C hC using fun c => (h c).1.2
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun p => (hC p.1 p.2.1 p.2.2).trans (hM ⟨p.1, rfl⟩)⟩

end

end GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms
