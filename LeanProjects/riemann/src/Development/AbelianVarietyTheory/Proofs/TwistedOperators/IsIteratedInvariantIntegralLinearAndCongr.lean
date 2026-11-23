import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal.NIterLin

section
variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quot_sum {I : Type} (S : Finset I) (x : I → ℂ) (F : I → G → ℂ) (z : I → ℂ)
    (hF : ∀ n ∈ S, IsQuotIntL1 μR μG (F n) (z n)) :
    IsQuotIntL1 μR μG (fun g => ∑ n ∈ S, x n * F n g) (∑ n ∈ S, x n * z n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun g : G => ∑ n ∈ (∅ : Finset I), x n * F n g) = 0 := by funext g; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := (hF a (Finset.mem_insert_self _ _)).smul (x a)
    have h2 := ih (fun n hn => hF n (Finset.mem_insert_of_mem hn))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext g
    simp [Finset.sum_insert ha]
end

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
  {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i))

theorem lin (l : List ι) : ∀ (h : ∀ i, H i) (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ),
    (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n) := by
  induction l with
  | nil =>
    intro h I S x z q hq
    simp only [NIter] at hq ⊢
    exact Finset.sum_congr rfl fun n hn => by rw [hq n hn]
  | cons i l ih =>
    intro h I S x z q hq
    classical
    simp only [NIter] at hq ⊢
    let F : I → H i → ℂ := fun n => if hn : n ∈ S then Classical.choose (hq n hn) else 0
    have hF : ∀ n ∈ S, IsQuotIntL1 (ρ i) (μ i) (F n) (z n) ∧ ∀ g, NIter ρ μ (q n) l (Function.update h i g) (F n g) := by
      intro n hn
      simp only [F, dif_pos hn]
      exact Classical.choose_spec (hq n hn)
    refine ⟨fun g => ∑ n ∈ S, x n * F n g, quot_sum S x F z fun n hn => (hF n hn).1, fun g => ?_⟩
    exact ih (Function.update h i g) I S x (fun n => F n g) q fun n hn => (hF n hn).2 g

theorem congr (l : List ι) : ∀ (h : ∀ i, H i) (q q' : (∀ i, H i) → ℂ) (z : ℂ),
    (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  induction l with
  | nil =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    rw [hz]
    exact hq h fun _ _ => rfl
  | cons i l ih =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    obtain ⟨f, hf, hf'⟩ := hz
    refine ⟨f, hf, fun g => ih (Function.update h i g) q q' (f g) (fun g' hg' => hq g' fun j hj => ?_) (hf' g)⟩
    have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun e => hj (List.mem_cons_of_mem _ e)
    rw [hg' j hjl, Function.update_of_ne hji]

end GlobalTheory.RowVal.NIterLin

theorem GlobalTheory.RowVal.niter_lin_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  intro ι _ H _ _ R ρ μ l h
  exact ⟨fun I S x z q hq => GlobalTheory.RowVal.NIterLin.lin ρ μ l h I S x z q hq,
    fun q q' z hq hz => GlobalTheory.RowVal.NIterLin.congr ρ μ l h q q' z hq hz⟩

end
