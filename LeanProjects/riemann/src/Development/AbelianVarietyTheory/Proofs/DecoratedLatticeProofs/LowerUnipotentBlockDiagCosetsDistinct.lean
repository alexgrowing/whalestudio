import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.CosetDistinct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

local notation "E" m => emb₂ k (Equiv.refl (A ⊕ D)) (1, m)

theorem lowU_mul_lowU (a b : Matrix D A k) : (lowU a * lowU b : GL (A ⊕ D) k) = lowU (a + b) := by
  ext1; rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]; simp [add_comm]

theorem emb_one_inv (m : GL D k) : (E m)⁻¹ = (E m⁻¹) := by rw [← map_inv]; simp

theorem quot_eq (ν ν' : Matrix D A k) (a b w : GL D k) :
    (lowU ν * (E a) * (E w))⁻¹ * (lowU ν' * (E b) * (E w)) =
      lowU (((a * w)⁻¹ : GL D k).1 * (ν' - ν)) * (E ((a * w)⁻¹ * (b * w))) := by
  have h : lowU ν' = (lowU ν * lowU (ν' - ν) : GL (A ⊕ D) k) := by rw [lowU_mul_lowU]; congr 1; abel
  rw [h, ← emb_mul_emb (a * w)⁻¹ (b * w), ← emb_mul_emb b w,
    ← mul_assoc (lowU (((a * w)⁻¹ : GL D k).1 * (ν' - ν))), ← emb_mul_lowU, ← emb_one_inv,
    ← emb_mul_emb a w]
  group

theorem lowU_emb_apply_inr_inl (X : Matrix D A k) (Y : GL D k) (i : D) (j : A) :
    (lowU X * (E Y) : GL (A ⊕ D) k).1 (.inr i) (.inl j) = X i j := by
  rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp

theorem mem_KO_of_emb {Y : GL D k} (h : (E Y) ∈ KO k (A ⊕ D)) : Y ∈ KO k D := by
  rw [GlobalTheory.StepData.mem_KO] at h ⊢
  refine ⟨fun i j => by simpa [val_emb_one] using h.1 (.inr i) (.inr j), fun i j => ?_⟩
  have := h.2 (.inr i) (.inr j)
  rw [emb_one_inv, val_emb_one] at this; simpa using this

theorem inv_mul_of_eq {G : Type*} [Group G] {x a w b : G} (h : x = a * w * b) (c : G) :
    x⁻¹ * c = b⁻¹ * ((a * w)⁻¹ * c) := by subst h; group

theorem mul_inv_of_eq {G : Type*} [Group G] {x a w b : G} (h : x = a * w * b) : x * b⁻¹ = a * w := by
  subst h; group

theorem coset_uniq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ _ s R hR κ κ' hκ g hg g' hg' ν ν' hmem
  rw [mtor_eq (A := A), quot_eq] at hmem
  obtain ⟨hk1, hk1', hgeq⟩ := hκ g hg
  obtain ⟨hk2, hk2', hg'eq⟩ := hκ g' hg'
  have hXm : ∀ i a, valuation k (((((κ g * torusElt k D ϖ (indic s))⁻¹ : GL D k).1 * (ν' - ν))) i a) < 1 :=
    fun i a => by
      have := (mem_parahoric.1 hmem).2 i a
      rwa [lowU_emb_apply_inr_inl] at this
  have hYK : (κ g * torusElt k D ϖ (indic s))⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
    apply mem_KO_of_emb (A := A)
    have hJ := (parahoric k A D).mul_mem ((parahoric k A D).inv_mem (lowU_mem hXm)) hmem
    rw [inv_mul_cancel_left] at hJ
    exact (mem_parahoric.1 hJ).1
  have hgg : g = g' := by
    obtain ⟨g0, _, huniq⟩ := hR.2 (κ g') hk2
    have h1 : g⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
      rw [inv_mul_of_eq hgeq]; exact mul_mem (inv_mem hk1') hYK
    have h2 : g'⁻¹ * (κ g' * torusElt k D ϖ (indic s)) ∈ KO k D := by
      rw [inv_mul_of_eq hg'eq, inv_mul_cancel, mul_one]; exact inv_mem hk2'
    exact (huniq g ⟨hg, h1⟩).trans (huniq g' ⟨hg', h2⟩).symm
  refine ⟨hgg, ((κ' g)⁻¹ : GL D k).1 * (((κ g * torusElt k D ϖ (indic s))⁻¹ : GL D k).1 * (ν' - ν)), ?_, ?_⟩
  · exact GlobalTheory.StepData.IntM.mul_maxM (GlobalTheory.StepData.intM_of_mem_KO (inv_mem hk1')) hXm
  · rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_of_eq hgeq, ← Matrix.mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.CosetDistinct

end
