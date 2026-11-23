import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Corev.mem_latO_line_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  intro D k _ _ _ _ ι p I P hP n'' _ _ σ B' γ γ₀ M' Λ' hM' hγ S LS hLS x hx
  have hu : (B'.o.resT S).symm (0, x) = B'.o.jB ⬝ x := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  have hMx : MxAt P (B'.o.jB ⬝ x) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)
  obtain ⟨hrk, hne⟩ := B'.line
  have hr : ∀ r r' : Fin B'.L.rank, r = r' := fun r r' => Fin.ext (by omega)
  let r₀ : Fin B'.L.rank := ⟨0, by omega⟩
  have hζ : B'.ζ r₀ ≠ 0 := by
    intro h0
    apply hne
    have : B'.ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hjB : ∀ d : AE D, B'.o.jB *ᵥ (d • ratV B'.ζ) = fun r => d * incA D (vecB B'.o B'.ζ r) := by
    intro d
    funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ y, (B'.o.jB ⬝ x) *ᵥ y ∈ latV B'.V₀ M' P ↔ ∃ d : AE D, d ∈ idAt D P ∧
      (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧
        (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k]) := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have hz : ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ ∈ idAt D P := by
        simp only [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r₀ j)
      set d : AE D := ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ * incA D (B'.ζ r₀)⁻¹ with hd
      have hdI : d ∈ idAt D P := Ideal.mul_mem_right _ _ hz
      have hzd : (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ := by
        funext r
        rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, hd, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
      rw [hzd, hjB] at h
      exact ⟨d, hdI, hzd, (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).1 h⟩
    · rintro ⟨d, hdI, hzd, hc⟩
      rw [hzd, hjB]
      exact (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).2 hc
  rw [hu, GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S B'.V₀ LS M' hLS hM' P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP B'.V₀ M']
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (key y).1 (h y hy)
  · intro h
    exact ⟨hMx, fun y hy => (key y).2 (h y hy)⟩
