import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinearStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ISmulOneMemUnitaryLie

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec.WordCont

theorem continuous_apply_family {Y L E : Type} [TopologicalSpace Y] [AddCommGroup L] [Module ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (W : Y → L →ₗ[ℝ] E) (hW : ∀ x, Continuous fun y => W y x)
    {f : Y → L} (hf : Continuous f) : Continuous fun y => W y (f y) := by
  let b := Module.finBasis ℝ L
  have e : (fun y => W y (f y)) = fun y => ∑ i, b.coord i (f y) • W y (b i) := by
    funext y
    conv_lhs => rw [← b.sum_repr (f y), map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp hf).smul (hW _)

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.UnitaryLieAlgebra.unitaryLie G

variable {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem continuous_word [CompleteSpace H] (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G)
    (hσ : IsURepOn (UJset ε) σ) {Y : Type} [TopologicalSpace Y] (l : List (Y → Matrix (Fin n) (Fin n) ℂ))
    (hc : ∀ f ∈ l, Continuous f) (hm : ∀ f ∈ l, ∀ y, f y ∈ lieG G) :
    ∀ w ∈ smSub G (trRep σ P), Continuous fun y => word (trRep σ P) (l.map fun f => f y) w := by
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  induction l using List.reverseRecOn with
  | nil => intro w _; exact continuous_const
  | append_singleton l f ih =>
    intro w hw
    have hc' : ∀ f ∈ l, Continuous f := fun g hg => hc g (by simp [hg])
    have hm' : ∀ f ∈ l, ∀ y, f y ∈ lieG G := fun g hg => hm g (by simp [hg])
    have hl : ∀ y, ∀ X ∈ l.map (fun f => f y), X ∈ lieG G := fun y X hX => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hX
      exact hm' g hg y
    obtain ⟨hadd, hsm⟩ := GlobalTheory.T.derived_action_smooth_vector_real_linear n ε H σ P G hP h hσ w hw
    let W : Y → lieSub G →ₗ[ℝ] H := fun y =>
      { toFun := fun X => word (trRep σ P) (l.map fun f => f y) (dRep (trRep σ P) X w)
        map_add' := fun X Z => by
          rw [Submodule.coe_add, hadd _ X.2 _ Z.2,
            word_add hG hπ (hl y) (dRep_mem hG hπ hw X.2) (dRep_mem hG hπ hw Z.2)]
        map_smul' := fun a X => by
          rw [Submodule.coe_smul, hsm a _ X.2, word_smul hG hπ (hl y) _ (dRep_mem hG hπ hw X.2)]
          simp }
    have hf : Continuous fun y => (⟨f y, hm f (by simp) y⟩ : lieSub G) :=
      (hc f (by simp)).subtype_mk _
    have := continuous_apply_family W (fun X => ih hc' hm' _ (dRep_mem hG hπ hw X.2)) hf
    simp only [List.map_append, word_append, List.map_cons, List.map_nil, word_cons, word_nil]
    exact this

theorem word_rep {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsUnit G) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π)
    {w : H} (hw : w ∈ smSub G π) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {l : List (Matrix (Fin n) (Fin n) ℂ)} (hl : ∀ X ∈ l, X ∈ lieG G) :
    word π l (π g w) = π g (word π (l.map fun X => g⁻¹ * X * g) w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    have hl' : ∀ Y ∈ l, Y ∈ lieG G := fun Y hY => hl Y (by simp [hY])
    have hm : ∀ Y ∈ l.map (fun X => g⁻¹ * X * g), Y ∈ lieG G := fun Y hY => by
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hY
      exact conj_mem_lieG hG hg (hl' Z hZ)
    rw [word_cons, ih hl', dRep_rep hG hπ (word_mem hG hπ hm hw) hg (hl X (by simp))]
    rfl

theorem continuous_sigma (hσ : IsURepOn (UJset ε) σ) {u : Formalism.REAL.UJ ε → H} (hu : Continuous u) :
    Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) (u g) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g => σ (umat g) (u g) - σ (umat g) (u g₀)) (𝓝 g₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : (fun g : Formalism.REAL.UJ ε => ‖σ (umat g) (u g) - σ (umat g) (u g₀)‖) = fun g => ‖u g - u g₀‖ := by
      funext g
      rw [← map_sub, hσ.2.1 _ g.2]
    rw [e]
    exact tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt
  have h2 := h1.add (continuous_orbit hσ (u g₀)).continuousAt
  simpa [ContinuousAt] using h2

theorem continuous_word_translate : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, X ∈ lieG G) → ∀ w ∈ smSub G (trRep σ P), Continuous fun g : Formalism.REAL.UJ ε => word (trRep σ P) l (σ (umat g) w) := by
  intro n ε H _ _ _ σ P G hP h hσ l hl w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hmem : ∀ g : Formalism.REAL.UJ ε, P⁻¹ * umat g * P ∈ Formalism.QuantumDeterminants.UH G := fun g => conj_mem_UH hP h g.2
  have hinv : ∀ g : Formalism.REAL.UJ ε, (P⁻¹ * umat g * P)⁻¹ = P⁻¹ * umat g⁻¹ * P := fun g => by
    apply Matrix.inv_eq_right_inv
    have e : umat g * umat g⁻¹ = 1 := Units.mul_inv g.1
    calc P⁻¹ * umat g * P * (P⁻¹ * umat g⁻¹ * P) = P⁻¹ * (umat g * (P * P⁻¹) * umat g⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv _ hd, Matrix.mul_one, e, Matrix.mul_one, nonsing_inv_mul _ hd]
  have c1 : Continuous fun g : Formalism.REAL.UJ ε => P⁻¹ * umat g * P :=
    (continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const
  have c2 : Continuous fun g : Formalism.REAL.UJ ε => (P⁻¹ * umat g * P)⁻¹ := by
    simp only [hinv]
    exact c1.comp continuous_inv
  have hc := continuous_word hP h hσ
    (l.map fun X (g : Formalism.REAL.UJ ε) => (P⁻¹ * umat g * P)⁻¹ * X * (P⁻¹ * umat g * P))
    (fun f hf => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hf
      exact (c2.matrix_mul continuous_const).matrix_mul c1)
    (fun f hf g => by
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hf
      exact conj_mem_lieG hG (hmem g) (hl X hX)) w hw
  convert continuous_sigma hσ hc using 2 with g
  have := word_rep hG hπ hw (hmem g) hl
  rw [trRep_conj hP] at this
  rw [this, List.map_map]
  rfl

end GlobalTheory.SmVec.WordCont
