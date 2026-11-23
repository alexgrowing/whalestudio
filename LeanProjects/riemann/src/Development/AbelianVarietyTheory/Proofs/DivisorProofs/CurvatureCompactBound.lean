import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

namespace GlobalTheory.CurvBound

open GlobalTheory.HermFrame ComplexConjugate

variable {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]

theorem IsSesq_zero_left {F : V → V → M} (hF : IsSesq F) (y : V) : F 0 y = 0 := by
  have h := hF.add_left 0 0 y
  simpa using h

theorem IsSesq_zero_right {F : V → V → M} (hF : IsSesq F) (x : V) : F x 0 = 0 := by
  have h := hF.add_right x 0 0
  simpa using h

theorem IsSesq_sum_left {ι : Type*} {F : V → V → M} (hF : IsSesq F) (s : Finset ι) (f : ι → V)
    (y : V) : F (∑ i ∈ s, f i) y = ∑ i ∈ s, F (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsSesq_zero_left hF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hF.add_left, ih]

theorem IsSesq_sum_right {ι : Type*} {F : V → V → M} (hF : IsSesq F) (s : Finset ι) (f : ι → V)
    (x : V) : F x (∑ i ∈ s, f i) = ∑ i ∈ s, F x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsSesq_zero_right hF]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hF.add_right, ih]

theorem IsSesq_expand {d : ℕ} {F : (Fin d → ℂ) → (Fin d → ℂ) → M} (hF : IsSesq F)
    (ξ η : Fin d → ℂ) :
    F ξ η = ∑ k, ∑ l, (ξ k * conj (η l)) • F (Pi.single k 1) (Pi.single l 1) := by
  have hv : ∀ v : Fin d → ℂ, v = ∑ i, v i • (Pi.single i 1 : Fin d → ℂ) := fun v => by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv ξ, hv η]
  rw [IsSesq_sum_left hF]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hF.smul_left, IsSesq_sum_right hF, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hF.smul_right, smul_smul, mul_comm]

theorem curv_entries_bound : ∀ (e n : ℕ) (U K : Set (Fin e → ℂ))
    (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), GlobalTheory.HermFrame.IsPosFrame U H₀ → IsCompact K →
    K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ ξ η : Fin e → ℂ,
      ∑ a, ∑ b, ‖GlobalTheory.HermFrame.curv H₀ z ξ η a b‖ ≤ B * ‖ξ‖ * ‖η‖ := by
  intro e n U K H₀ hH hK hKU
  have hf := hH.isHermFrame
  let g : (Fin e → ℂ) → ℝ := fun z => ∑ a, ∑ b, ∑ k, ∑ l,
    ‖curv H₀ z (Pi.single k 1) (Pi.single l 1) a b‖
  have hc : ContinuousOn g K := by
    intro z hz
    have hz' := hKU hz
    have h0 : ∀ k l : Fin e, MContDiffAt 0
        (fun x => curv H₀ x (Pi.single k 1) (Pi.single l 1)) z := fun k l =>
      (hf.mContDiffAt hz').curv (hf.isUnit z hz') (j := 0) (by first | norm_cast | simp | exact_mod_cast (le_top : ((2 : ℕ∞) : WithTop ℕ∞) ≤ _)) _ _
    refine ContinuousAt.continuousWithinAt ?_
    exact tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ =>
      tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ =>
        ((h0 k l a b).continuousAt).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun z hz ξ η => ?_⟩
  have hz' := hKU hz
  have hs := isSesq_curv (hf.two hz') (hf.isUnit z hz')
  have hgz : g z ≤ max C 0 := (Real.le_norm_self _).trans ((hC z hz).trans (le_max_left _ _))
  have hent : ∀ a b, ‖curv H₀ z ξ η a b‖ ≤
      ‖ξ‖ * ‖η‖ * ∑ k, ∑ l, ‖curv H₀ z (Pi.single k 1) (Pi.single l 1) a b‖ := by
    intro a b
    rw [IsSesq_expand hs ξ η]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := norm_le_pi_norm ξ k
    have h2 := norm_le_pi_norm η l
    have h3 := norm_nonneg (curv H₀ z (Pi.single k 1) (Pi.single l 1) a b)
    gcongr
  calc ∑ a, ∑ b, ‖curv H₀ z ξ η a b‖
      ≤ ∑ a, ∑ b, ‖ξ‖ * ‖η‖ * ∑ k, ∑ l, ‖curv H₀ z (Pi.single k 1) (Pi.single l 1) a b‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hent a b
    _ = ‖ξ‖ * ‖η‖ * g z := by simp only [g, Finset.mul_sum]
    _ ≤ ‖ξ‖ * ‖η‖ * max C 0 := by gcongr
    _ = max C 0 * ‖ξ‖ * ‖η‖ := by ring

end GlobalTheory.CurvBound
