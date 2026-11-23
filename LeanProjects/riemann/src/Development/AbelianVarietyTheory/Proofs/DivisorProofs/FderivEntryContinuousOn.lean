import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open scoped ComplexOrder ContDiff
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.QuasiPlurisubharmonic ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm GlobalTheory.HermFrame

namespace GlobalTheory.FrameCompact

variable {D n : ℕ} {V : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → Matrix (Fin n) (Fin n) ℂ}

end GlobalTheory.FrameCompact

namespace GlobalTheory.FrameCompact

variable {D n : ℕ} {V : Set (Fin D → ℂ)} {F : (Fin D → ℂ) → Matrix (Fin n) (Fin n) ℂ}

theorem norm_del_apply_le (u : (Fin D → ℂ) → ℂ) (z ξ : Fin D → ℂ) :
    ‖del u z ξ‖ ≤ ‖fderiv ℝ u z‖ * ‖ξ‖ :=
  ((del u z).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right (GlobalTheory.norm_linPart_le _) (norm_nonneg _))

theorem inv_entry_continuousOn (hF : IsPosFrame V F) (a c : Fin n) :
    ContinuousOn (fun z => ((F z)ᵀ)⁻¹ a c) V := fun z hz => by
  have h := hF.isHermFrame
  have hu : IsUnit ((F z)ᵀ).det := by rw [det_transpose]; exact h.isUnit z hz
  exact ((((h.mContDiffAt hz).transpose.inv hu) a c).continuousAt).continuousWithinAt

theorem fderiv_entry_continuousOn (hF : IsPosFrame V F) (b c : Fin n) :
    ContinuousOn (fun z => fderiv ℝ (fun x => F x b c) z) V :=
  (hF.smooth b c).continuousOn_fderiv_of_isOpen hF.isOpen (by exact_mod_cast le_top)

theorem exists_conn_bound (hF : IsPosFrame V F) {K : Set (Fin D → ℂ)} (hK : K ⊆ V)
    (hKc : IsCompact K) : ∃ β : ℝ, ∀ z ∈ K, ∀ (ξ : Fin D → ℂ) (a b : Fin n),
      ‖conn F z ξ a b‖ ≤ β * ‖ξ‖ := by
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn
    (f := fun z => ∑ b, ∑ c, ‖fderiv ℝ (fun x => F x b c) z‖)
    (continuousOn_finset_sum _ fun b _ => continuousOn_finset_sum _ fun c _ =>
      ((fderiv_entry_continuousOn hF b c).mono hK).norm)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn
    (f := fun z => ∑ a, ∑ c, ‖((F z)ᵀ)⁻¹ a c‖)
    (continuousOn_finset_sum _ fun a _ => continuousOn_finset_sum _ fun c _ =>
      ((inv_entry_continuousOn hF a c).mono hK).norm)
  have e1 : ∀ z ∈ K, ∀ b c, ‖fderiv ℝ (fun x => F x b c) z‖ ≤ M₁ := fun z hz b c => by
    refine le_trans ?_ ((le_abs_self _).trans (hM₁ z hz))
    refine le_trans ?_ (Finset.single_le_sum (f := fun b => ∑ c, ‖fderiv ℝ (fun x => F x b c) z‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ b))
    exact Finset.single_le_sum (f := fun c => ‖fderiv ℝ (fun x => F x b c) z‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  have e2 : ∀ z ∈ K, ∀ a c, ‖((F z)ᵀ)⁻¹ a c‖ ≤ M₂ := fun z hz a c => by
    refine le_trans ?_ ((le_abs_self _).trans (hM₂ z hz))
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ c, ‖((F z)ᵀ)⁻¹ a c‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a))
    exact Finset.single_le_sum (f := fun c => ‖((F z)ᵀ)⁻¹ a c‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
  refine ⟨n * (M₂ * M₁), fun z hz ξ a b => ?_⟩
  have hterm : ∀ c, ‖((F z)ᵀ)⁻¹ a c * mdel F z ξ b c‖ ≤ M₂ * (M₁ * ‖ξ‖) := fun c => by
    rw [norm_mul]
    refine mul_le_mul (e2 z hz a c) ?_ (norm_nonneg _) ((norm_nonneg _).trans (e2 z hz a c))
    rw [mdel_apply]
    exact (norm_del_apply_le _ z ξ).trans
      (mul_le_mul_of_nonneg_right (e1 z hz b c) (norm_nonneg _))
  calc ‖conn F z ξ a b‖ = ‖∑ c, ((F z)ᵀ)⁻¹ a c * mdel F z ξ b c‖ := by
        rw [conn, mul_apply]; rfl
    _ ≤ ∑ c, ‖((F z)ᵀ)⁻¹ a c * mdel F z ξ b c‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin n, M₂ * (M₁ * ‖ξ‖) := Finset.sum_le_sum fun c _ => hterm c
    _ = n * (M₂ * M₁) * ‖ξ‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.FrameCompact
