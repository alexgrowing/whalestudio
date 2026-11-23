import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsInfinite

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap nonZeroDivisors Classical
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published NumberField.mixedEmbedding

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pair_sum {α : Type*} [Zero α] {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Summable f) :
    Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => f (ξ.1 0) * f (ξ.1 1)) ∧
      ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤
        2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := by
  set f' : α → ℝ := fun x => if x = 0 then 0 else f x with hf'def
  have hf'0 : ∀ x, 0 ≤ f' x := fun x => by
    simp only [f']; split_ifs
    · exact le_rfl
    · exact hf0 x
  have hf'le : ∀ x, f' x ≤ f x := fun x => by
    simp only [f']; split_ifs
    · exact hf0 x
    · exact le_rfl
  have hf' : Summable f' := hf.of_nonneg_of_le hf'0 hf'le
  have hP1 : Summable (fun p : α × α => f' p.1 * f p.2) := hf'.mul_of_nonneg hf hf'0 hf0
  have hP2 : Summable (fun p : α × α => f p.1 * f' p.2) := hf.mul_of_nonneg hf' hf0 hf'0
  set g : α × α → ℝ := fun p => f' p.1 * f p.2 + f p.1 * f' p.2 with hgdef
  have hg : Summable g := hP1.add hP2
  set e : (Fin 2 → α) ≃ α × α := finTwoArrowEquiv α
  have hge : ∀ ξ : Fin 2 → α, g (e ξ) = f' (ξ 0) * f (ξ 1) + f (ξ 0) * f' (ξ 1) := fun ξ => rfl
  have hQ : Summable (fun ξ : Fin 2 → α => g (e ξ)) := (e.summable_iff (f := g)).2 hg
  have hQ0 : ∀ ξ : Fin 2 → α, 0 ≤ g (e ξ) := fun ξ => by
    rw [hge]
    exact add_nonneg (mul_nonneg (hf'0 _) (hf0 _)) (mul_nonneg (hf0 _) (hf'0 _))
  have hle : ∀ ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤ g (e ξ.1) := by
    intro ξ
    rw [hge]
    by_cases h0 : ξ.1 0 = 0
    · have h1 : ξ.1 1 ≠ 0 := by
        intro h1
        apply ξ.2
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have : f' (ξ.1 1) = f (ξ.1 1) := by simp only [f', if_neg h1]
      rw [this]
      linarith [mul_nonneg (hf'0 (ξ.1 0)) (hf0 (ξ.1 1))]
    · have : f' (ξ.1 0) = f (ξ.1 0) := by simp only [f', if_neg h0]
      rw [this]
      linarith [mul_nonneg (hf0 (ξ.1 0)) (hf'0 (ξ.1 1))]
  have hQs : Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => g (e ξ.1)) := hQ.subtype _
  have hS : Summable (fun ξ : {ξ : Fin 2 → α // ξ ≠ 0} => f (ξ.1 0) * f (ξ.1 1)) :=
    hQs.of_nonneg_of_le (fun ξ => mul_nonneg (hf0 _) (hf0 _)) hle
  refine ⟨hS, ?_⟩
  have h1 : ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤
      ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, g (e ξ.1) := hS.tsum_le_tsum hle hQs
  have h2 : ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, g (e ξ.1) ≤ ∑' ξ : Fin 2 → α, g (e ξ) :=
    hQ.tsum_subtype_le _ {ξ | ξ ≠ 0} hQ0
  have h3 : ∑' ξ : Fin 2 → α, g (e ξ) = ∑' p : α × α, g p := e.tsum_eq g
  have h4 : ∑' p : α × α, g p = (∑' x, f' x) * (∑' x, f x) + (∑' x, f x) * (∑' x, f' x) := by
    rw [hgdef, hP1.tsum_add hP2, hf'.tsum_mul_tsum hf hP1, hf.tsum_mul_tsum hf' hP2]
  have h5 : (∑' x, f' x) * (∑' x, f x) + (∑' x, f x) * (∑' x, f' x) = 2 * (∑' x, f x) * ∑' x, f' x := by
    ring
  calc ∑' ξ : {ξ : Fin 2 → α // ξ ≠ 0}, f (ξ.1 0) * f (ξ.1 1) ≤ 2 * (∑' x, f x) * ∑' x, f' x := by
        rw [← h5, ← h4, ← h3]; exact h1.trans h2
    _ = 2 * (∑' x, f x) * ∑' x, (if x = 0 then 0 else f x) := rfl

theorem decay1D {G : Ad F → ℂ} (hG : G ∈ schwartzBruhat F) {C : Set (IdeleGroup F)} (hC : IsCompact C)
    (w : InfinitePlace F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ C, ∀ T : {r : ℝ // 0 < r}, 1 ≤ (T : ℝ) →
      Summable (fun x : F => ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ∧
      ∑' x : F, (if x = 0 then 0 else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ≤ ((T : ℝ) ^ 3)⁻¹ * M ∧
      ∑' x : F, ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖ ≤ ‖G 0‖ + M := by
  obtain ⟨u, hu, hFu⟩ := exists_decay_bound w hG hC 3
  refine ⟨∑' ξ, |u ξ|, tsum_nonneg fun _ => abs_nonneg _, fun a ha T hT => ?_⟩
  have hs : Summable (fun x : F => ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) :=
    summable_norm_smul_algebraMap _ hG
  have hT0 : 0 < ((T : ℝ) ^ 3)⁻¹ := inv_pos.2 (pow_pos T.2 3)
  have hT1 : ((T : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have hs' : Summable (fun x : F =>
      if x = 0 then (0 : ℝ) else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) :=
    hs.of_nonneg_of_le (fun x => by split_ifs <;> positivity) (fun x => by split_ifs <;> simp)
  have h2 : ∑' x : F, (if x = 0 then 0 else ‖G ((moduleSection w T * a) • algebraMap F (Ad F) x)‖) ≤
      ((T : ℝ) ^ 3)⁻¹ * ∑' ξ, |u ξ| := by
    rw [← tsum_mul_left]
    refine hs'.tsum_le_tsum (fun ξ => ?_) (hu.abs.mul_left _)
    split_ifs with h
    · exact mul_nonneg hT0.le (abs_nonneg _)
    · exact (hFu a ha T hT ξ h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hT0.le)
  refine ⟨hs, h2, ?_⟩
  rw [hs.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero]
  have h3 : ((T : ℝ) ^ 3)⁻¹ * ∑' ξ, |u ξ| ≤ ∑' ξ, |u ξ| :=
    mul_le_of_le_one_left (tsum_nonneg fun _ => abs_nonneg _) hT1
  have h4 := h2.trans h3
  linarith

theorem absD_scalar_mul (z : Ideles F) (g : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (ideleModule F z : ℝ) ^ 2 * absD g := by
  unfold absD
  rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_mul, map_pow,
    Positive.val_mul, Positive.val_pow]

theorem ideleModule_section_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    (ideleModule F (moduleSection (w0 F) t * (u : Ideles F)) : ℝ) = t := by
  have hu : ideleModule F (u : IdeleGroup F) = 1 := u.2
  change (ideleModule F (moduleSection (w0 F) t * (u : IdeleGroup F)) : ℝ) = t
  rw [map_mul, ideleModule_moduleSection, hu, mul_one]

theorem integrable_bound : Integrable (fun t : {r : ℝ // 0 < r} => (1 + Real.log t ^ 2)⁻¹) posRealMeasure := by
  rw [posRealMeasure_eq_map_expPos]
  change Integrable _ (Measure.map expPosHomeomorph.toMeasurableEquiv volume)
  refine (integrable_map_equiv expPosHomeomorph.toMeasurableEquiv _).2 ?_
  refine integrable_inv_one_add_sq.congr (Filter.Eventually.of_forall fun x => ?_)
  show (1 + x ^ 2)⁻¹ = (1 + Real.log (Real.exp x) ^ 2)⁻¹
  rw [Real.log_exp]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinIntegrability
