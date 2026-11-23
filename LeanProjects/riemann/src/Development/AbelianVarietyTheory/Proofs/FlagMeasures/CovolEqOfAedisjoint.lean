import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.OrbitTerm

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

def oneInf (E : Type) [Field E] [NumberField E] (j : ℕ) : MatInf E j := fun _ a b => if a = b then 1 else 0

theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := by
  ext a b; simp [oneInf, Matrix.one_apply]

theorem of_mul (x y : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl

theorem matInf_ext {x y : MatInf E j} (h : ∀ w, Matrix.of (x w) = Matrix.of (y w)) : x = y :=
  funext fun w => Matrix.of.injective (h w)

theorem matInf_mul_assoc (x y z : MatInf E j) : x * y * z = x * (y * z) :=
  matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]

theorem oneInf_mul (x : MatInf E j) : oneInf E j * x = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.one_mul]

theorem mul_oneInf (x : MatInf E j) : x * oneInf E j = x :=
  matInf_ext fun w => by rw [of_mul, of_oneInf, Matrix.mul_one]

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  simp only [detNorm, of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem detNorm_oneInf : detNorm E j (oneInf E j) = 1 := by
  simp [detNorm, of_oneInf]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_pos_iff (x : MatInf E j) : 0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  rw [(detNorm_nonneg x).lt_iff_ne', detNorm, Finset.prod_ne_zero_iff]
  simp

theorem measurable_entry (w : InfinitePlace E) (a b : Fin j) : Measurable fun x : MatInf E j => x w a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    (measurable_pi_apply (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) w))

theorem measurable_detNorm : Measurable (detNorm E j) := by
  have h : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 := by
    refine continuous_finsetProd _ fun w _ => Continuous.pow (Continuous.norm ?_) 2
    exact Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  exact h.measurable

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  measurableSet_lt measurable_const measurable_detNorm

theorem measurable_mul_left (γ : MatInf E j) : Measurable fun g : MatInf E j => γ * g := by
  refine measurable_pi_lambda (X := fun _ : InfinitePlace E => Fin j → Fin j → ℂ) _ fun w =>
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  show Measurable fun g : MatInf E j => ∑ c, γ w a c * g w c b
  exact Finset.measurable_sum _ fun c _ => (measurable_entry w c b).const_mul _

theorem measurable_inv_entry (w : InfinitePlace E) (a b : Fin j) :
    Measurable fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b := by
  have h1 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).det :=
    Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)
  have h2 : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => (Matrix.of (x w)).adjugate a b :=
    (Continuous.matrix_adjugate (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
      (continuous_apply w)).matrix_elem a b
  have h3 := h1.measurable.inv.mul h2.measurable
  have : (fun g : MatInf E j => (Matrix.of (g w))⁻¹ a b) =
      fun g : MatInf E j => ((Matrix.of (g w)).det)⁻¹ * (Matrix.of (g w)).adjugate a b := by
    funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  rw [this]; exact h3

theorem haarGL_singular (hj : 1 ≤ j) : haarGL E j {g | 0 < detNorm E j g}ᶜ = 0 := by
  have hm : MeasurableSet {g : MatInf E j | 0 < detNorm E j g}ᶜ := measurableSet_detNorm_pos.compl
  unfold haarGL
  erw [withDensity_apply _ hm]
  refine setLIntegral_eq_zero hm fun g hg => ?_
  have h0 : detNorm E j g = 0 := le_antisymm (not_lt.1 hg) (detNorm_nonneg g)
  simp [h0, zero_pow (by omega : j ≠ 0)]

theorem haarGL_restrict (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j :=
  Measure.restrict_eq_self_of_ae_mem (haarGL_singular hj)

instance : SigmaFinite (haarGL E j) :=
  haveI : SigmaFinite (volume : Measure (Fin j → ℂ)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin j → Fin j → ℂ)) := inferInstance
  @SigmaFinite.withDensity_ofReal (InfinitePlace E → Fin j → Fin j → ℂ) _ volume inferInstance
    fun x => (detNorm E j x)⁻¹ ^ j

def embGL (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

theorem embGL_mul (γ δ : GL (Fin j) E) : embGL (γ * δ) = embGL γ * embGL δ := by
  funext w a b
  show embGL (γ * δ) w a b = ∑ c, embGL γ w a c * embGL δ w c b
  simp [embGL, Matrix.mul_apply]

theorem embGL_one : embGL (1 : GL (Fin j) E) = oneInf E j := by
  funext w a b
  simp only [embGL, oneInf, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} : x ∈ autGL E j Λ ↔
    ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧ x = embGL γ :=
  ⟨fun ⟨γ, h, h'⟩ => ⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩,
    fun ⟨γ, h, h'⟩ => ⟨γ, h, fun _ _ _ => by rw [h']; rfl⟩⟩

theorem countable_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : (autGL E j Λ).Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  have : Countable (GL (Fin j) E) := Units.val_injective.countable
  refine (Set.countable_range (embGL : GL (Fin j) E → MatInf E j)).mono fun x hx => ?_
  obtain ⟨γ, -, rfl⟩ := mem_autGL.1 hx
  exact ⟨γ, rfl⟩

theorem oneInf_mem_autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : oneInf E j ∈ autGL E j Λ :=
  mem_autGL.2 ⟨1, by simp, embGL_one.symm⟩

theorem mul_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x y : MatInf E j} (hx : x ∈ autGL E j Λ)
    (hy : y ∈ autGL E j Λ) : x * y ∈ autGL E j Λ := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  obtain ⟨δ, h', rfl⟩ := mem_autGL.1 hy
  refine mem_autGL.2 ⟨γ * δ, fun z => ?_, (embGL_mul γ δ).symm⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, h']

theorem exists_inv_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    ∃ y ∈ autGL E j Λ, y * x = oneInf E j ∧ x * y = oneInf E j := by
  obtain ⟨γ, h, rfl⟩ := mem_autGL.1 hx
  refine ⟨embGL γ⁻¹, mem_autGL.2 ⟨γ⁻¹, fun z => ?_, rfl⟩, ?_, ?_⟩
  · rw [← h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rw [← embGL_mul, inv_mul_cancel, embGL_one]
  · rw [← embGL_mul, mul_inv_cancel, embGL_one]

theorem detNorm_pos_of_mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ autGL E j Λ) :
    0 < detNorm E j x := by
  obtain ⟨y, -, h, -⟩ := exists_inv_mem_autGL hx
  have h1 := detNorm_mul y x
  rw [h, detNorm_oneInf] at h1
  refine (detNorm_nonneg x).lt_of_ne' fun h0 => ?_
  rw [h0, mul_zero] at h1
  exact one_ne_zero h1

theorem covol_eq_of_aedisjoint {X : Type} [Mul X] [MeasurableSpace X] (S : Set X) (μ : Measure X) (A D : Set X)
    (hS : S.Countable) (hm : ∀ γ ∈ S, Measurable fun x => γ * x) (hμ : ∀ γ ∈ S, μ.map (fun x => γ * x) = μ)
    (hinv : ∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x)
    (hD : MeasurableSet D) (hDA : D ⊆ A) (hcov : ∀ x ∈ A, ∃ γ ∈ S, γ * x ∈ D)
    (hdis : ∀ γ ∈ S, ∀ δ ∈ S, γ ≠ δ → μ {x | γ * x ∈ D ∧ δ * x ∈ D} = 0) : covol S μ A = μ D := by
  apply le_antisymm
  · unfold covol
    exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le hcov le_rfl))
  unfold covol
  refine le_iInf fun C => le_iInf fun hC => le_iInf fun hCc => ?_
  have : Countable S := hS.to_subtype
  choose inv hinvS hl hr using hinv
  have h1 : D ⊆ ⋃ δ : S, (fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hCc x (hDA hx)
    refine Set.mem_iUnion.2 ⟨⟨inv γ hγ, hinvS γ hγ⟩, ?_, ?_⟩
    · have e : inv (inv γ hγ) (hinvS γ hγ) * x = γ * x := by
        conv_lhs => rw [← hl γ hγ x, hl]
      show inv (inv γ hγ) (hinvS γ hγ) * x ∈ C
      rw [e]; exact hγx
    · show inv γ hγ * (inv (inv γ hγ) (hinvS γ hγ) * x) ∈ D
      rw [hr]; exact hx
  have hmeas : ∀ δ : S, MeasurableSet (C ∩ (fun x => δ.1 * x) ⁻¹' D) := fun δ => hC.inter (hm δ δ.2 hD)
  calc μ D ≤ ∑' δ : S, μ ((fun x => inv δ δ.2 * x) ⁻¹' (C ∩ (fun x => δ.1 * x) ⁻¹' D)) :=
        (measure_mono h1).trans (measure_iUnion_le _)
    _ = ∑' δ : S, μ (C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine tsum_congr fun δ => ?_
        rw [← Measure.map_apply (hm _ (hinvS δ δ.2)) (hmeas δ), hμ _ (hinvS δ δ.2)]
    _ = μ (⋃ δ : S, C ∩ (fun x => δ.1 * x) ⁻¹' D) := by
        refine (measure_iUnion₀ (fun γ δ hne => ?_) fun δ => (hmeas δ).nullMeasurableSet).symm
        refine measure_mono_null (fun x hx => ?_) (hdis γ γ.2 δ δ.2 fun h => hne (Subtype.ext h))
        exact ⟨hx.1.2, hx.2.2⟩
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun δ => Set.inter_subset_left)

end GlobalTheory.OrbitTerm
