import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory

theorem exists_stable_spanning_finset : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  intro l _ Γ _ _ _ _ a ρ L hρ hL
  classical
  obtain ⟨t₀, ht₀⟩ := zl_span_image_finite l Γ a ρ hρ
  let e : Matrix (Fin a) (Fin a) L.1 →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (Om l) :=
    LinearMap.mapMatrix L.1.val.toLinearMap
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let bM := Module.finBasis ℚ_[l] (Matrix (Fin a) (Fin a) L.1)
  let B : Finset (Matrix (Fin a) (Fin a) (Om l)) := insert 1 (Finset.univ.image (fun k => e (bM k)))
  let t₁ : Finset Γ := insert 1 t₀
  let t : Finset (Matrix (Fin a) (Fin a) (Om l)) := (t₁ ×ˢ B).image (fun p => (ρ p.1).val * p.2)
  have hBL : ∀ b ∈ B, ∀ i j, b i j ∈ L.1 := by
    intro b hb i j
    rcases Finset.mem_insert.mp hb with rfl | hb
    · by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
      exact (bM k i j).2
  have hmemt : ∀ h ∈ t₁, ∀ b ∈ B, (ρ h).val * b ∈ t := fun h hh b hb =>
    Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, hb⟩, rfl⟩
  have hBt : ∀ b ∈ B, b ∈ t := fun b hb => by
    have := hmemt 1 (Finset.mem_insert_self _ _) b hb
    simpa using this
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    simp only [Matrix.mul_apply]
    exact L.1.sum_mem fun k _ => L.1.mul_mem (hL h i k) (hBL b hb k j)
  · intro x hx
    have hxe : x = e (fun i j => ⟨x i j, hx i j⟩) := by ext i j; rfl
    have hsp : (fun i j => (⟨x i j, hx i j⟩ : L.1)) ∈ Submodule.span ℚ_[l] (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 : e (fun i j => ⟨x i j, hx i j⟩) ∈ Submodule.span ℚ_[l] (e '' Set.range bM) := by
      rw [Submodule.span_image]; exact Submodule.mem_map_of_mem hsp
    rw [hxe]
    refine Submodule.span_mono ?_ h2
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    exact hBt _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  · refine ⟨fun y => if y = 1 then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Matrix (Fin a) (Fin a) (Om l))]
    · simp
    · intro y _ hy; simp [hy]
    · intro h1; exact absurd (hBt 1 (Finset.mem_insert_self _ _)) h1
  · intro g x hx
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    obtain ⟨f', hf'sup, hf'⟩ := ht₀ (Finsupp.single (g * h) 1)
    have hgh : ((ρ (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
        f'.sum fun k c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((ρ k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
      rw [← hf', Finsupp.sum_single_index (by simp)]
      simp
    refine ⟨fun y => ∑ k ∈ f'.support with (ρ k).val * b = y, f' k, ?_⟩
    have hmaps : ∀ k ∈ f'.support, (ρ k).val * b ∈ t := fun k hk =>
      hmemt k (Finset.mem_insert_of_mem (hf'sup hk)) b hb
    calc (ρ g).val * ((ρ h).val * b) = (ρ (g * h)).val * b := by rw [map_mul, Units.val_mul, Matrix.mul_assoc]
      _ = ∑ k ∈ f'.support, zOm l (f' k) • ((ρ k).val * b) := by
          rw [hgh, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mul]; rfl
      _ = ∑ y ∈ t, ∑ k ∈ f'.support with (ρ k).val * b = y, zOm l (f' k) • ((ρ k).val * b) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ y ∈ t, zOm l (∑ k ∈ f'.support with (ρ k).val * b = y, f' k) • y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [map_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [(Finset.mem_filter.mp hk).2]

end GlobalTheory
