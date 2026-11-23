import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.DarbouxDenom

theorem incM_add {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {m n : Type}
    (A B : Matrix m n E) : incM F (A + B) = incM F A + incM F B := by
  ext i j; simp [incM]

theorem incM_zero {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {m n : Type} :
    incM F (0 : Matrix m n E) = 0 := by
  ext i j; simp [incM]

theorem exists_uniform_denom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (x : Fin d → E), ∃ D : ℕ, 1 ≤ D ∧ ∀ β : Fin n → 𝓞 E, ∃ y z : Fin n × Fin d → 𝓞 F,
      M.co.e (incM F (Matrix.vecMulVec (fun i => (β i : E)) x)) =
        (fun k => algebraMap F (AF F) ((y k : F) / D), fun k => algebraMap F (AF F) ((z k : F) / D)) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM x

  let f : (Fin n → 𝓞 E) →+ (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun β => M.co.e (incM F (Matrix.vecMulVec (fun i => (β i : E)) x))
      map_zero' := by
        have h0 : (fun i => ((0 : Fin n → 𝓞 E) i : E)) = 0 := by funext i; simp
        simp only [h0, Matrix.zero_vecMulVec, incM_zero, map_zero]
      map_add' := by
        intro β γ
        have : (fun i => ((β + γ) i : E)) = (fun i => (β i : E)) + (fun i => (γ i : E)) := by
          funext i; simp
        simp only [this, Matrix.add_vecMulVec, incM_add, map_add] }
  have hf : ∀ β, f β = M.co.e (incM F (Matrix.vecMulVec (fun i => (β i : E)) x)) := fun _ => rfl
  obtain ⟨g, hg⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (Fin n → 𝓞 E)).FG)
  choose Y Z hYZ using fun β : Fin n → 𝓞 E => hM.rat (Matrix.vecMulVec (fun i => (β i : E)) x)
  let s : Finset F := g.biUnion (fun β => Finset.univ.image (Y β) ∪ Finset.univ.image (Z β))
  obtain ⟨a, ha, hint⟩ := exists_integral_multiples ℤ ℚ s
  set D := a.natAbs with hD
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha)
  have hDF : (D : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hD1)
  have key : ∀ c ∈ s, IsIntegral ℤ ((D : F) * c) := by
    intro c hc
    have h := hint c hc
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq a with h' | h'
    · rw [h'] at h; simpa [hD] using h
    · rw [h'] at h
      have := h.neg
      simpa [hD] using this
  refine ⟨D, hD1, ?_⟩
  let S : AddSubgroup (Fin n → 𝓞 E) :=
    { carrier := {β | ∃ y z : Fin n × Fin d → 𝓞 F, f β =
        (fun k => algebraMap F (AF F) ((y k : F) / D), fun k => algebraMap F (AF F) ((z k : F) / D))}
      zero_mem' := ⟨0, 0, by ext k <;> simp⟩
      add_mem' := by
        rintro β γ ⟨y, z, h1⟩ ⟨y', z', h2⟩
        refine ⟨y + y', z + z', ?_⟩
        rw [map_add, h1, h2]
        ext k <;> simp [add_div]
      neg_mem' := by
        rintro β ⟨y, z, h1⟩
        refine ⟨-y, -z, ?_⟩
        rw [map_neg, h1]
        ext k <;> simp [neg_div] }
  have hgS : ∀ β ∈ g, β ∈ S := by
    intro β hβ
    have hy : ∀ k, IsIntegral ℤ ((D : F) * Y β k) := fun k =>
      key _ (Finset.mem_biUnion.mpr ⟨β, hβ, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩)
    have hz : ∀ k, IsIntegral ℤ ((D : F) * Z β k) := fun k =>
      key _ (Finset.mem_biUnion.mpr ⟨β, hβ, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩)
    refine ⟨fun k => ⟨(D : F) * Y β k, hy k⟩, fun k => ⟨(D : F) * Z β k, hz k⟩, ?_⟩
    rw [hf, hYZ β]
    ext k
    · show algebraMap F (AF F) (Y β k) = algebraMap F (AF F) (((D : F) * Y β k) / D)
      rw [mul_div_cancel_left₀ _ hDF]
    · show algebraMap F (AF F) (Z β k) = algebraMap F (AF F) (((D : F) * Z β k) / D)
      rw [mul_div_cancel_left₀ _ hDF]
  intro β
  have hmem : β ∈ (Submodule.span ℤ (g : Set (Fin n → 𝓞 E))).toAddSubgroup := by
    rw [hg]; trivial
  rw [Submodule.span_int_eq_addSubgroupClosure] at hmem
  have hle : AddSubgroup.closure (g : Set (Fin n → 𝓞 E)) ≤ S := (AddSubgroup.closure_le S).mpr hgS
  exact hle hmem

end GlobalTheory.DarbouxDenom
