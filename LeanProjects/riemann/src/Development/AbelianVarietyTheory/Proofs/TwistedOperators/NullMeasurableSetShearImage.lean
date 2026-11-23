import Mathlib

open MeasureTheory

namespace GlobalTheory.UnfoldNormal

def pairGroup {H : Type} [Group H] (Γ N : Subgroup H) (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) :
    Subgroup (H × H) where
  carrier := {p | p.1 ∈ Γ ∧ p.2 ∈ Γ ∧ p.1 * p.2⁻¹ ∈ N}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hb, hab⟩ ⟨hc, hd, hcd⟩
    refine ⟨Γ.mul_mem ha hc, Γ.mul_mem hb hd, ?_⟩
    have e : a * c * (b * d)⁻¹ = (a * b⁻¹) * (b * (c * d⁻¹) * b⁻¹) := by group
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [e]
    exact N.mul_mem hab (hN b hb _ hcd)
  one_mem' := ⟨Γ.one_mem, Γ.one_mem, by simp [N.one_mem]⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    refine ⟨Γ.inv_mem ha, Γ.inv_mem hb, ?_⟩
    have e : a⁻¹ * b⁻¹⁻¹ = a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    simp only [Prod.fst_inv, Prod.snd_inv]
    rw [e]
    exact hN _ (Γ.inv_mem ha) _ (N.inv_mem hab)

def shear {H : Type} [Group H] (N : Subgroup H) (p : N × H) : H × H := ((p.1 : H) * p.2, p.2)

end GlobalTheory.UnfoldNormal

namespace GlobalTheory.UnfoldNormal

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

def shearEquiv : H × H ≃ᵐ H × H where
  toFun p := (p.1 * p.2, p.2)
  invFun p := (p.1 * p.2⁻¹, p.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := (measurable_fst.mul measurable_snd).prodMk measurable_snd
  measurable_invFun := (measurable_fst.mul measurable_snd.inv).prodMk measurable_snd

theorem shear_eq (N : Subgroup H) : shear N = shearEquiv ∘ Prod.map Subtype.val id := rfl

theorem measurableEmbedding_shear {N : Subgroup H} (hN : IsClosed (N : Set H)) :
    MeasurableEmbedding (shear N) := by
  rw [shear_eq]
  exact shearEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hN.measurableSet).prodMap MeasurableEmbedding.id)

theorem nullMeasurableSet_shear_image {N : Subgroup H} (hN : IsClosed (N : Set H)) (κ : Measure N)
    (ν : Measure H) {A : Set N} {B : Set H} (hA : NullMeasurableSet A κ) (hB : NullMeasurableSet B ν) :
    NullMeasurableSet (shear N '' (A ×ˢ B)) ((κ.prod ν).map (shear N)) := by
  have he := measurableEmbedding_shear hN
  have hAB : NullMeasurableSet (A ×ˢ B) (κ.prod ν) := hA.prod hB
  refine (he.measurableSet_image.2 (measurableSet_toMeasurable (κ.prod ν) (A ×ˢ B))).nullMeasurableSet.congr ?_
  refine (he.ae_map_iff (p := fun y => (shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) y =
    (shear N '' (A ×ˢ B)) y)).2 ?_
  filter_upwards [hAB.toMeasurable_ae_eq] with x hx
  have e1 : (shear N '' toMeasurable (κ.prod ν) (A ×ˢ B)) (shear N x) = toMeasurable (κ.prod ν) (A ×ˢ B) x :=
    propext he.injective.mem_set_image
  have e2 : (shear N '' (A ×ˢ B)) (shear N x) = (A ×ˢ B) x := propext he.injective.mem_set_image
  rw [e1, e2]
  exact hx

end GlobalTheory.UnfoldNormal
