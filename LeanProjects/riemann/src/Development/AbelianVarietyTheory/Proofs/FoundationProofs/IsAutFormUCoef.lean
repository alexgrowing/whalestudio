import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.EquivCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  {X : Type} [AddCommGroup X] [Module ℂ X]

def coefL (R : UA E n →* Module.End ℂ X) (F : UA E n → X) : Module.Dual ℂ X →ₗ[ℂ] (UA E n → ℂ) where
  toFun μ := fun g => μ (R g⁻¹ (F g))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isAutFormU_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Type) [AddCommGroup X]
    [Module ℂ X] [FiniteDimensional ℂ X] (R : UA E n →* Module.End ℂ X) (F : UA E n → X),
    (∀ k ∈ finU E n, R k = 1) → (∀ (u : X) (ℓ : Module.Dual ℂ X), Continuous fun g => ℓ (R g u)) →
    (∀ y ∈ infU E n, ∀ g, F (g * y) = F g) → (∀ γ ∈ ratU E n, ∀ g, F (γ * g) = R γ (F g)) →
    (∀ᶠ y in 𝓝 (1 : UA E n), ∀ g, F (g * y) = F g) →
    ∀ ℓ : Module.Dual ℂ X, IsAutFormU fun g => ℓ (R g⁻¹ (F g)) := by
  intro E _ _ _ n X _ _ _ R F hfin hcont hinf hrat hsm ℓ
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA E n => ℓ (R g⁻¹ (F g0)) := (hcont (F g0) ℓ).comp continuous_inv
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g0⁻¹ * g) (𝓝 g0) (𝓝 1) := by
      have : Continuous fun g : UA E n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left] at e
    change ℓ (R g⁻¹ (F g0)) = ℓ (R g⁻¹ (F g))
    rw [e]
  · intro γ hγ g
    change ℓ (R (γ * g)⁻¹ (F (γ * g))) = ℓ (R g⁻¹ (F g))
    rw [hrat γ hγ g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (R γ⁻¹), ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · let φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F g))
    let H : Subgroup (finU E n) :=
      { carrier := {k | RU E n (k : UA E n) φ = φ}
        mul_mem' := fun {a b} ha hb => by
          change RU E n ((a : UA E n) * b) _ = _
          rw [← GlobalTheory.DefU.RU_RU, hb, ha]
        one_mem' := by
          change RU E n 1 _ = _
          rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change RU E n ((a : UA E n)⁻¹) _ = _
          conv_lhs => rw [← ha]
          change RU E n ((a : UA E n)⁻¹) (RU E n (a : UA E n) _) = _
          rw [GlobalTheory.DefU.RU_RU, inv_mul_cancel, map_one]; rfl }
    have hnb : {k : finU E n | ∀ g, F (g * (k : UA E n)) = F g} ∈ 𝓝 (1 : finU E n) :=
      (continuous_subtype_val.tendsto (1 : finU E n)).eventually hsm
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hnb fun k hk => ?_)
    change RU E n (k : UA E n) φ = φ
    funext g
    change ℓ (R (g * (k : UA E n))⁻¹ (F (g * k))) = ℓ (R g⁻¹ (F g))
    rw [hk g, _root_.mul_inv_rev, map_mul, hfin _ ((finU E n).inv_mem k.2), one_mul]
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefL R F)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    change ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F g))) = ℓ (R (g * (k : UA E n))⁻¹ (F (g * k)))
    rw [hinf _ k.2 g, _root_.mul_inv_rev, map_mul, Module.End.mul_apply]

end GlobalTheory.EquivCoef
