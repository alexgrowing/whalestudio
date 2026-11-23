import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePartAtOwnWeightNeBot

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DefU.CoefSp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def coef (W : GlobalTheory.DefU.Wt E n) : Module.Dual ℂ (Module.End ℂ W.Sp) →ₗ[ℂ] (infU E n → ℂ) :=
  LinearMap.pi fun x => LinearMap.applyₗ (W.rep x)

def C (W : GlobalTheory.DefU.Wt E n) : Submodule ℂ (infU E n → ℂ) := LinearMap.range (coef W)

instance (W : GlobalTheory.DefU.Wt E n) : FiniteDimensional ℂ (C W) := LinearMap.finiteDimensional_range _

theorem C_right (W : GlobalTheory.DefU.Wt E n) {c : infU E n → ℂ} (hc : c ∈ C W) (y : infU E n) :
    (fun x => c (x * y)) ∈ C W := by
  obtain ⟨B, rfl⟩ := hc
  refine ⟨B ∘ₗ LinearMap.mulRight ℂ (W.rep y), funext fun x => ?_⟩
  change B (W.rep x * W.rep y) = B (W.rep (x * y))
  exact congrArg B (map_mul W.rep x y).symm

def Y (W : GlobalTheory.DefU.Wt E n) : Submodule ℂ (UA E n → ℂ) :=
  ⨅ g : UA E n, (C W).comap (LinearMap.funLeft ℂ ℂ fun x : infU E n => g * (x : UA E n))

theorem mem_Y {W : GlobalTheory.DefU.Wt E n} {ψ : UA E n → ℂ} :
    ψ ∈ Y W ↔ ∀ g : UA E n, (fun x : infU E n => ψ (g * x)) ∈ C W := by
  simp only [Y, Submodule.mem_iInf, Submodule.mem_comap]
  rfl

theorem le_Y (π : GlobalTheory.DefU.AutSub E n) (W : GlobalTheory.DefU.Wt E n) (hW : π.finPart W ≠ ⊥) : π.V ≤ Y W := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (Subtype.ext (LinearMap.ext h))
  have hvπ : f.1 v ∈ π.V := GlobalTheory.DefU.AutSub.mem_finPart.1 hf v
  have hvY : f.1 v ∈ Y W := mem_Y.2 fun g =>
    ⟨(LinearMap.proj g ∘ₗ f.1) ∘ₗ LinearMap.applyₗ v, funext fun x => by
      change f.1 (W.rep x v) g = f.1 v (g * x)
      rw [f.2.2 x v]
      rfl⟩
  have hst : ∀ x, ∀ ψ ∈ π.V ⊓ Y W, RU E n x ψ ∈ π.V ⊓ Y W := by
    intro x ψ hψ
    refine ⟨π.isAut.stable x ψ hψ.1, mem_Y.2 fun g => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.DefU.admitted.exists_fin_mul_inf x
    have e : (fun z : infU E n => RU E n (a * b) ψ (g * z)) =
        fun z => ψ ((g * a) * ((z * ⟨b, hb⟩ : infU E n) : UA E n)) := by
      funext z
      rw [GlobalTheory.DefU.RU_apply, Subgroup.coe_mul, Subgroup.coe_mk, ← mul_assoc, mul_assoc g,
        ← GlobalTheory.DefU.fin_mul_inf ha z.2, ← mul_assoc, mul_assoc (g * a)]
    rw [e]
    exact C_right W (mem_Y.1 hψ.2 (g * a)) ⟨b, hb⟩
  rcases π.isAut.irred (π.V ⊓ Y W) inf_le_left hst with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (⟨hvπ, hvY⟩ : f.1 v ∈ π.V ⊓ Y W))) hv
  · rw [← h]
    exact inf_le_right

theorem wt_eq (U : GlobalTheory.DefU.AutSub E n) (lam : GlobalTheory.DefU.Wt E n)
    (hw : ∀ v : InfinitePlace E, HasWeightAt U.V v.embedding (lam v)) : (GlobalTheory.DefU.AU.mk U).wt = lam := by
  funext v
  have h := GlobalTheory.DefU.AU.HasWt.wt ((GlobalTheory.DefU.AU.hasWt_mk U v.embedding (lam v)).2 (hw v))
  rw [GlobalTheory.DefU.Wt.at_embedding] at h
  exact GlobalTheory.DefU.hasWeightAt_unique U v.embedding ((GlobalTheory.DefU.AU.hasWt_mk U _ _).1 h) (hw v)

theorem coef_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n),
    ∃ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C ∧ ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ φ ∈ π, ∀ g : UA E n,
        (fun x : infU E n => φ (g * (x : UA E n))) ∈ C := by
  intro E _ _ _ n lam
  refine ⟨C lam, inferInstance, fun π hπ hw φ hφ g => ?_⟩
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have hne := GlobalTheory.DefU.AutSub.finPart_wt_ne_bot E n U
  rw [wt_eq U lam hw] at hne
  exact mem_Y.1 (le_Y U lam hne hφ) g

end GlobalTheory.DefU.CoefSp

end
