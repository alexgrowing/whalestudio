import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

def graphFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : HdR A₀ →ₗ[k] HdR A₀) :
    Submodule (DualNumber k) (Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) where
  carrier := {d | ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
    d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c)}
  add_mem' := by
    rintro d d' ⟨x, hx, y, hy, e⟩ ⟨x', hx', y', hy', e'⟩
    refine ⟨x + x', add_mem hx hx', y + y', add_mem hy hy', fun c => ?_⟩
    rw [LinearMap.add_apply, e, e']
    ext <;> simp <;> ring
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, fun c => by
    rw [LinearMap.zero_apply]
    ext <;> simp⟩
  smul_mem' := by
    rintro r d ⟨x, hx, y, hy, e⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, r.fst • y + r.snd • x,
      add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, e, smul_eq_mul]
    ext <;> simp <;> ring

variable {A₀ : Over (Sp k)} [GrpObj A₀]

theorem mem_graphFil {f : HdR A₀ →ₗ[k] HdR A₀} {d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀} :
    d ∈ graphFil A₀ f ↔ ∃ x ∈ Fil A₀, ∃ y ∈ Fil A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c + y c) := Iff.rfl

theorem isBC_constMor (hA : IsAbelianScheme A₀) : (constMor A₀).IsBC :=
  GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k A₀ hA (SqExt.dual k).sq (constMor A₀)

theorem exists_crys (hA : IsAbelianScheme A₀) (u v : HdR A₀) :
    ∃ d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  obtain ⟨d₁, h₁⟩ := (isBC_constMor hA).exists u
  obtain ⟨d₂, h₂⟩ := (isBC_constMor hA).exists v
  refine ⟨d₁ + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • d₂, fun c => ?_⟩
  rw [LinearMap.add_apply, LinearMap.smul_apply, h₁ c, h₂ c]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 1000000 in

theorem crys_ext (hA : IsAbelianScheme A₀) {d d' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀}
    (h : ∀ c : primDR A₀, d ((constMor A₀).pull c) = d' ((constMor A₀).pull c)) : d = d' := by
  refine LinearMap.ext fun c' => ?_
  obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c'
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => rw [liftSemi_tmul, map_smul, map_smul, h c]

def coordOf (g : DualNumber k →ₗ[k] k) (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) : HdR A₀ where
  toFun c := g (d ((constMor A₀).pull c))
  map_add' a b := by rw [map_add, map_add, map_add]
  map_smul' r a := by
    rw [map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul]
    rfl

theorem exists_coords (d : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀) :
    ∃ u v : HdR A₀, ∀ c : primDR A₀,
      d ((constMor A₀).pull c) = TrivSqZeroExt.inl (u c) + TrivSqZeroExt.inr (v c) := by
  refine ⟨coordOf (TrivSqZeroExt.fstHom k k k).toLinearMap d, coordOf (TrivSqZeroExt.sndHom k k) d, fun c => ?_⟩
  ext <;> simp [coordOf]

end GlobalTheory.HTRealise
