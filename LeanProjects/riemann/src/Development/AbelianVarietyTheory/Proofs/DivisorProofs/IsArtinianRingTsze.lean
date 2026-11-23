import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTGlue

variable {k : Type} [Field k] {d : ℕ}

theorem finite_tsze (k : Type) [Field k] (d : ℕ) : Module.Finite k (TrivSqZeroExt k (Fin d → k)) :=
  Module.Finite.of_surjective
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))).coprod (TrivSqZeroExt.inrHom k (Fin d → k)))
    (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)

theorem isArtinianRing_tsze (k : Type) [Field k] (d : ℕ) : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) :=
  haveI := finite_tsze k d; IsArtinianRing.of_finite k _

theorem exists_coords (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀) (l : primDR A₀ →ₗ[k] TrivSqZeroExt k V) :
    ∃ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀,
      ∀ c, e ((GlobalTheory.FODef.constMorV k V A₀).pull c) = l c := by
  have hm := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k V A₀ hA (GlobalTheory.FODef.sqZero k V) (GlobalTheory.FODef.constMorV k V A₀)
  let eqv := LinearEquiv.ofBijective _ hm
  refine ⟨(LinearMap.liftBaseChange (TrivSqZeroExt k V) l) ∘ₗ eqv.symm.toLinearMap, fun c => ?_⟩
  have : (GlobalTheory.FODef.constMorV k V A₀).pull c = eqv (1 ⊗ₜ c) :=
    (one_smul (TrivSqZeroExt k V) ((GlobalTheory.FODef.constMorV k V A₀).pull c)).symm
  rw [this, LinearMap.comp_apply, LinearEquiv.coe_coe, eqv.symm_apply_apply,
    LinearMap.liftBaseChange_tmul, one_smul]

def glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) :
    Submodule (TrivSqZeroExt k (Fin d → k))
      (Crys (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) A₀) where
  carrier := {e | ∃ x ∈ Fil A₀, ∃ z : Fin d → HdR A₀, (∀ j, z j ∈ Fil A₀) ∧
      ∀ c : primDR A₀, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
        TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (fun j => (f j x + z j) c)}
  add_mem' := by
    rintro e e' ⟨x, hx, z, hz, he⟩ ⟨x', hx', z', hz', he'⟩
    refine ⟨x + x', add_mem hx hx', z + z', fun j => add_mem (hz j) (hz' j), fun c => ?_⟩
    rw [LinearMap.add_apply, he c, he' c]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, map_add,
        LinearMap.add_apply, zero_add, Pi.zero_apply, add_zero]
      ring
  zero_mem' := ⟨0, zero_mem _, 0, fun _ => zero_mem _, fun c => by rw [LinearMap.zero_apply]; ext <;> simp⟩
  smul_mem' := by
    rintro r e ⟨x, hx, z, hz, he⟩
    refine ⟨r.fst • x, Submodule.smul_mem _ _ hx, fun j => r.fst • z j + r.snd j • x,
      fun j => add_mem (Submodule.smul_mem _ _ (hz j)) (Submodule.smul_mem _ _ hx), fun c => ?_⟩
    rw [LinearMap.smul_apply, he c, smul_eq_mul]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Pi.add_apply, Pi.smul_apply,
        map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_zero, zero_add,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.zero_apply]
      ring

theorem exists_mem_glueFil (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀)) {x : HdR A₀} (hx : x ∈ Fil A₀) :
    ∃ e ∈ glueFil A₀ f, ∀ c, e ((GlobalTheory.FODef.constMorV k (Fin d → k) A₀).pull c) =
      TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr ((LinearMap.pi fun j => f j x) c) := by
  obtain ⟨e, he⟩ := exists_coords (Fin d → k) A₀ hA
    ((Algebra.linearMap k (TrivSqZeroExt k (Fin d → k))) ∘ₗ x + (TrivSqZeroExt.inrHom k (Fin d → k)) ∘ₗ
      LinearMap.pi fun j => f j x)
  refine ⟨e, ⟨x, hx, 0, fun _ => zero_mem _, fun c => ?_⟩, fun c => ?_⟩
  · rw [he c]; ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [he c]; simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.HTGlue
