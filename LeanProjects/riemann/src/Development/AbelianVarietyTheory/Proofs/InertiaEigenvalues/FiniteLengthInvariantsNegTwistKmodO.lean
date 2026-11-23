import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZBridge

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
