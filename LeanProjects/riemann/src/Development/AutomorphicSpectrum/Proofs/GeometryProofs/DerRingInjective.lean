import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.Tan

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieEx

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R)

def augPart (f : B) : RingHom.ker ε :=
  ⟨f - algebraMap R B (ε f), by simp [RingHom.mem_ker]⟩

theorem augPart_coe (f : B) : ((augPart ε f : RingHom.ker ε) : B) = f - algebraMap R B (ε f) := rfl

theorem augPart_of_mem (f : RingHom.ker ε) : augPart ε f.1 = f := by
  apply Subtype.ext
  rw [augPart_coe, RingHom.mem_ker.mp f.2, map_zero, sub_zero]

theorem augPart_add (f g : B) : augPart ε (f + g) = augPart ε f + augPart ε g := by
  apply Subtype.ext
  simp only [Submodule.coe_add, augPart_coe, map_add]
  abel

theorem augPart_smul (r : R) (f : B) : (RingHom.ker ε).toCotangent (augPart ε (r • f)) =
    r • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have h : augPart ε (r • f) = algebraMap R B r • augPart ε f := by
    apply Subtype.ext
    have hr : algebraMap R R r = r := rfl
    simp only [Submodule.coe_smul, augPart_coe, smul_eq_mul, Algebra.smul_def, map_mul,
      AlgHom.commutes, hr]
    ring
  rw [h, map_smul, algebraMap_smul]

theorem augPart_mul (f g : B) : (RingHom.ker ε).toCotangent (augPart ε (f * g)) =
    (ε f) • (RingHom.ker ε).toCotangent (augPart ε g) + (ε g) • (RingHom.ker ε).toCotangent (augPart ε f) := by
  have hab : ((augPart ε f : B) * (augPart ε g : B)) ∈ RingHom.ker ε :=
    Ideal.mul_mem_left _ _ (augPart ε g).2
  have hdec : augPart ε (f * g) =
      ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ + algebraMap R B (ε f) • augPart ε g +
        algebraMap R B (ε g) • augPart ε f := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, augPart_coe, smul_eq_mul, map_mul]
    ring
  have h0 : (RingHom.ker ε).toCotangent ⟨(augPart ε f : B) * (augPart ε g : B), hab⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul (augPart ε f).2 (augPart ε g).2
  rw [hdec, map_add, map_add, h0, zero_add, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

variable {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

def derRing (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) : B →ₐ[R] TrivSqZeroExt R V :=
  AlgHom.ofLinearMap
    { toFun := fun f => TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f)))
      map_add' := fun f g => by
        rw [augPart_add, map_add, map_add, map_add]
        ext <;> simp <;> abel
      map_smul' := fun r f => by
        rw [augPart_smul, map_smul]
        ext <;> simp }
    (by
      have : augPart ε (1 : B) = 0 := by
        apply Subtype.ext
        simp [augPart_coe]
      simp [this])
    (fun f g => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [augPart_mul, map_add, map_smul, map_smul]
      ext <;> simp [add_comm])

theorem derRing_apply (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : B) : derRing ε ψ f =
    TrivSqZeroExt.inl (ε f) + TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent (augPart ε f))) := rfl

theorem derRing_of_mem (ψ : (RingHom.ker ε).Cotangent →ₗ[R] V) (f : RingHom.ker ε) :
    derRing ε ψ f.1 = TrivSqZeroExt.inr (ψ ((RingHom.ker ε).toCotangent f)) := by
  rw [derRing_apply, augPart_of_mem, RingHom.mem_ker.mp f.2]
  simp

theorem derRing_injective {ψ ψ' : (RingHom.ker ε).Cotangent →ₗ[R] V} (h : derRing ε ψ = derRing ε ψ') : ψ = ψ' := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective (RingHom.ker ε) x
  have hy := congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h y.1)
  simpa [derRing_of_mem] using hy

end Alg

section Op
variable (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

abbrev opMod : Module Rᵐᵒᵖ V := Module.compHom V ((RingHom.id R).fromOpposite fun _ _ => mul_comm _ _)

theorem opCentral : @IsCentralScalar R V _ (opMod R V).toSMul := by
  exact @IsCentralScalar.mk R V _ (opMod R V).toSMul (fun _ _ => rfl)
end Op

section Red
variable {R : Type} [CommRing R] (I : Ideal R)

def kap : TrivSqZeroExt R (R ⧸ I) →ₐ[R] DualNumber (R ⧸ I) where
  toFun a := TrivSqZeroExt.inl (Ideal.Quotient.mk I a.fst) + TrivSqZeroExt.inr a.snd
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [TrivSqZeroExt.snd_mul, Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  commutes' r := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_inr (q : R ⧸ I) : kap I (TrivSqZeroExt.inr q) = TrivSqZeroExt.inr q := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap]

theorem kap_algebraMap (r : R) : kap I (algebraMap R _ r) = algebraMap (R ⧸ I) (DualNumber (R ⧸ I)) (Ideal.Quotient.mk I r) := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, TrivSqZeroExt.algebraMap_eq_inl']

theorem kap_map (a : DualNumber R) : kap I (TrivSqZeroExt.map (Ideal.Quotient.mkₐ R I).toLinearMap a) =
    dualMap (Ideal.Quotient.mk I) a := by
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [kap, dualMap]
end Red

section Rel

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]
  {V : Type} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev ev1 (Γ : QFGroup R T) : Γ.btOrder ⊤ →ₐ[R] R := evalAt (Γ.btOrder ⊤) 1

def TanRel (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} {x : Spec (CommRingCat.of R) ⟶ S} (i : Γ.G.left ⟶ G.left)
    (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))) (ψ : omega (Γ.btOrder ⊤) →ₗ[R] V) (v : ob x V ⟶ G) : Prop :=
  ∃ y : Spec (CommRingCat.of (TrivSqZeroExt R V)) ⟶ Γ.G.left,
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R V))) ∧
    y ≫ j = Spec.map (CommRingCat.ofHom (derRing (ev1 Γ) ψ).toRingHom) ∧
    y ≫ i = v.left

end Rel

end GlobalTheory.CompanionTheory.Ar.BT.Tan
