import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.TwFree

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

theorem pow_val_mul (ζ : Prim q A) (a b : (ZMod q)ˣ) :
    (ζ.1 ^ (a : ZMod q).val) ^ (b : ZMod q).val = ζ.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ)]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ ((1 : (ZMod q)ˣ) : ZMod q).val = ζ.1 := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ), pow_one]

def orbRel : Setoid (Prim q A) where
  r ζ ξ := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val
  iseqv :=
    { refl := fun ζ => ⟨1, (pow_val_one q A ζ).symm⟩
      symm := fun {ζ ξ} ⟨a, h⟩ => ⟨a⁻¹, by rw [h, pow_val_mul, mul_inv_cancel, pow_val_one]⟩
      trans := fun {ζ ξ η} ⟨a, h⟩ ⟨b, h'⟩ => ⟨a * b, by rw [h', h, pow_val_mul]⟩ }

abbrev Orb := Quotient (orbRel q A)

abbrev orb (ζ : Prim q A) : Orb q A := Quotient.mk (orbRel q A) ζ

def rep (O : Orb q A) : Prim q A := Quotient.out O

theorem exists_coef (ζ : Prim q A) : ∃ a : (ZMod q)ˣ, ζ.1 = (rep q A (orb q A ζ)).1 ^ (a : ZMod q).val :=
  Quotient.exact (Quotient.out_eq (orb q A ζ))

def coef (ζ : Prim q A) : (ZMod q)ˣ := (exists_coef q A ζ).choose

theorem coef_spec (ζ : Prim q A) : ζ.1 = (rep q A (orb q A ζ)).1 ^ (coef q A ζ : ZMod q).val :=
  (exists_coef q A ζ).choose_spec

variable [Nontrivial A]

theorem units_eq_of_pow (r : Prim q A) (a b : (ZMod q)ˣ)
    (h : r.1 ^ (a : ZMod q).val = r.1 ^ (b : ZMod q).val) : a = b := by
  by_contra hne
  have hm : ¬ (a : ZMod q).val ≡ (b : ZMod q).val [MOD q] := by
    intro hm
    apply hne
    apply Units.ext
    apply ZMod.val_injective
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hm
    exact hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 r _ _ hm
  rw [h, sub_self] at hu
  exact not_isUnit_zero hu

theorem orb_coef_of_pow (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    orb q A ξ = orb q A ζ ∧ coef q A ξ = coef q A ζ * a := by
  have ho : orb q A ξ = orb q A ζ := (Quotient.sound (s := orbRel q A) (a := ζ) (b := ξ) ⟨a, h⟩).symm
  refine ⟨ho, units_eq_of_pow q A (rep q A (orb q A ξ)) _ _ ?_⟩
  rw [← coef_spec, h, coef_spec q A ζ, pow_val_mul, ho]

theorem orb_coef_rep (O : Orb q A) : orb q A (rep q A O) = O ∧ coef q A (rep q A O) = 1 := by
  have ho : orb q A (rep q A O) = O := Quotient.out_eq O
  refine ⟨ho, units_eq_of_pow q A (rep q A O) _ _ ?_⟩
  have h := coef_spec q A (rep q A O)
  rw [ho] at h
  rw [← h, pow_val_one]

variable (i : ℤ)

def coordMap : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ (fun ζ => Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem twRel_le_ker : twRel q i A ≤ LinearMap.ker (coordMap q A i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  obtain ⟨ho, hc⟩ := orb_coef_of_pow q A ζ ξ a h
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, coordMap, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, one_mul, ho, hc, sub_eq_zero]
  congr 1
  apply ULift.ext
  simp [mul_zpow, mul_comm]

def coordQ : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  (twRel q i A).liftQ (coordMap q A i) (twRel_le_ker q A i)

def basisMap : (Orb q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Finsupp.linearCombination _ (fun O => Submodule.Quotient.mk (Finsupp.single (rep q A O) 1))

theorem coordQ_mk_single (ζ : Prim q A) :
    coordQ q A i (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)) := by
  simp [coordQ, coordMap, Finsupp.linearCombination_single]

def twEquiv : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ≃ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  LinearEquiv.ofLinear (coordQ q A i) (basisMap q A i)
    (by
      refine Finsupp.lhom_ext' fun O => LinearMap.ext_ring ?_
      obtain ⟨ho, hc⟩ := orb_coef_rep q A O
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, basisMap,
        Finsupp.linearCombination_single, one_smul, coordQ_mk_single, ho, hc, one_zpow, LinearMap.id_coe, id_eq]
      rfl)
    (by
      refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
        coordQ_mk_single, basisMap, Finsupp.linearCombination_single, LinearMap.id_coe, id_eq]
      rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one, eq_comm,
        Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨rep q A (orb q A ζ), ζ, coef q A ζ, coef_spec q A ζ, rfl⟩)

theorem twist_free : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A],
    Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧
    ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  intro q _ i A _ _
  refine ⟨Module.Free.of_equiv (twEquiv q A i).symm, fun ζ => ?_⟩
  refine ⟨ULift.up (((coef q A ζ ^ i)⁻¹ : (ZMod q)ˣ) : ZMod q) •
    (Finsupp.lapply (orb q A ζ) ∘ₗ coordQ q A i), ?_⟩
  rw [LinearMap.smul_apply, LinearMap.comp_apply, coordQ_mk_single, Finsupp.lapply_apply,
    Finsupp.single_eq_same, smul_eq_mul]
  apply ULift.ext
  simp

end GlobalTheory.TwFree
