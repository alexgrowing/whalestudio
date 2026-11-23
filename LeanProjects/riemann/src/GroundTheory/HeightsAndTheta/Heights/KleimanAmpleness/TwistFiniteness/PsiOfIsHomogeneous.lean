import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial AddMonoidAlgebra

noncomputable section

universe u w

namespace TwistFin

variable {Ω : Type w} [Field Ω] {N r : ℕ}

abbrev LA (Ω : Type w) [Field Ω] : Type w := AddMonoidAlgebra Ω (ℤ × ℤ)

set_option linter.unusedVariables false in

def Amb (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) : Type w := LA Ω

variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)

instance : AddCommGroup (Amb x η) := inferInstanceAs (AddCommGroup (LA Ω))

instance : Module (LA Ω) (Amb x η) := inferInstanceAs (Module (LA Ω) (LA Ω))

def toA : Amb x η ≃+ LA Ω := AddEquiv.refl _

variable (S : Type u) [CommRing S] [Algebra S Ω]

abbrev Sy (S : Type u) [CommRing S] (r : ℕ) : Type u := MvPolynomial (Fin (r + 1)) S

def psi : Sy S r →ₐ[S] LA Ω := aeval fun j => single ((0 : ℤ), (1 : ℤ)) (η j)

def phi : Poly (Sy S r) N →+* LA Ω :=
  eval₂Hom (psi η S).toRingHom fun i => single ((1 : ℤ), (0 : ℤ)) (x i)

instance modP : Module (Poly (Sy S r) N) (Amb x η) := Module.compHom _ (phi x η S)

instance modSy : Module (Sy S r) (Amb x η) := Module.compHom _ (psi η S).toRingHom

theorem toA_smulP (p : Poly (Sy S r) N) (a : Amb x η) : toA x η (p • a) = phi x η S p * toA x η a := rfl

theorem toA_smulSy (s : Sy S r) (a : Amb x η) : toA x η (s • a) = psi η S s * toA x η a := rfl

theorem phi_C (s : Sy S r) : phi x η S (C s) = psi η S s := eval₂Hom_C _ _ _

theorem phi_X (i : Fin (N + 1)) : phi x η S (X i) = single ((1 : ℤ), (0 : ℤ)) (x i) :=
  eval₂Hom_X' _ _ _

theorem psi_X (j : Fin (r + 1)) : psi η S (X j) = single ((0 : ℤ), (1 : ℤ)) (η j) :=
  aeval_X _ _

instance : IsScalarTower (Sy S r) (Poly (Sy S r) N) (Amb x η) where
  smul_assoc s p a := by
    apply (toA x η).injective
    rw [toA_smulP, toA_smulSy, toA_smulP, MvPolynomial.smul_eq_C_mul, map_mul, phi_C, mul_assoc]

abbrev tgr (c : ℤ) : Submodule Ω (LA Ω) := gradeBy Ω (AddMonoidHom.fst ℤ ℤ) c

theorem single_mem_tgr (c k : ℤ) (ω : Ω) : (single (c, k) ω : LA Ω) ∈ tgr c :=
  single_mem_gradeBy (R := Ω) (AddMonoidHom.fst ℤ ℤ) (c, k) ω

theorem algebraMap_LA (s : S) : algebraMap S (LA Ω) s = single ((0 : ℤ), (0 : ℤ)) (algebraMap S Ω s) :=
  rfl

theorem psi_mem_tgr (s : Sy S r) : psi η S s ∈ tgr 0 := by
  induction s using MvPolynomial.induction_on with
  | C a =>
    rw [psi, aeval_C, algebraMap_LA]
    exact single_mem_tgr 0 0 _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, psi_X]
    simpa using SetLike.mul_mem_graded hp (single_mem_tgr 0 1 (η j))

theorem phi_mem_tgr {p : Poly (Sy S r) N} {d : ℕ} (hp : p.IsHomogeneous d) :
    phi x η S p ∈ tgr (d : ℤ) := by
  classical
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hdeg : ∑ i ∈ μ.support, μ i = d := by
    have := hp (mem_support_iff.mp hμ)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [phi, coe_eval₂Hom, eval₂_monomial]
  have h1 := psi_mem_tgr η S (MvPolynomial.coeff μ p)
  have h2 : (∏ i ∈ μ.support, (single ((1 : ℤ), (0 : ℤ)) (x i) : LA Ω) ^ μ i) ∈
      tgr (∑ i ∈ μ.support, ((μ i : ℕ) : ℤ)) := by
    refine SetLike.prod_mem_graded _ _ _ fun i _ => ?_
    simpa using SetLike.pow_mem_graded (μ i) (single_mem_tgr 1 0 (x i))
  have h3 := SetLike.mul_mem_graded h1 h2
  rw [zero_add, ← Nat.cast_sum, hdeg] at h3
  exact h3

def kapT : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((1 : ℤ), (0 : ℤ)) 1)

def kapU : Polynomial Ω →ₐ[Ω] LA Ω := Polynomial.aeval (single ((0 : ℤ), (1 : ℤ)) 1)

theorem phi_map_C {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    phi x η S (MvPolynomial.map (C : S →+* Sy S r) f) = single ((e : ℤ), (0 : ℤ)) (aeval x f) := by
  have key : (phi x η S).comp (MvPolynomial.map (C : S →+* Sy S r)) =
      (kapT (Ω := Ω)).toRingHom.comp (cone (S := S) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, map_C, phi_C]
      change psi η S (C a) = kapT ((cone (S := S) x) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapT,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, phi_X]
      change _ = kapT (coneGen x (X i))
      rw [coneGen, aeval_X, kapT, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g f) key
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  change kapT (cone (S := S) x f) = _
  rw [cone_of_isHomogeneous x hf, kapT, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]

theorem psi_of_isHomogeneous {h : Sy S r} {b : ℕ} (hh : h.IsHomogeneous b) :
    psi η S h = single ((0 : ℤ), (b : ℤ)) (aeval η h) := by
  have key : (psi η S).toRingHom = (kapU (Ω := Ω)).toRingHom.comp (coneGen (S := S) η).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change psi η S (C a) = kapU ((coneGen (S := S) η) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapU,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro j
      change psi η S (X j) = kapU (coneGen η (X j))
      rw [psi_X, coneGen, aeval_X, kapU, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g h) key
  change psi η S h = kapU (coneGen (S := S) η h) at this
  rw [this, coneGen_of_isHomogeneous η hh, kapU, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]

end TwistFin

end

end GroundTheory.Heights₂.Heights.Kleiman
