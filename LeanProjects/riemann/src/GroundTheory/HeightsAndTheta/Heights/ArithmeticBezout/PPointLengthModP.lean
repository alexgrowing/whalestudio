import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsPointLengthModP
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsMultiProjPrime)

def PointLengthModP.varEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ => rfl

theorem PointLengthModP.proof : PointLengthModP.Statement := by
  intro n p W F _ hp _ hpW hsurj hpF i
  classical
  let e : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
    (renameEquiv ℤ (PointLengthModP.varEquiv n)).toRingEquiv
  set W' := IndefiniteRowSideFullHecke.ArithBezout.finIdeal W with hW'
  have hWe : W'.map e = W := by
    change (W.comap e).map e = W
    exact Ideal.map_comap_of_surjective _ e.surjective W
  set I : Ideal (MvPolynomial (Fin n) ℤ) := W' ⊔ Ideal.span {X i - 1} with hI
  have hJ : W ⊔ Ideal.span {(X ⟨(), i⟩ : MRing (PBlk n)) - 1} = I.map e := by
    rw [hI, Ideal.map_sup, hWe, Ideal.map_span, Set.image_singleton]
    congr 3
    simp [e, PointLengthModP.varEquiv]
  let E1 := Ideal.quotientEquiv I _ e hJ
  let φ : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F := MvPolynomial.map (Int.castRingHom F)
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ hsurj
  have : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 (by exact_mod_cast hpF)
  have hker : RingHom.ker φ ≤ I := by
    rw [MvPolynomial.ker_map]
    apply Ideal.map_le_of_le_comap
    intro z hz
    rw [RingHom.mem_ker, eq_intCast, CharP.intCast_eq_zero_iff F p] at hz
    obtain ⟨c, rfl⟩ := hz
    simp only [Ideal.mem_comap, map_mul]
    apply Ideal.mul_mem_right
    apply Ideal.mem_sup_left
    show rename _ (C (p : ℤ)) ∈ W
    simpa [rename_C] using hpW
  set J' := W'.map φ ⊔ Ideal.span {(X i : MvPolynomial (Fin n) F) - 1} with hJ'def
  have hJ' : J' = I.map φ := by
    rw [hJ'def, hI, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    simp [φ]
  let f : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) F ⧸ J' := (Ideal.Quotient.mk J').comp φ
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hφ
  have hkerf : RingHom.ker f = I := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hJ', Ideal.comap_map_of_surjective _ hφ]
    exact sup_eq_left.2 hker
  let E2 : (MvPolynomial (Fin n) ℤ ⧸ I) ≃+* (MvPolynomial (Fin n) F ⧸ J') :=
    (Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf)
  have hZ : Function.Surjective (algebraMap ℤ F) := by rw [algebraMap_int_eq]; exact hsurj
  rw [(E1.symm.trans E2).toIntAlgEquiv.toLinearEquiv.length_eq,
    Module.length_eq_of_surjective hZ, Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

end ObjectsChow

end GroundTheory.Heights₂.Heights
