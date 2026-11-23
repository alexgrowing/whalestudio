import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentDefiniteUnitaryFinitePartEqLocalPo
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinCentComm

theorem commute_aeval {R : Type} [CommRing R] {r : ℕ} {m A : Matrix (Fin r) (Fin r) R}
    (h : Commute m A) (p : R[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_krylov {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (v c : Fin r → R) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_cyclic {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (v : Fin r → R)
    (hKu : IsUnit (GlobalTheory.ClassParam.krylov A v).det) (n : Matrix (Fin r) (Fin r) R) (hn : Commute n A) :
    ∃ q : R[X], n = aeval A q := by
  set K := GlobalTheory.ClassParam.krylov A v with hK
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval (Commute.refl A) _).symm
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) R, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hn, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_map_separable {E R : Type} [Field E] [CommRing R] (f : E →+* R) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hA : A.charpoly.Separable) (X Y : Matrix (Fin r) (Fin r) R)
    (hX : X * A.map f = A.map f * X) (hY : Y * A.map f = A.map f * Y) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hA
  have hKu : IsUnit (GlobalTheory.ClassParam.krylov (A.map f) (f ∘ v)).det := by
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map f
  obtain ⟨q, rfl⟩ := eq_aeval_of_cyclic (A.map f) (f ∘ v) hKu Y hY
  exact (commute_aeval (m := X) hX q).eq

end GlobalTheory.BCT.FinCentComm

namespace GlobalTheory.BCT.FinCentComm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_fst_eq_one (a : finU E n) : ((a : UA E n) : GA E n).val.map (FinPtLoc.fstA E) = 1 := by
  have ha : cInf (a : UA E n) = 1 := a.2
  ext i j
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => g.val i j) ha
  change (infEq E).symm (FinPtLoc.fstA E (((a : UA E n) : GA E n).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j at h
  rw [Matrix.map_apply]
  apply (infEq E).symm.injective
  rw [h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_snd_finPt (γ : UE E n) :
    (((finPt γ : finU E n) : UA E n) : GA E n).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
  rw [FinPtLoc.finPt_eq]
  ext i j
  rw [Matrix.map_apply, FinPtLoc.snd_entry]
  rfl

end GlobalTheory.BCT.FinCentComm

open GlobalTheory.BCT.FinCentComm in

theorem GlobalTheory.BCT.finCent_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n),
    γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU E n)) (finPt γ),
      ∀ b ∈ twCent (MonoidHom.id (finU E n)) (finPt γ), a * b = b * a := by
  intro E _ _ _ n γ hγ a ha b hb
  have key : ∀ c ∈ twCent (MonoidHom.id (finU E n)) (finPt γ),
      (((c : UA E n) : GA E n).val.map (pFin E)) * γ.1.val.map (algebraMap E (Af E)) =
        γ.1.val.map (algebraMap E (Af E)) * ((c : UA E n) : GA E n).val.map (pFin E) := by
    intro c hc
    have h : c * finPt γ = finPt γ * c := hc
    have h' := congrArg (fun z : finU E n => ((z : UA E n) : GA E n).val.map (pFin E)) h
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul] at h'
    rwa [map_snd_finPt] at h'
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  apply FinPtLoc.ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_eq_one a, map_fst_eq_one b]
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact commute_of_commute_map_separable (algebraMap E (Af E)) γ.1.val hγ _ _ (key a ha) (key b hb)
