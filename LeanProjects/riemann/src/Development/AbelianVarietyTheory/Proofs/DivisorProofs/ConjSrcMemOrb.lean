import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem prjG_val (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (prjG E n T g).val = idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) := rfl

theorem conjSrc_mem_orb (u v : Pl E) :
    conjSrc (IsCMField.complexConj E).toRingEquiv v ∈ orb E u ↔ v ∈ orb E u := by
  simp only [orb, cPl, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right; rw [← h, GlobalTheory.ThetaPull.conjSrc_conjSrc]
    · left; exact conjSrc_injective _ h
  · rintro (rfl | rfl)
    · right; rfl
    · left; exact GlobalTheory.ThetaPull.conjSrc_conjSrc _

theorem cFin_idem (u : Pl E) : GlobalTheory.ThetaPull.cFin E (idem E (orb E u)) = idem E (orb E u) :=
  FiniteAdeleRing.ext _ fun v => by
    show conjLoc _ v (pLoc E _ (idem E _)) = pLoc E v (idem E _)
    rw [pLoc_idem, pLoc_idem]
    by_cases h : v ∈ orb E u
    · rw [if_pos ((conjSrc_mem_orb u v).2 h), if_pos h, map_one]
    · rw [if_neg (mt (conjSrc_mem_orb u v).1 h), if_neg h, map_zero]

theorem thF_val (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    (thF E n g).val = (PhiU n _).val * (((g⁻¹).val.map (GlobalTheory.ThetaPull.cFin E))ᵀ) * ((PhiU n _)⁻¹).val := rfl

theorem thF_prjG (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    thF E n (prjG E n (orb E u) g) = prjG E n (orb E u) (thF E n g) := by
  apply Units.ext
  have he := cFin_idem (E := E) u
  rw [thF_val, prjG_val, thF_val, ← map_inv, prjG_val]
  have h1 : (idem E (orb E u) • (g⁻¹).val + (1 - idem E (orb E u)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))).map
      (GlobalTheory.ThetaPull.cFin E) = idem E (orb E u) • (g⁻¹).val.map (GlobalTheory.ThetaPull.cFin E) + (1 - idem E (orb E u)) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, he]
  have h2 : (PhiU n (FiniteAdeleRing (𝓞 E) E)).val * ((PhiU n (FiniteAdeleRing (𝓞 E) E))⁻¹).val = 1 := Units.mul_inv _
  rw [h1, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, h2]

theorem prjG_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    prjG E n T (prjG E n T g) = prjG E n T g := by
  apply Units.ext
  have h1 : idem E T * (1 - idem E T) = 0 := by rw [mul_sub, mul_one, idem_mul_self, sub_self]
  rw [prjG_val, prjG_val, smul_add, smul_smul, smul_smul, idem_mul_self, h1, zero_smul, add_zero]

theorem thU_val (u : Pl E) (a : Gam E n u) : (thU E n u a).1 = thF E n a.1 := by
  obtain ⟨g, hg⟩ := a.2
  show prjG E n (orb E u) (thF E n a.1) = thF E n a.1
  rw [← hg, thF_prjG, prjG_prjG]

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
