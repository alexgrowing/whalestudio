import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.AdelEqProof

theorem map_thetaR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  change f (σ ((g⁻¹ : GL (Fin n) A).val j i)) = τ (((GeneralLinearGroup.map f g)⁻¹ : GL (Fin n) B).val j i)
  rw [← map_inv]
  exact h _

theorem map_PhiU {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n A) = PhiU n B := by
  apply Units.ext
  ext i j
  change f ((PhiU n A).val i j) = (PhiU n B).val i j
  rw [phiU_val, phiU_val]
  simp [GlobalTheory.Tw.Phi, apply_ite f]

theorem map_thetaGL {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaGL n σ g) = thetaGL n τ (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_PhiU, map_thetaR f σ τ h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

theorem pFin_conjAd (x : Ad E) :
    pFin E (conjAd E x) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E x) := rfl

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) :
    cV v (conjAd E x) = starRingEnd ℂ (cV v x) := by
  have h : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) := by
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) ((infEq E).symm x.1))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change pInf E (conjAd E x) v = _
  rw [h]
  rfl

theorem cV_algebraMap (v : InfinitePlace E) (y : E) : cV v (algebraMap E (Ad E) y) = v.embedding y :=
  pInf_algebraMap y v

theorem map_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = GeneralLinearGroup.map v.embedding d := by
  apply Units.ext
  ext i j
  exact cV_algebraMap v _

theorem map_pFin_ratGL (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  apply Units.ext
  ext i j
  rfl

theorem map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  apply Units.ext
  ext i j
  rfl

theorem map_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) :=
  map_thetaGL _ _ _ pFin_conjAd n g

theorem map_cV_twConj (v : InfinitePlace E) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (twConj (thetaA E n) x (ratGL E n d)) =
      twConj (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map (cV v) x) (GeneralLinearGroup.map v.embedding d) := by
  simp only [twConj, map_mul, map_inv, map_cV_ratGL]
  rw [map_thetaR (cV v) (conjAd E) (starRingEnd ℂ) (cV_conjAd v) n x]

theorem map_pFin_twConj (hT : TranslAd) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := hT E n u hu x
  have h2 : twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹ =
      x⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) x := by
    rw [h, map_mul, map_inv]
    simp only [twConj]
    group
  rw [h2, map_mul, map_mul, map_inv, map_pFin_ratGL, map_pFin_thetaGL]

theorem cpt_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x)) := by
  rw [cpt, map_cW, map_pFin_twConj hT u hu]

theorem cpt'_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt' w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w) (thF E n
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x))) := by
  rw [cpt', map_cW, map_pFin_thetaGL, map_pFin_twConj hT u hu]

theorem adelEqOf : AdelEqOf := by
  intro hT E _ _ _ a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [adel, orbFn, finFn]
  refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun v _ => ?_)
    (finprod_congr fun w => finprod_congr fun _ => ?_)
  · rw [map_cV_twConj, map_cV_twConj]
    rfl
  · rw [cpt_twConj hT w u₁ h₁, cpt_twConj hT w u₂ h₂, cpt'_twConj hT w u₁ h₁, cpt'_twConj hT w u₂ h₂]
    rfl

end GlobalTheory.CompanionTheory.AdelEqProof

end
