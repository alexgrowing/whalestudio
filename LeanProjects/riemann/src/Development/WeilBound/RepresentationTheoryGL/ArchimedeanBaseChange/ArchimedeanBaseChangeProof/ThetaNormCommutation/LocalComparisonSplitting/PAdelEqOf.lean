import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT

namespace PositivityTheory.Rg.BcB.G8

open PositivityTheory.Rg.Tf.Loc (twConj)

theorem adeleqof_map_Phi {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    (GlobalTheory.Tw.Phi m R).map f = GlobalTheory.Tw.Phi m S := by
  ext i j
  simp only [GlobalTheory.Tw.Phi, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem adeleqof_map_PhiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (m : ℕ) :
    GeneralLinearGroup.map f (PhiU m R) = PhiU m S := by
  apply Units.ext
  show (PhiU m R).val.map f = (PhiU m S).val
  rw [phiU_val, phiU_val]
  exact adeleqof_map_Phi f m

theorem adeleqof_map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (σ : R →+* R) (τ : S →+* S)
    (hf : ∀ y, f (σ y) = τ (f y)) (m : ℕ) (g : GL (Fin m) R) :
    GeneralLinearGroup.map f (thetaR σ m g) = thetaR τ m (GeneralLinearGroup.map f g) := by
  apply Units.ext
  show (thetaR σ m g).val.map f = (thetaR τ m (GeneralLinearGroup.map f g)).val
  rw [thetaR_val, thetaR_val, ← map_inv]
  ext i j
  exact hf _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem adeleqof_pFin_conj (y : Ad E) :
    pFin E (conjAd E y) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E y) := rfl

theorem adeleqof_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) := by
  rw [thF, thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, adeleqof_map_PhiU,
    adeleqof_map_thetaR (pFin E) (conjAd E) _ adeleqof_pFin_conj]

theorem adeleqof_pInf_conj (y : Ad E) : pInf E (conjAd E y) = starRingEnd (Cinf E) (pInf E y) := by
  show (infEq E).symm ((infEq E) (starRingEnd (Cinf E) ((infEq E).symm (RingHom.fst _ _ y)))) =
    starRingEnd (Cinf E) ((infEq E).symm (RingHom.fst _ _ y))
  exact (infEq E).symm_apply_apply _

theorem adeleqof_cV_conj (v : InfinitePlace E) (y : Ad E) : cV v (conjAd E y) = starRingEnd ℂ (cV v y) := by
  show pInf E (conjAd E y) v = starRingEnd ℂ (pInf E y v)
  rw [adeleqof_pInf_conj]
  rfl

theorem adeleqof_cV_thetaA (v : InfinitePlace E) (g : GA E n) :
    GeneralLinearGroup.map (cV v) (thetaA E n g) = thetaR (starRingEnd ℂ) n (GeneralLinearGroup.map (cV v) g) :=
  adeleqof_map_thetaR (cV v) (conjAd E) (starRingEnd ℂ) (adeleqof_cV_conj v) n g

theorem adeleqof_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = GeneralLinearGroup.map v.embedding d := by
  ext i j
  exact pInf_algebraMap (d i j) v

omit [IsCMField E] in
theorem adeleqof_pFin_ratGL (d : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  ext i j
  rfl

omit [IsCMField E] in
theorem adeleqof_map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem adeleqof_twist (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) :
    twConj (thetaA E n) g (ratGL E n d) * (ratGL E n u)⁻¹ = g⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) g := by
  rw [hT E n u hu g, twConj, map_mul, map_inv]
  group

theorem adeleqof_cpt (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) (w : Pl E) :
    cpt w u (twConj (thetaA E n) g (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) g)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) g)) := by
  rw [cpt, adeleqof_map_cW, adeleqof_twist hT hu]
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL]

theorem adeleqof_cpt' (hT : TranslAd) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (g : GA E n) (w : Pl E) :
    cpt' w u (twConj (thetaA E n) g (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w) (thF E n
      ((GeneralLinearGroup.map (pFin E) g)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) g))) := by
  rw [cpt', adeleqof_map_cW, adeleqof_twist hT hu, adeleqof_pFin_thetaGL]
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL]

theorem adelEqOf_holds : AdelEqOf := by
  intro hT E _ _ _ a b S u₁ u₂ hu₁ hu₂ ψ φ₁ φ₂ d₁ d₂ x
  simp only [adel, orbFn, finFn, atW, comps, adeleqof_cpt hT hu₁, adeleqof_cpt hT hu₂, adeleqof_cpt' hT hu₁,
    adeleqof_cpt' hT hu₂]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp only [twConj, map_mul, map_inv, adeleqof_cV_thetaA, adeleqof_cV_ratGL]

end PositivityTheory.Rg.BcB.G8

end
