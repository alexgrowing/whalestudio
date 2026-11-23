import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedGLMassFormula
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCentNorm

open GlobalTheory.ClassParam (krylov)
open GlobalTheory.MassNorm

section Core

variable {R : Type} [CommRing R] {m : ℕ}

def PhiU (m : ℕ) (R : Type) [CommRing R] : GL (Fin m) R :=
  ⟨GlobalTheory.Tw.Phi m R, (GlobalTheory.Tw.Phi m R)ᵀ, Phi_mul_transpose m R, PhiT_mul_Phi⟩

def DJ (J : GL (Fin m) R) : GL (Fin m) R := J⁻¹ * (PhiU m R)⁻¹

theorem psi_DJ (c : R →+* R) (J : GL (Fin m) R) (x : Matrix (Fin m) (Fin m) R) :
    psi c (DJ J) x = (J⁻¹).val * cT c x * J.val := by
  have h1 : ((PhiU m R)⁻¹).val = (GlobalTheory.Tw.Phi m R)ᵀ := rfl
  have h2 : (DJ J).val = (J⁻¹).val * (GlobalTheory.Tw.Phi m R)ᵀ := by
    rw [DJ, Units.val_mul, h1]
  have h3 : ((DJ J)⁻¹).val = GlobalTheory.Tw.Phi m R * J.val := by
    rw [DJ, _root_.mul_inv_rev, inv_inv, inv_inv, Units.val_mul]; rfl
  rw [psi, h2, h3]
  have hP := PhiT_mul_Phi (m := m) (R := R)
  calc _ = (J⁻¹).val * ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * (c.mapMatrix x)ᵀ *
        ((GlobalTheory.Tw.Phi m R)ᵀ * GlobalTheory.Tw.Phi m R) * J.val := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.mul_one, Matrix.mul_one]; rfl

theorem mem_UJ_iff (c : R →+* R) (J g : GL (Fin m) R) :
    g ∈ UJ c J.val ↔ psi c (DJ J) g.val = (g⁻¹).val := by
  rw [psi_DJ]
  have hJ : J.val * (J⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ' : (J⁻¹).val * J.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg : g.val * (g⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hg' : (g⁻¹).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  change cT c g.val * J.val * g.val = J.val ↔ _
  constructor
  · intro h
    calc (J⁻¹).val * cT c g.val * J.val
        = (J⁻¹).val * (cT c g.val * J.val * g.val) * (g⁻¹).val := by
          simp only [Matrix.mul_assoc]; rw [hg, Matrix.mul_one]
      _ = _ := by rw [h, hJ', Matrix.one_mul]
  · intro h
    calc cT c g.val * J.val * g.val
        = J.val * ((J⁻¹).val * cT c g.val * J.val) * g.val := by
          simp only [← Matrix.mul_assoc]; rw [hJ, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_assoc, hg', Matrix.mul_one]

theorem psi_norm (c : R →+* R) (hc : ∀ x, c (c x) = x) (D : GL (Fin m) R) :
    psi c D (D * thetaGL m c D).val = ((D * thetaGL m c D)⁻¹).val := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  rw [psi_units]
  congr 1
  simp only [_root_.mul_inv_rev, map_mul, map_inv, hθ]
  group

theorem mem_twCent_iff (c : R →+* R) (D g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔ psi c D g.val = (g⁻¹).val := by
  rw [psi_units]
  constructor
  · intro h
    have h' : g⁻¹ * D = D * thetaGL m c g⁻¹ := (twCent (thetaGL m c) D).inv_mem h
    congr 1
    rw [← h']; group
  · intro h
    have h' : D * thetaGL m c g⁻¹ * D⁻¹ = g⁻¹ := Units.ext h
    have : g⁻¹ ∈ twCent (thetaGL m c) D := by
      change g⁻¹ * D = D * thetaGL m c g⁻¹
      calc g⁻¹ * D = (D * thetaGL m c g⁻¹ * D⁻¹) * D := by rw [h']
        _ = _ := by group
    simpa using (twCent (thetaGL m c) D).inv_mem this

theorem commute_of_mem_twCent (c : R →+* R) (hc : ∀ x, c (c x) = x) (D g : GL (Fin m) R)
    (hg : g ∈ twCent (thetaGL m c) D) : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have hθ : ∀ g, thetaGL m c (thetaGL m c g) = g := GlobalTheory.LocTwist.thetaGL_thetaGL m c hc
  have h1 : g * D = D * thetaGL m c g := hg
  have h2 : thetaGL m c g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg (thetaGL m c) h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * thetaGL m c D)
      = (D * thetaGL m c D) * ((thetaGL m c D)⁻¹ * (D⁻¹ * g * D) * thetaGL m c D) := by group
    _ = _ := by rw [← h3]

theorem mem_twCent_iff_mem_UJ (c : R →+* R) (hc : ∀ x, c (c x) = x) (D J : GL (Fin m) R)
    (hN : D * thetaGL m c D ∈ UJ c J.val) (v : Fin m → R)
    (hv : IsUnit (krylov (D * thetaGL m c D).val v).det) (g : GL (Fin m) R) :
    g ∈ twCent (thetaGL m c) D ↔
      g ∈ UJ c J.val ∧ g * (D * thetaGL m c D) = (D * thetaGL m c D) * g := by
  have key : g * (D * thetaGL m c D) = (D * thetaGL m c D) * g →
      psi c D g.val = psi c (DJ J) g.val := by
    intro hcomm
    obtain ⟨p, hp⟩ := aeval_of_commute_cyclic v hv (N := g.val) (by
      change g.val * (D * thetaGL m c D).val = (D * thetaGL m c D).val * g.val
      rw [← Units.val_mul, ← Units.val_mul, hcomm])
    rw [hp, psi_aeval, psi_aeval, psi_norm c hc, (mem_UJ_iff c J _).1 hN]
  constructor
  · intro hg
    have hcomm := commute_of_mem_twCent c hc D g hg
    refine ⟨?_, hcomm⟩
    rw [mem_UJ_iff, ← key hcomm]
    exact (mem_twCent_iff c D g).1 hg
  · rintro ⟨hg, hcomm⟩
    rw [mem_twCent_iff, key hcomm]
    exact (mem_UJ_iff c J g).1 hg

end Core

section Global

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem cT_map_algebraMap {m : ℕ} (M : Matrix (Fin m) (Fin m) E) :
    cT (conjFin (IsCMField.complexConj E).toRingEquiv) (M.map (algebraMap E (Af E))) =
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (Af E)) := by
  ext i j
  simp [cT, conjFin_algebraMap]

theorem mem_twCent_ratF_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E) (H : Matrix (Fin n) (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable → IsUnit H.det →
  δ * thE E n δ ∈ UJ (IsCMField.complexConj E).toRingEquiv.toRingHom H →
  ∀ g : GL (Fin n) (Af E), g ∈ twCent (thF E n) (ratF E n δ) ↔
    g ∈ UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) ∧
      g * ratF E n (δ * thE E n δ) = ratF E n (δ * thE E n δ) * g := by
  intro E _ _ _ n δ H hs hH hU g
  have hc : ∀ y, conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv y) = y :=
    fun y => GlobalTheory.ThetaPull.cFin_cFin y
  have hNorm : ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ) =
      ratF E n (δ * thE E n δ) := by
    change ratF E n δ * thF E n (ratF E n δ) = _
    rw [GlobalTheory.MassNorm.thF_ratF, map_mul]
  have hdet : IsUnit (H.map (algebraMap E (Af E))).det := by
    have h1 := hH.map (algebraMap E (Af E))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  let J : GL (Fin n) (Af E) := Matrix.nonsingInvUnit _ hdet
  have hJ : J.val = H.map (algebraMap E (Af E)) := rfl
  have hU' : ratF E n (δ * thE E n δ) ∈
      UJ (conjFin (IsCMField.complexConj E).toRingEquiv) (H.map (algebraMap E (Af E))) := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (δ * thE E n δ).val * H * (δ * thE E n δ).val = H := hU
    change cT _ (ratF E n (δ * thE E n δ)).val * _ * (ratF E n (δ * thE E n δ)).val = _
    have hv : (ratF E n (δ * thE E n δ)).val = (δ * thE E n δ).val.map (algebraMap E (Af E)) := rfl
    rw [hv, cT_map_algebraMap]
    conv_rhs => rw [← h0]
    simp only [Matrix.map_mul]
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (krylov (ratF E n δ * thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [hNorm]
    exact h1
  have := mem_twCent_iff_mem_UJ _ hc (ratF E n δ) J (by rw [hNorm, hJ]; exact hU') _ hv' g
  rw [hNorm, hJ] at this
  exact this

end Global

end GlobalTheory.CompanionTheory.TwCentNorm
