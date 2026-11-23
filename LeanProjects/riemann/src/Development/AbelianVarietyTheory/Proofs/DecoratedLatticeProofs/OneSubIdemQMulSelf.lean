import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

variable {D : D7}

def indQ (D : D7) (Q : Finset (Pl D)) : Af D.host.F := ∑ v ∈ Q, singleV D.host.F v 1

def idemQ (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (indQ D Q)

def idemQc (D : D7) (Q : Finset (Pl D)) : AF D.host.F := pairA D.host.F 0 (1 - indQ D Q)

open Classical in
theorem evalV_indQ (Q : Finset (Pl D)) (w : Pl D) :
    evalV D.host.F w (indQ D Q) = if w ∈ Q then 1 else 0 := by
  classical
  rw [indQ, map_sum]
  have h : ∀ v ∈ Q, evalV D.host.F w (singleV D.host.F v 1) = if w = v then 1 else 0 := by
    intro v _
    by_cases hwv : w = v
    · subst hwv
      rw [if_pos rfl]
      change (singleV D.host.F w 1) w = 1
      exact RestrictedProduct.single_eq_same _ _ _
    · rw [if_neg hwv]
      change (singleV D.host.F v 1) w = 0
      exact RestrictedProduct.single_eq_of_ne (fun u : Pl D => u.adicCompletionIntegers D.host.F)
        (1 : Fv D.host.F v) hwv
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]

theorem parts_pairA (α : Af D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
        evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  · exact (placeIdempotent_infinite_and_finite_components D w _ α rfl).2 w

open Classical in
theorem parts_idemQ (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQ D Q)) = if w ∈ Q then 1 else 0 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQ, (parts_pairA _).2 w, evalV_indQ]
  split_ifs
  · rfl
  · exact TensorProduct.zero_tmul _ _

open Classical in
theorem parts_idemQc (Q : Finset (Pl D)) :
    infPart D (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) (idemQc D Q)) = if w ∈ Q then 0 else 1 := by
  refine ⟨(parts_pairA _).1, fun w => ?_⟩
  rw [idemQc, (parts_pairA _).2 w, map_sub, map_one, evalV_indQ]
  split_ifs
  · rw [sub_self]; exact TensorProduct.zero_tmul _ _
  · rw [sub_zero]; rfl

theorem mem_idAt_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idAt D P ↔ c * a = a := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  constructor
  · rintro ⟨ha0, haw⟩
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [if_pos h, one_mul, sub_self]
      · rw [if_neg h, haw w h, zero_mul, sub_zero]
  · intro ha
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, hc w, if_neg hw, zero_mul]

theorem mem_idOff_iff_mul (P : Pl D → Prop) [DecidablePred P] (c : AE D) (h0 : infPart D c = 0)
    (hc : ∀ w, compAt D w c = if P w then 1 else 0) (a : AE D) : a ∈ idOff D P ↔ c * a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  constructor
  · intro ha
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_mul, h0, zero_mul]
    · intro w
      rw [RingHom.map_mul, hc w]
      by_cases h : P w
      · rw [ha w h, mul_zero]
      · rw [if_neg h, zero_mul]
  · intro ha w hw
    have := congrArg (compAt D w) ha
    rwa [RingHom.map_mul, hc w, if_pos hw, one_mul, RingHom.map_zero] at this

open Classical in
theorem mem_idAt_Q_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∈ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQ D Q) * a = a :=
  mem_idAt_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 a

open Classical in
theorem mem_idAt_Qc_iff (Q : Finset (Pl D)) (a : AE D) :
    a ∈ idAt D (· ∉ Q) ↔ algebraMap (AF D.host.F) (AE D) (idemQc D Q) * a = a :=
  mem_idAt_iff_mul (· ∉ Q) _ (parts_idemQc Q).1
    (fun w => by rw [(parts_idemQc Q).2 w]; by_cases h : w ∈ Q <;> simp [h]) a

theorem idemQ_mul_self (Q : Finset (Pl D)) : idemQ D Q * idemQ D Q = idemQ D Q := by
  have e : (idemQ D Q * idemQ D Q : AF D.host.F) = pairA D.host.F 0 (indQ D Q * indQ D Q) :=
    Prod.ext (mul_zero _) rfl
  rw [e, idemQ]
  congr 1
  apply RestrictedProduct.ext
  intro w
  have h := evalV_indQ (D := D) Q w
  change evalV D.host.F w (indQ D Q * indQ D Q) = evalV D.host.F w (indQ D Q)
  rw [map_mul, h]
  split_ifs <;> simp

theorem one_sub_idemQ_mul_self (Q : Finset (Pl D)) :
    (1 - idemQ D Q) * (1 - idemQ D Q) = 1 - idemQ D Q := by
  have h := idemQ_mul_self (D := D) Q
  linear_combination h

theorem mem_congGrp_iff (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

def cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) : GA D V →* GA D V :=
  GlobalTheory.UnitaryIdemCut.cutUJ (sigR (AF D.host.F) D.sp.cm.sig) (JR (AF D.host.F) V.gram)
    (algebraMap (AF D.host.F) (AE D) ε) (by rw [← map_mul, hε])
    (GlobalTheory.UnitaryIdemCut.sigR_algebraMap (AF D.host.F) D.sp.cm.sig ε)

theorem mt_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g +
      (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := rfl

end GlobalTheory.FinPl.SetCut

end
