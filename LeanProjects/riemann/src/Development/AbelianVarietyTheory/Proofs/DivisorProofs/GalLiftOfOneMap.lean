import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IpMSelfEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueBarCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConjOnFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefAtOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HvMemOfInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CircleEqOneIffOfConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsWeightCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatiblePhaseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFormsRescale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JEvExistsAndJEvBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsIndependentAndSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
open Formalism.IndefR.Arith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Assembly

section Abstract

variable {L : Type} [Field L] {G : Type} [Group G] [Fintype G] {C Y H : Type} [AddCommGroup Y] [Module L Y]
  [AddCommGroup H] [Module ℂ H]

theorem read_sum (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) {n : ℕ} (b : Fin n → L) (f : Fin n → C) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, b k • ι (act g (f k))) =
      ∑ g, σ (e g) • ρ g (∑ k, σ (b k) • J (ι (f k))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smulₛₗ, map_sum, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, h, map_smul, smul_smul, smul_smul, smul_smul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  have := (chi g).inv_mul
  linear_combination (e g * b k) * this

theorem shift_sum (ρ : Representation ℂ G H) (e : G → ℂ) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G) (hz : z ∈ Subgroup.center G)
    (α β κ : ℂ) (hβ : β ≠ 0) (S T : H) (hT : κ • T = ∑ g, e g • ρ g (β • ρ z S)) :
    ∑ g, e g • ρ g (α • ρ z₀ S) = (α * β⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  rw [mul_smul, ← map_smul (ρ (z₀ * z⁻¹)) κ, hT, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ρ (z₀ * z⁻¹) (ρ g (ρ z S)) = ρ g (ρ z₀ S) := by
    have e1 : z₀ * z⁻¹ * (g * z) = g * z₀ := by
      rw [Subgroup.mem_center_iff.1 hz g, Subgroup.mem_center_iff.1 h₀ g]; group
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, e1, map_mul, Module.End.mul_apply]
  simp only [map_smul, h1, smul_smul]
  congr 1
  field_simp

theorem norm_of_pow {a : ℂ} {m : ℕ} (hm : 0 < m) (h : a ^ m = 1) : ‖a‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_chi (σ : L →+* ℂ) (chi : G →* Lˣ) (g : G) : ‖σ (chi g : L)‖ = 1 :=
  norm_of_pow (m := Fintype.card G) Fintype.card_pos (by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])

variable {P : Type} [AddCommGroup P] [Module ℂ P]

theorem conj_abstract (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) (ev : H →ₗ[ℂ] P) (hev : Function.Injective ev)
    (W : P →ₗ[ℂ] P) (hW : ∀ y, W (ev y) = ev (∑ g, σ (e g) • ρ g y)) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G)
    (hz : z ∈ Subgroup.center G) (ze : L) (κ : ℂ) {n : ℕ} (a : Fin n → L) (f : Fin n → C) (θ : P)
    (hθ : κ • θ = ∑ k, σ (a k) • ev (J (ι (act z (f k))))) (T : H) (hT : ev T = W θ) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, (ze * a k) • ι (act g (act z₀ (f k)))) =
      (σ ze * σ (chi z₀ : L) * (σ (chi z : L))⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  have e1 : ∑ k, σ (a k) • ev (J (ι (act z (f k)))) = ev (σ (chi z : L) • ρ z (∑ k, σ (a k) • J (ι (f k)))) := by
    rw [map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [h, map_smul]; rw [smul_comm]
  have h3 : ∑ k, σ (ze * a k) • J (ι (act z₀ (f k))) = (σ ze * σ (chi z₀ : L)) • ρ z₀ (∑ k, σ (a k) • J (ι (f k))) := by
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h, map_smul, smul_smul, smul_smul, map_mul]
    congr 1
    ring
  rw [read_sum σ J ι act chi ρ h e (fun k => ze * a k) (fun k => act z₀ (f k)), h3]
  refine shift_sum ρ _ h₀ hz _ _ κ (norm_ne_zero_iff.1 (by rw [norm_chi]; exact one_ne_zero)) _ _ (hev ?_)
  rw [map_smul, hT, ← map_smul, hθ, e1, hW]

theorem exists_ev (ev : H →ₗ[ℂ] P) {κ : ℂ} (hκ : ‖κ‖ = 1) {n : ℕ} (a : Fin n → ℂ) (t : Fin n → H) (θ : P)
    (hθ : κ • θ = ∑ k, a k • ev (t k)) : ∃ s, ev s = θ := by
  have hκ0 : κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hκ]; exact one_ne_zero)
  refine ⟨κ⁻¹ • ∑ k, a k • t k, ?_⟩
  rw [map_smul, map_sum, ← inv_smul_smul₀ hκ0 θ, hθ]
  simp only [map_smul]

def evL {I : Type} {M : I → Type} [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] (e : H →ₗ[ℂ] MultilinearMap ℂ M P)
    (v : ∀ τ, M τ) : H →ₗ[ℂ] P where
  toFun y := e y v
  map_add' x y := by rw [map_add]; rfl
  map_smul' a x := by rw [map_smul]; rfl

end Abstract

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def crdF (fw : FWTie T R κw v₀) (i : Fin D.R.m) (f : Cu T κw i) : Fin (R.nW i) → D.what₂.LL := (fw.e i f : (R.FW i).WK)

def ratOf (fw : FWTie T R κw v₀) (i : Fin D.R.m) (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL) {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i) : Fin (R.nW i) → D.what₂.LL :=
  ∑ g, ((idemOf A.X).coeff g * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) •
    ∑ k, (ze * a k) • crdF fw i (act g (act z (f k)))

theorem sign_at_base_place_eq_embedding (R : RealDat D A T.Q.c.F) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem exists_reps {i : Fin D.R.m} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hP : OMPins T R κw v₀ O i) :
    ∃ h, RepsAt (O i) (v₀ i (sg0 D A)) h := (hP.2.tuple ()).reps

end Main

section Final

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem smul_inv_of {H : Type} [AddCommGroup H] [Module ℂ H] (L : H →ₗ[ℂ] H) {κ κ' : ℂ} (h : ‖κ'‖ = 1) {a b : H}
    (e : b = κ' • a) : κ • L a = (κ * κ'⁻¹) • L b := by
  have h0 : κ' ≠ 0 := norm_ne_zero_iff.1 (by rw [h]; exact one_ne_zero)
  rw [e, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]

end Final

end GlobalTheory.GalLift.Assembly

end
