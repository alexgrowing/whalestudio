import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamondStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGammaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSesquilinearHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjointStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk.Semisimple

theorem dia_sub_smul (k : ℤ) (σ : SL(2, ℤ)) (f g : ℍ → ℂ) (c : ℂ) :
    GlobalTheory.Hk.dia k σ (f - c • g) = GlobalTheory.Hk.dia k σ f - c • GlobalTheory.Hk.dia k σ g := by
  unfold GlobalTheory.Hk.dia
  rw [sub_eq_add_neg, SlashAction.add_slash, ← _root_.neg_smul, ModularForm.SL_smul_slash, _root_.neg_smul,
    ← sub_eq_add_neg]

theorem heckeT_zero (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) : GlobalTheory.Hk.heckeT k q σ 0 = 0 := by
  funext τ
  simp [GlobalTheory.Hk.heckeT, GlobalTheory.Hk.uOp, GlobalTheory.Hk.vOp]

section
variable {N l : ℕ} {k : ℤ}

local notation "P" => GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k

theorem pet_zero_right (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑f 0 = 0 := by
  have h := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 0 1).1
  simp only [CuspForm.coe_zero, smul_zero, add_zero, one_mul] at h
  linear_combination -h

theorem pet_smul_right (hN : 0 < N) (hl : 0 < l) (f h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ) :
    P ⇑f (c • ⇑h) = c * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f 0 h c).1
  simp only [CuspForm.coe_zero, zero_add] at e
  rw [e, pet_zero_right hN hl f, zero_add]

theorem pet_lin_right (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P ⇑f (a • ⇑g - b • ⇑h) = a * P ⇑f ⇑g - b * P ⇑f ⇑h := by
  have e := (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f (a • g) h (-b)).1
  rw [CuspForm.coe_smul, _root_.neg_smul, ← sub_eq_add_neg] at e
  rw [e, pet_smul_right hN hl]
  ring

theorem pet_conj (hN : 0 < N) (hl : 0 < l) (f g : CuspForm (GlobalTheory.Hk.lev N l) k) :
    P ⇑g ⇑f = (starRingEnd ℂ) (P ⇑f ⇑g) :=
  (GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian N l k hN hl f g 0 0).2

theorem pet_lin_left (hN : 0 < N) (hl : 0 < l) (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (a b : ℂ) :
    P (a • ⇑g - b • ⇑h) ⇑f = (starRingEnd ℂ) a * P ⇑g ⇑f - (starRingEnd ℂ) b * P ⇑h ⇑f := by
  have e : a • ⇑g - b • ⇑h = ⇑(a • g - b • h) := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  rw [e, pet_conj hN hl, CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul,
    pet_lin_right hN hl, map_sub, map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl]

theorem eq_zero_of_pet_self (hN : 0 < N) (hl : 0 < l) (f : CuspForm (GlobalTheory.Hk.lev N l) k)
    (h : P ⇑f ⇑f = 0) : f = 0 := by
  by_contra hf
  have := (GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 N l k hN hl f hf).1
  rw [h] at this
  simp at this

theorem eigen_dia (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (u v : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hv : ⇑v = GlobalTheory.Hk.dia k σ ⇑u) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    c • ⇑u = (starRingEnd ℂ) c • ⇑v := by
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : (starRingEnd ℂ) c * P ⇑u ⇑v = c * P ⇑u ⇑u := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ u u
    rw [hu, ← hv, pet_smul_right hN hl, ← CuspForm.coe_smul, pet_conj hN hl, CuspForm.coe_smul,
      pet_smul_right hN hl, map_mul, ← pet_conj hN hl] at h
    exact h
  have h3 : c * P ⇑v ⇑u = (starRingEnd ℂ) c * P ⇑u ⇑u := by
    have h := congrArg (starRingEnd ℂ) h2
    rw [map_mul, map_mul, ← pet_conj hN hl, ← pet_conj hN hl, Complex.conj_conj] at h
    exact h
  have e : ⇑(c • u - (starRingEnd ℂ) c • v) = c • ⇑u - (starRingEnd ℂ) c • ⇑v := by
    rw [CuspForm.coe_sub, CuspForm.coe_smul, CuspForm.coe_smul]
  have hw : c • u - (starRingEnd ℂ) c • v = 0 := by
    apply eq_zero_of_pet_self hN hl
    have := pet_lin_left hN hl (c • u - (starRingEnd ℂ) c • v) u v c ((starRingEnd ℂ) c)
    rw [← e] at this
    rw [this, e, pet_lin_right hN hl, pet_lin_right hN hl, h1, h2, h3]
    ring
  rw [hw, CuspForm.coe_zero] at e
  exact (sub_eq_zero.mp e.symm)

theorem ker_sq (hN : 0 < N) (hl : 0 < l) {q : ℕ} {σ : SL(2, ℤ)} (hq : q.Prime)
    (hqN : ¬ q ∣ N * l) (hσ : GlobalTheory.Hk.IsDia N l q σ) (c : ℂ) (g u : CuspForm (GlobalTheory.Hk.lev N l) k)
    (hg : ⇑u = GlobalTheory.Hk.heckeT k q σ ⇑g - c • ⇑g) (hu : GlobalTheory.Hk.heckeT k q σ ⇑u = c • ⇑u) :
    u = 0 := by
  obtain ⟨v, hv⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ u
  obtain ⟨dg, hdg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q σ hN hσ g
  obtain ⟨sdg, hsdg⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ dg
  have hw := eigen_dia hN hl hq hqN hσ c u v hv hu
  have hcomm : GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k σ ⇑g)
      = GlobalTheory.Hk.dia k σ (GlobalTheory.Hk.heckeT k q σ ⇑g) :=
    GlobalTheory.T.hecke_operator_commutes_diamond N l q k q σ σ hN hq hqN hσ hσ (CuspForm.toModularFormₗ g)
  have hv' : ⇑v = (1 : ℂ) • ⇑sdg - c • ⇑dg := by
    rw [hv, hg, dia_sub_smul, ← hcomm, hsdg, hdg, one_smul]
  have h1 : P ⇑v ⇑v = P ⇑u ⇑u := by
    rw [hv]; exact GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary N l k q σ hN hl hσ u u
  have h2 : P ⇑sdg ⇑v = (starRingEnd ℂ) c * P ⇑dg ⇑v := by
    have h := GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint N l q k σ σ hN hl hq hqN hσ hσ dg u
    rw [← hsdg, ← hv, hu, hw, pet_smul_right hN hl] at h
    exact h
  apply eq_zero_of_pet_self hN hl
  have h3 := pet_lin_left hN hl v sdg dg 1 c
  rw [← hv', h1, h2] at h3
  rw [h3]
  simp

end

theorem heckeT_semisimple : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  intro N l q k σ c n hN hl hq hqN hσ
  induction n with
  | zero =>
    intro f hf
    have hf' : ⇑f = 0 := hf
    rw [hf', heckeT_zero, smul_zero]
  | succ n ih =>
    intro f hf
    obtain ⟨sf, hsf⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k σ hN hq hqN hσ f
    have e : ⇑(sf - c • f) = GlobalTheory.Hk.heckeT k q σ ⇑f - c • ⇑f := by
      rw [CuspForm.coe_sub, CuspForm.coe_smul, hsf]
    rw [Function.iterate_succ_apply] at hf
    have hu := ih (sf - c • f) (by rw [e]; exact hf)
    have h0 := ker_sq hN hl hq hqN hσ c f (sf - c • f) e hu
    rw [h0, CuspForm.coe_zero] at e
    exact sub_eq_zero.mp e.symm

end GlobalTheory.Hk.Semisimple
