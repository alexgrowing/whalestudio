import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetPositivePartKroneckerBlockUnitaryOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCharAtPlace

theorem det_eq_detPos_mul_detNeg {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) :
    κ.det = detPos p κ * detNeg p κ := by
  unfold detPos detNeg
  exact Matrix.twoBlockTriangular_det κ (fun i => i.val < p) (fun i hi j hj => h.2 i j (by tauto))

theorem onb_mul_inv {k p : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) : B * B⁻¹ = 1 := by
  obtain ⟨ε, hε, h1, -⟩ := h
  have hd : (Bᴴ * G * B).det ≠ 0 := by
    rw [h1, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rcases hε a with ⟨e, -⟩ | ⟨e, -⟩ <;> simp [e]
  rw [Matrix.det_mul] at hd
  exact Matrix.mul_nonsing_inv _ (Ne.isUnit (right_ne_zero_of_mul hd))

theorem comm_of_onb {k p : ℕ} {G s B κ : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p) (hk : IsKMat p κ) :
    s * (B * κ * B⁻¹) = B * κ * B⁻¹ * s := by
  have hB := onb_mul_inv h
  have hB' : B⁻¹ * B = 1 := mul_eq_one_comm.1 hB
  obtain ⟨ε, hε, -, h2⟩ := h
  have hs : s = B * diagonal (fun a => (ε a : ℂ)) * B⁻¹ := by
    rw [← h2, Matrix.mul_assoc, hB, Matrix.mul_one]
  have hc : diagonal (fun a => (ε a : ℂ)) * κ = κ * diagonal (fun a => (ε a : ℂ)) := by
    ext i j
    rw [diagonal_mul, mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · have e : ε i = ε j := by
        rcases hε i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hε j with ⟨b1, b2⟩ | ⟨b1, b2⟩
        · rw [a1, b1]
        · exact absurd (hij.1 a2) (by omega)
        · exact absurd (hij.2 b2) (by omega)
        · rw [a1, b1]
      rw [e, mul_comm]
    · rw [hk.2 i j hij, mul_zero, zero_mul]
  rw [hs]
  calc B * diagonal (fun a => (ε a : ℂ)) * B⁻¹ * (B * κ * B⁻¹)
        = B * (diagonal (fun a => (ε a : ℂ)) * (B⁻¹ * B) * κ) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = B * (κ * (B⁻¹ * B) * diagonal (fun a => (ε a : ℂ))) * B⁻¹ := by
        rw [hB', Matrix.mul_one, Matrix.mul_one, hc]
    _ = B * κ * B⁻¹ * (B * diagonal (fun a => (ε a : ℂ)) * B⁻¹) := by simp only [Matrix.mul_assoc]

theorem alg {A B C E : ℂ} (cS cT : ℤ) (pS qS pT qT : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hE : E ≠ 0) :
    ((A * B) ^ cT)⁻¹ * (C * E) ^ cS * (C ^ pS * E ^ qS * (A ^ pT)⁻¹ * (B ^ qT)⁻¹) =
      A ^ (-cT - (pT : ℤ) - (qT : ℤ) + (qT : ℤ)) * B ^ (-cT - (pT : ℤ) - (qT : ℤ) + (pT : ℤ)) *
        (C ^ (cS + (pS : ℤ)) * E ^ (cS + (qS : ℤ))) := by
  have e1 : -cT - (pT : ℤ) - (qT : ℤ) + (qT : ℤ) = -cT - (pT : ℤ) := by ring
  have e2 : -cT - (pT : ℤ) - (qT : ℤ) + (pT : ℤ) = -cT - (qT : ℤ) := by ring
  rw [e1, e2, mul_zpow, mul_zpow, zpow_add₀ hC, zpow_add₀ hE, zpow_sub₀ hA, zpow_sub₀ hB, _root_.zpow_neg, _root_.zpow_neg]
  simp only [zpow_natCast]
  have := zpow_ne_zero cT hA
  have := zpow_ne_zero cT hB
  have := pow_ne_zero pT hA
  have := pow_ne_zero qT hB
  field_simp

end GlobalTheory.VacCharAtPlace

open GlobalTheory.VacCharAtPlace in

theorem GlobalTheory.VacCharAtPlace.vacuum_char_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ τ : D.what₂.Tau, ∃ mS mT : ℤ, ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → om (g, h) f = (detPos (pS τ) κS ^ (mS + (T.rank - pT τ : ℕ)) * detNeg (pS τ) κS ^ (mS + pT τ) * (detPos (pT τ) κT ^ (mT + pS τ) * detNeg (pT τ) κT ^ (mT + (S.rank - pS τ : ℕ)))) • f := by
  intro D ψ θ S T χS χT om hW hθ τ
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨aS, haS⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χS S.rank τ hθ hW.hecS hW.resS
  obtain ⟨aT, haT⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ χT T.rank τ hθ hW.hecT hW.resT
  obtain ⟨cS, hcS⟩ := GlobalTheory.CompactFockAction.exp_twist_int hθ S hW.resS e3 haS (e2 τ)
  obtain ⟨cT, hcT⟩ := GlobalTheory.CompactFockAction.exp_twist_int hθ T hW.resT e3 haT (e2 τ)
  refine ⟨-cT - T.rank, cS, ?_⟩
  intro sS BS sT BT pS pT hpS hpT hCS hCT hOS hOT f hf hv κS κT hkS hkT g h hg hh
  classical
  have cg : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt S g) = if ρ = τ then BS τ * κS * (BS τ)⁻¹ else 1 := fun ρ => by
    split_ifs with e
    · subst e; exact hg.2.1
    · exact hg.2.2 ρ e
  have ch : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt T h) = if ρ = τ then BT τ * κT * (BT τ)⁻¹ else 1 := fun ρ => by
    split_ifs with e
    · subst e; exact hh.2.1
    · exact hh.2.2 ρ e
  have ginv : ∀ ρ, compAt θ ρ (Formalism.L2.Theta.mt S g⁻¹) = (compAt θ ρ (Formalism.L2.Theta.mt S g))⁻¹ := fun ρ =>
    (Matrix.inv_eq_right_inv (GlobalTheory.WeilVacMove.compAt_mt_mul_inv θ ρ S g)).symm
  have commS : ∀ ρ, sS ρ * compAt θ ρ (Formalism.L2.Theta.mt S g) = compAt θ ρ (Formalism.L2.Theta.mt S g) * sS ρ := fun ρ => by
    rw [cg]; split_ifs with e
    · subst e; exact comm_of_onb (hOS ρ) hkS
    · rw [Matrix.mul_one, Matrix.one_mul]
  have commT : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * sT ρ := fun ρ => by
    rw [ch]; split_ifs with e
    · subst e; exact comm_of_onb (hOT ρ) hkT
    · rw [Matrix.mul_one, Matrix.one_mul]
  have dS : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt S g)).det = if ρ = τ then κS.det else 1 := fun ρ => by
    rw [cg]; split_ifs
    · exact Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (onb_mul_inv (hOS τ)))) κS
    · exact Matrix.det_one
  have dT : ∀ ρ, (compAt θ ρ (Formalism.L2.Theta.mt T h)).det = if ρ = τ then κT.det else 1 := fun ρ => by
    rw [ch]; split_ifs
    · exact Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (onb_mul_inv (hOT τ)))) κT
    · exact Matrix.det_one
  have nS : ‖κS.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hkS.1)
  have nT : ‖κT.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hkT.1)
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq κS.det two_pos
  obtain ⟨v, hv'⟩ := IsAlgClosed.exists_pow_nat_eq κT.det two_pos
  have hw1 : ‖w‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, hw, nS])
  have hv1 : ‖v‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 (by rw [← norm_pow, hv', nT])
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.CompactFockAction.exists_root_at hθ S hg.1 τ w hw1 (by rw [dS, if_pos rfl, hw])
    (fun ρ e => by rw [dS, if_neg e])
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.CompactFockAction.exists_root_at hθ T hh.1 τ v hv1 (by rw [dT, if_pos rfl, hv'])
    (fun ρ e => by rw [dT, if_neg e])
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW sS sT hCS hCT g hg.1 h hh.1 commS commT x y hx hy
    f hf hv]
  congr 1
  have vx : (((χT * (η ^ T.rank)⁻¹) x : Circle) : ℂ) = κS.det ^ cT := by
    rw [hxv _ (aT - T.rank / 2) (2 * cT) (GlobalTheory.VacuumCharacter.hasInfExp_twist haT (e2 τ) T.rank)
      (by push_cast; rw [hcT]), _root_.zpow_mul, ← hw]
    norm_cast
  have vy : (((χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) = κT.det ^ cS := by
    rw [hyv _ (aS - S.rank / 2) (2 * cS) (GlobalTheory.VacuumCharacter.hasInfExp_twist haS (e2 τ) S.rank)
      (by push_cast; rw [hcS]), _root_.zpow_mul, ← hv']
    norm_cast
  have hP : ∏ ρ, GlobalTheory.WeilParts.detPlus (sS ρ) (sT ρ) (compAt θ ρ (Formalism.L2.Theta.mt S g⁻¹))
      (compAt θ ρ (Formalism.L2.Theta.mt T h)) =
      GlobalTheory.WeilParts.detPlus (sS τ) (sT τ) (BS τ * κS * (BS τ)⁻¹)⁻¹ (BT τ * κT * (BT τ)⁻¹) := by
    rw [Finset.prod_eq_single τ (fun ρ _ e => by
        rw [ginv, cg, ch, if_neg e, if_neg e, inv_one]; exact GlobalTheory.CompactFockAction.detPlus_one_one _ _)
      (by simp), ginv, cg, ch, if_pos rfl, if_pos rfl]
  have d0S := det_eq_detPos_mul_detNeg hkS
  have d0T := det_eq_detPos_mul_detNeg hkT
  have nz : ∀ {a b c : ℂ}, ‖c‖ = 1 → c = a * b → a ≠ 0 ∧ b ≠ 0 := fun {a b c} hc e => by
    have : c ≠ 0 := fun h0 => by simp [h0] at hc
    rw [e] at this
    exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩
  obtain ⟨hA, hB⟩ := nz nS d0S
  obtain ⟨hC, hE⟩ := nz nT d0T
  rw [Circle.coe_mul, Circle.coe_inv, vx, vy, hP,
    GlobalTheory.T.detPositivePartKronecker_blockUnitary_orthonormal (gramAt D S τ) (sS τ) (BS τ) κS (gramAt D T τ) (sT τ) (BT τ) κT (pS τ) (pT τ) (hpS τ) (hpT τ)
      (hOS τ) (hOT τ) hkS hkT, d0S, d0T,
    show (-cT - (T.rank : ℤ)) = -cT - (pT τ : ℤ) - ((T.rank - pT τ : ℕ) : ℤ) by push_cast [hpT τ]; ring]
  exact alg cS cT (pS τ) (S.rank - pS τ) (pT τ) (T.rank - pT τ) hA hB hC hE
