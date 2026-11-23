import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFourInverseMul
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordGood
open GlobalTheory.HL.Model GlobalTheory.HL.Inhab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem adjugate_int (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : IsIntM L A) :
    IsIntM L A.adjugate := by
  let B : Matrix (Fin n) (Fin n) L.O := fun i j => ⟨A i j, h i j⟩
  have hB : A = L.O.subtype.mapMatrix B := by ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  intro i j
  exact (B.adjugate i j).2

theorem isSD_coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : Good S) :
    IsSD L S.Hm (coordLat S) := by
  obtain ⟨y, hy, hyd⟩ := h.Hm_unit
  refine isSD_stdLat L S.Hm (y • S.Hm.adjugate) h.Hm_int (fun i j => ?_) ?_
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (adjugate_int L _ h.Hm_int i j)
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hyd, one_smul]

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG
  haveI := nontrivial L
  have hsd := isSD_coordLat S hG
  have hmem : ∀ v : S.V, v ∈ coordLat S ↔ ∀ i, v i ∈ L.O := fun v => mem_stdLat L v
  have h1 : ∀ a, S.f a ∈ coordLat S := fun a => (hmem _).2 (hG.f_int a)
  have h2 : ∀ a, S.f' a ∈ coordLat S := fun a => (hmem _).2 (hG.f'_int a)
  have h3 : ∀ a, S.es a ∈ coordLat S := fun a => (hmem _).2 (hG.es_int a)
  have h4 : ∀ a, S.es' a ∈ coordLat S := fun a => (hmem _).2 (hG.es'_int a)
  have hint : ∀ x ∈ coordLat S, ∀ y ∈ coordLat S, hf L S.Hm x y ∈ L.O :=
    fun x hx y hy => (hsd.2 y).2 hy x hx
  have hZ : IsIntM L S.Zh := fun a b => hint _ (h2 b) _ (h1 a)
  have hU : IsUnit (S.D (Fin.last (r + 1))) := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  obtain ⟨-, u, hu, hud⟩ := hG.D_unit _ hU.ne_zero
  have hDet : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  rw [hDet] at hud
  have e1 : S.Zh * (u • S.Zh.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, hud, one_smul]
  have e2 : (u • S.Zh.adjugate) * S.Zh = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hud, one_smul]
  generalize hPdef : u • S.Zh.adjugate = P at e1 e2
  have hP : IsIntM L P := fun i j => by
    rw [← hPdef, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hu (adjugate_int L _ hZ i j)
  haveI : IsNoetherianRing L.O := by
    obtain ⟨-, -, -, hpid, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    infer_instance
  have hfg : (coordLat S).FG := hsd.1.1
  have hh := S.herm.1

  have hc : ∀ a, hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
      if a = Fin.last r then 1 else 0 := fun a => by
    have : hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
        L.cj ((S.Zh * P) a (Fin.last r)) := by
      rw [hf_sum_right, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hf_smul_right, map_mul, mul_comm, hf_symm L hh]
      rfl
    rw [this, e1, Matrix.one_apply]
    split_ifs <;> simp

  have hc' : ∀ b, hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
      if b = Fin.last r then 1 else 0 := fun b => by
    have : hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
        (P * S.Zh) (Fin.last r) b := by
      rw [hf_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hf_smul_right, L.cj_cj]
      rfl
    rw [this, e2, Matrix.one_apply]
    simp [eq_comm]
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.HL.FrameLift.core S S.f S.es S.T S.gram S.dual S.iso (coordLat S) hfg
    hsd.2 h1 h3 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun b => hP _ _) h2) hc
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.HL.FrameLift.core S S.f' S.es' S.T' S.gram' S.dual' S.iso' (coordLat S)
    hfg hsd.2 h2 h4 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun a => cj_int L (hP _ _)) h1) hc'
  refine ⟨(A, B, S.graphOf (coordLat S)), hA, hB, one_mem _, one_mem _, ?_, ?_, fun b => ?_, rfl⟩
  · rw [one_smul]; exact hA'
  · rw [one_smul]; exact hB'
  · refine ⟨S.f' b - S.f b, sub_mem (h2 b) (h1 b), ?_⟩
    simp [Frames.th, hG.gg]

end GlobalTheory.HL.CoordGood
