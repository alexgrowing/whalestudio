import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameVectorLatticeCriterion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

set_option maxHeartbeats 1000000 in

theorem latV_normalFrame_zero_loc : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → ∀ (a : ℕ) (ha : 0 + a = G.s + 1) (Λ L : GlobalTheory.FinPl.Lat (c.V 0)), Formalism.L2.DIV.IsFrame β Λ → GlobalTheory.FinPl.Moves (c.V 0) b Λ L (· = G.q.v) → ∀ y : XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin a → G.k, (fun r => G.q.sec (((G.FY 0 a ha).β *ᵥ y) r)) ∈ GlobalTheory.FinPl.latV (c.V 0) L (· = G.q.v) ↔ (∀ z, y (Sum.inl z) ∈ 𝒪[G.k]) ∧ ∀ i : Fin a, ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k] := by
  intro D c v G PP b β hloc n hn Λ L hβ hmv y
  obtain rfl : n = G.s + 1 := by omega
  obtain ⟨e, -, hM⟩ := hloc.frame (G.s + 1) hn
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame G.q hloc.idem (c.V 0) Λ β hβ
  have hb := GlobalTheory.LocMod.liftM_map β.val
  have h1 := hM _ hb
  have h2 := hB1 _ hb
  rw [GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul] at h2
  rw [Matrix.map_mul, h2] at h1
  let ε := e.symm.trans (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hn)
  let X := (G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val
  let P := (mt (c.V 0) b).map G.q.pr
  let Pi := (mt (c.V 0) b⁻¹).map G.q.pr
  have h1' : P * B.val = X.submatrix id ε := h1
  have hPPi : P * Pi = 1 := by
    change (mt (c.V 0) b).map G.q.pr * (mt (c.V 0) b⁻¹).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, mul_inv_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hPiP : Pi * P = 1 := by
    change (mt (c.V 0) b⁻¹).map G.q.pr * (mt (c.V 0) b).map G.q.pr = 1
    rw [← Matrix.map_mul, ← GlobalTheory.LocMod.mt_mul_gaMat, inv_mul_cancel, GlobalTheory.LocMod.mt_one_gaMat,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hX : X = (P * B.val).submatrix id ε.symm := by
    rw [h1', submatrix_submatrix, Function.comp_id, Equiv.self_comp_symm, submatrix_id_id]
  let z := (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y
  have hw : (G.FY 0 (G.s + 1) hn).β *ᵥ y = (P * B.val) *ᵥ (z ∘ ε) := by
    have e1 : (G.FY 0 (G.s + 1) hn).β *ᵥ y = X *ᵥ z := by
      change _ = ((G.FY 0 (G.s + 1) hn).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn).val) *ᵥ
        ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hn)⁻¹).val *ᵥ y)
      rw [mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [e1, hX, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_id]
  have key : (fun r => G.q.sec (((G.FY 0 (G.s + 1) hn).β *ᵥ y) r)) =
      mt (c.V 0) b *ᵥ (fun r => G.q.sec ((Pi *ᵥ ((G.FY 0 (G.s + 1) hn).β *ᵥ y)) r)) := by
    rw [GlobalTheory.Core.Mi.LatMatch.mulVec_sec_split]
    change _ = fun r => G.q.sec ((P *ᵥ (Pi *ᵥ _)) r)
    rw [mulVec_mulVec, hPPi, one_mulVec]
  rw [key, ← hmv _ (fun i => GlobalTheory.FrameGlob.sec_mem_idAt G.q _), hB2, hw, mulVec_mulVec, mulVec_mulVec]
  have hB : (B⁻¹).val * Pi * (P * B.val) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPiP, Matrix.one_mul, Units.inv_mul]
  rw [hB, one_mulVec]
  have hz : ∀ w, z w = (GlobalTheory.LevZeroUp.scal (Fin D.R.t) G.S.ϖ w)⁻¹ * y w := by
    intro w
    change ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val *ᵥ y) w = _
    rw [GlobalTheory.LevZeroUp.bas_inv_val, mulVec_diagonal]
  have hall : (∀ i, (z ∘ ε) i ∈ 𝒪[G.k]) ↔ ∀ w, z w ∈ 𝒪[G.k] :=
    ⟨fun h w => by simpa using h (ε.symm w), fun h i => h _⟩
  rw [hall, Sum.forall]
  refine and_congr (forall_congr' fun w => ?_) (forall_congr' fun i => ?_)
  · rw [hz]
    simp [GlobalTheory.LevZeroUp.scal]
  · rw [hz]
    rfl

end GlobalTheory.LevZero

end
