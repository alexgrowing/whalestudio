import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.ReadAtBase

theorem mat_read {k : Type} [CommRing k] {N Y : Type} [Fintype N] [DecidableEq N] [Fintype Y] [DecidableEq Y] (σ : N ≃ Y)
    (β' βi' W Mi M0 : Matrix N N k) (Fb : Matrix N Y k) (Fg : Matrix Y N k) (bs bi X : Matrix Y Y k)
    {Yy G : Matrix _ _ k} (h1 : β' * W * βi' = Mi * Yy * M0) (hY : Yy = Fb * G * Fg) (hG : G = bs * X * bi) (h2 : βi' * β' = 1) (h3 : M0 * Mi = 1)
    (h4 : Fg * Fb = 1) (h5 : bi * bs = 1) (h6 : β' = (Mi * Fb * bs).submatrix id σ) :
    W = X.submatrix σ σ := by
  subst hY hG
  have hs : ∀ (M : Matrix N N k) (P : Matrix N Y k), M * P.submatrix id σ = (M * P).submatrix id σ := fun M P => by
    ext i j; simp [Matrix.mul_apply]
  have hA : β' * W = β' * X.submatrix σ σ := by
    have e1 : β' * W = β' * W * βi' * β' := by rw [Matrix.mul_assoc (β' * W), h2, Matrix.mul_one]
    rw [e1, h1, h6, hs, Matrix.submatrix_mul_equiv _ _ _ σ]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M0 Mi, h3, Matrix.one_mul, ← Matrix.mul_assoc Fg Fb, h4, Matrix.one_mul,
      h5, Matrix.mul_one]
  calc W = βi' * β' * W := by rw [h2, Matrix.one_mul]
    _ = βi' * β' * X.submatrix σ σ := by rw [Matrix.mul_assoc, hA, ← Matrix.mul_assoc]
    _ = X.submatrix σ σ := by rw [h2, Matrix.one_mul]

end GlobalTheory.ReadAtBase

namespace GlobalTheory.ReadAtBase

theorem map_mt_conj {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t y : GA D V) :
    (Formalism.L2.Theta.mt V (t⁻¹ * y * t)).map p.π =
      (Formalism.L2.Theta.mt V t⁻¹).map p.π * (Formalism.L2.Theta.mt V y).map p.π * (Formalism.L2.Theta.mt V t).map p.π := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem map_mt_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k) (V : HSp D) (t : GA D V) :
    (Formalism.L2.Theta.mt V t).map p.π * (Formalism.L2.Theta.mt V t⁻¹).map p.π = 1 := by
  rw [← Matrix.map_mul]
  simp [Formalism.L2.Theta.mt]

theorem map_inv_mul {R k : Type} [CommRing R] [CommRing k] {n : ℕ} (f : R →+* k) (β : GL (Fin n) R) :
    (β⁻¹).val.map f * β.val.map f = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (g : GL (Fin n) A) (i j : Fin n) :
    (Formalism.UG.bc f g).val i j = f (g.val i j) := rfl

theorem intGL_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : GL (Fin n) (Formalism.L2.Herm.intAf F E)) (i j : Fin n) :
    (intGL F E n w).val i j = (w.val i j : E ⊗[F] Formalism.L2.Herm.Af F) := rfl
end GlobalTheory.ReadAtBase

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ReadAtBase.red_of_isLoc : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (hr : D.R.r ≤ (d.st 0).V.rank) (hc : 0 + (G.s + 1) = G.s + 1) (x : G.S.P.J) (y : GA D (d.st 0).V), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) hc) y ((GlobalTheory.StepData.typeFrame G.S.ϖ (GlobalTheory.StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj (GlobalTheory.StepData.reGL (GlobalTheory.StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))) → Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0) ∈ Formalism.L2.DIV.St (d.st 0).β → G.Red x (Formalism.L2.DIV.upperLeftBlock hr (Formalism.L2.DIV.redFn (d.st 0).β PP (Formalism.IndefR.Lev.finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)))) := by
  intro D u d τ PP G hr hc x y hL hSt
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP G.idem
  have hπ' : ∀ a, π' (toEAf D a) = (GlobalTheory.LocMod.ofSplit G.q).π a := hπ
  obtain ⟨w, hw⟩ := hSt
  rw [← hw, Formalism.L2.DIV.redFn_frGL]
  obtain ⟨e, he, hmv⟩ := G.frame 0 (G.s + 1) hc
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo (GlobalTheory.LocMod.ofSplit G.q) (G.FY 0 (G.s + 1) hc) hπ' _ _ hmv
  have hn : (d.st 0).V.rank ≤ D.R.r := by
    have h1 := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_mul, add_zero] at h1
    have h2 := G.hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  intro a b a' b' ha hb z hz
  have hrb : ((upperLeftBlock hr ((Formalism.UG.bc (resS D.host.F PP)) w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) =
      (((Formalism.UG.bc (resS D.host.F PP)) w) : Matrix _ _ (kP PP)).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    refine upper_block_val_submatrix hr ?_
    intro i j hij
    exfalso
    have hi : blk2 D.R.r i = 0 := by simp [blk2, show i.val < D.R.r from lt_of_lt_of_le i.2 hn]
    rw [hi] at hij
    exact Nat.not_lt_zero _ hij
  rw [hrb] at hz
  have hpos : ∀ (c : Fin D.R.k ⊕ Fin (G.s + 1)) (c' : Fin D.R.r), c'.val = IndefiniteRowSideFullHecke.FramePositiveSum.framePos D.R.k (G.s + 1) c →
      Fin.castLE hr c' = e (StepData.ixZero _ _ c) := by
    intro c c' hc'
    ext
    rw [Fin.val_castLE, he, hc']
    rcases c with c | c <;> rfl
  rw [Matrix.submatrix_apply, hpos a a' ha, hpos b b' hb] at hz
  have e1 : frGL (d.st 0).β w = (d.st 0).β * Formalism.L2.DIV.intGL _ _ _ w * ((d.st 0).β)⁻¹ := rfl
  have e2 := congrArg Units.val (e1.symm.trans hw)
  rw [Units.val_mul, Units.val_mul] at e2
  have h1 := congrArg (Matrix.map · π') e2
  simp only [Matrix.map_mul] at h1
  have e4 : (finE (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).val.map π' =
      (Formalism.L2.Theta.mt (d.st 0).V ((d.t 0)⁻¹ * y * d.t 0)).map (GlobalTheory.LocMod.ofSplit G.q).π := by
    ext i j
    exact hπ' _
  have h1' := (h1.trans e4).trans (GlobalTheory.ReadAtBase.map_mt_conj (GlobalTheory.LocMod.ofSplit G.q) _ (d.t 0) y)
  have hG : ((StepData.typeFrame G.S.ϖ (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)).conj
      ((StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t))) x)).val =
      ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc).val *
        (StepData.reGL (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)
          (StepData.reGL (StepData.ixZero (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t)) (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k))).val *
        (((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) hc)⁻¹).val := rfl
  have hW := GlobalTheory.ReadAtBase.mat_read ((e.symm).trans (StepData.stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) hc)) _ _ _ _ _ _ _ _ _ _ h1' hL.2
    hG (GlobalTheory.ReadAtBase.map_inv_mul _ _)
    (GlobalTheory.ReadAtBase.map_mt_inv _ _ _) (G.FY 0 (G.s + 1) hc).γβ (Units.inv_mul _) hβ
  have h := congrFun (congrFun hW (e (StepData.ixZero _ _ a))) (e (StepData.ixZero _ _ b))
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.trans_apply, Equiv.symm_apply_apply, StepData.reGL_val] at h
  simp only [GlobalTheory.ReadAtBase.intGL_apply] at h
  simp only [GlobalTheory.ReadAtBase.bc_apply] at hz
  have hz0 : resS D.host.F PP (w.val (e (StepData.ixZero _ _ a)) (e (StepData.ixZero _ _ b)) - oToS D.host.F D.host.E z) = 0 := by
    rw [map_sub, resS_oToS, hz]
    exact sub_self _
  have hv := (hred.ker _).1 hz0
  simp only [RingHom.comp_apply, Subring.coe_subtype, AddSubgroupClass.coe_sub, map_sub, h] at hv
  have e8 : π' ((oToS _ _ z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Datum.EAf D) =
      (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := hπ' (incA D (z : D.host.E))
  rw [e8] at hv
  exact hv
