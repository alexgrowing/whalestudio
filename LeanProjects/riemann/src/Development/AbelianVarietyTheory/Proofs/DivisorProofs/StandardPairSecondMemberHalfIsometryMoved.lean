import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove

open GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)

variable {D : D7}

private theorem gram_inv_cT {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (V'.gram⁻¹) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q) = HMul.hMul I.P (V.gram⁻¹) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hg : cT σ I.P * V'.gram * I.P = V.gram := I.gram
  have hg' : cT σ I.Q * V.gram * I.Q = V'.gram := I.symm.gram
  have hPQh : cT σ I.Q * cT σ I.P = 1 := by rw [← cT_mul, I.PQ, cT_one]
  have hQPh : cT σ I.P * cT σ I.Q = 1 := by rw [← cT_mul, I.QP, cT_one]
  by_cases hu : IsUnit V.gram.det
  · have hinv : V'.gram⁻¹ = I.P * V.gram⁻¹ * cT σ I.P := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← hg']
      calc cT σ I.Q * V.gram * I.Q * (I.P * V.gram⁻¹ * cT σ I.P)
          = cT σ I.Q * (V.gram * (I.Q * I.P) * V.gram⁻¹) * cT σ I.P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.QP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hPQh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [hinv, Matrix.mul_assoc, hQPh, Matrix.mul_one]
  · have hu' : ¬ IsUnit V'.gram.det := by
      intro h'
      apply hu
      refine Matrix.isUnit_det_of_right_inverse (B := I.Q * V'.gram⁻¹ * cT σ I.Q) ?_
      rw [← hg]
      calc cT σ I.P * V'.gram * I.P * (I.Q * V'.gram⁻¹ * cT σ I.Q)
          = cT σ I.P * (V'.gram * (I.P * I.Q) * V'.gram⁻¹) * cT σ I.Q := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ h', Matrix.mul_one, hQPh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu', Matrix.zero_mul,
      Matrix.mul_zero]

private theorem cT_gram {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P) V'.gram = HMul.hMul V.gram I.Q := by
  show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

private theorem sandwich {R : Type} [CommRing R] {s s' t t' : ℕ} (aQ : Matrix (Fin s) (Fin s') R) (aP : Matrix (Fin s') (Fin s) R)
    (G' : Matrix (Fin s') (Fin s') R) (cQ : Matrix (Fin s') (Fin s) R) (G : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (cP : Matrix (Fin t) (Fin t') R) (H' : Matrix (Fin t') (Fin t') R) (H : Matrix (Fin t) (Fin t) R)
    (tQ : Matrix (Fin t) (Fin t') R) (tP : Matrix (Fin t') (Fin t) R)
    (h1 : G' * cQ = aP * G) (h2 : cP * H' = H * tQ) (hs : aQ * aP = 1) (ht : tQ * tP = 1) :
    aQ * (G' * (cQ * (Y * cP)) * H') * tP = G * Y * H := by
  calc _ = aQ * (G' * cQ) * Y * (cP * H') * tP := by simp only [Matrix.mul_assoc]
    _ = (aQ * aP) * G * Y * H * (tQ * tP) := by rw [h1, h2]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]

private theorem adj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (y : WO S T) :
    HMul.hMul (HMul.hMul IS.aQ (HMul.hMul (HMul.hMul ((S'.gram⁻¹).map (incA D))
      (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose)) (T'.gram.map (incA D)))) IT.aP
      = HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose))
          (T.gram.map (incA D)) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hc : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (M.map (incA D)).map (cA D) = (M.map σ).map (incA D) := by
    intro m n M; ext i j; exact (rfl : cA D (incA D (M i j)) = incA D (σ (M i j)))
  have h1 : HMul.hMul ((S'.gram⁻¹).map (incA D)) ((IS.aQ.map (cA D)).transpose) = HMul.hMul IS.aP ((S.gram⁻¹).map (incA D)) := by
    rewrite [IsoMat.aQ, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aP, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (gram_inv_cT IS)
  have h2 : HMul.hMul ((IT.aP.map (cA D)).transpose) (T'.gram.map (incA D)) = HMul.hMul (T.gram.map (incA D)) IT.aQ := by
    rewrite [IsoMat.aP, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aQ, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (cT_gram IT)
  have hy : (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose) =
      HMul.hMul ((IS.aQ.map (cA D)).transpose) (HMul.hMul (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) ((IT.aP.map (cA D)).transpose)) := by
    rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  rewrite [hy]
  exact sandwich _ _ _ _ _ _ _ _ _ _ _ h1 h2 IS.aQ_aP IT.aQ_aP

private theorem sandwich2 {R : Type} [CommRing R] {s s' t t' : ℕ} (ri : Matrix (Fin s') (Fin s) R) (bi : Matrix (Fin s) (Fin s) R)
    (fq : Matrix (Fin s) (Fin s') R) (N' : Matrix (Fin s') (Fin t') R) (fp : Matrix (Fin t') (Fin t) R)
    (b : Matrix (Fin t) (Fin t) R) (rx : Matrix (Fin t) (Fin t') R) (N : Matrix (Fin s) (Fin t) R) (h : fq * N' * fp = N) :
    ri * bi * fq * N' * (fp * b * rx) = ri * (bi * N * b) * rx := by
  rw [← h]; simp only [Matrix.mul_assoc]

private theorem fQ_eq {V V' : HSp D} (I : IsoMat V V') : fQ I = I.aQ.map (toEAf D) := by
  ext i j; rfl

private theorem fP_eq {V V' : HSp D} (I : IsoMat V V') : fP I = I.aP.map (toEAf D) := by
  ext i j; rfl

private theorem frMapAdj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    frMapAdj S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IS.rank_eq) (frMapAdj S T βS βT y)) (rdx (K := Lev.EAf D) IT.rank_eq) := by
  have hk := congrArg (Matrix.map · (toEAf D)) (adj_homMap IS IT y)
  rewrite [Matrix.map_mul, Matrix.map_mul, ← fQ_eq, ← fP_eq] at hk
  exact sandwich2 (rdi (K := Lev.EAf D) IS.rank_eq) (βS⁻¹).val (fQ IS) _ (fP IT) βT.val (rdx (K := Lev.EAf D) IT.rank_eq) _ hk

private theorem rdi_mul_mul_rdx {K : Type} [CommRing K] {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (N : Matrix (Fin m) (Fin n) K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h1) N) (rdx (K := K) h2) = N.submatrix (finCongr h1).symm (finCongr h2).symm := by
  subst h1 h2
  ext i j
  simp [rdi, rdx, Matrix.one_apply]

private theorem dualCoord_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y).submatrix (finCongr IS.rank_eq).symm (finCongr IT.rank_eq).symm := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
  rw [frMapAdj_homMap, rdi_mul_mul_rdx]
  rfl

private theorem isHalf_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (c : AE D) (y : WO S T) :
    IsHalf c (homMap IS IT y) ↔ IsHalf c y := by
  have hs : ∀ {m n : ℕ} (u : Mx D m n), IsHalf c u ↔ c • u = u := fun u =>
    ⟨fun h => Matrix.ext fun i j => (h i j : _), fun h i j => (congrFun (congrFun h i) j : _)⟩
  rw [hs, hs]
  have hm : c • homMap IS IT y = homMap IS IT (c • y) := by
    rw [homMap_apply, homMap_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [hm, (homMap IS IT).injective.eq_iff]

private theorem read_cond {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (a : ℕ) (N : Matrix (Fin m) (Fin n) (Lev.EAf D)) :
    ((Formalism.IndefR.Datum.IsIntM (N.submatrix (finCongr h1).symm (finCongr h2).symm) ∧
        ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N.submatrix (finCongr h1).symm (finCongr h2).symm i j)) ↔
      (Formalism.IndefR.Datum.IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j))) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a (N.submatrix (finCongr h1).symm (finCongr h2).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N) := by
  subst h1 h2
  have e0 : N.submatrix (finCongr (rfl : m = m)).symm (finCongr (rfl : n = n)).symm = N := by
    ext i j; rfl
  rw [e0]
  exact ⟨Iff.rfl, rfl⟩

theorem _root_.GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) := by
  intro D S S' T T' IS IT ν e I a βS βT
  funext w
  obtain ⟨y, rfl⟩ : ∃ y, w = homMap IS IT y := ⟨(homMap IS IT).symm w, ((homMap IS IT).apply_symm_apply w).symm⟩
  have hy : GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) (homMap IS IT y) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT y := by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT ((homMap IS IT).symm (homMap IS IT y)) = _
    rw [(homMap IS IT).symm_apply_apply]
  rw [hy]
  obtain ⟨h1, h2⟩ := read_cond IS.rank_eq IT.rank_eq ν e I a (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  split_ifs with hA hB hB
  · rw [dualCoord_homMap, h2]
  · exfalso; apply hB; rw [isHalf_homMap, dualCoord_homMap, h1] at hA; exact hA
  · exfalso; apply hA; rw [isHalf_homMap, dualCoord_homMap, h1]; exact hB
  · rfl

end GlobalTheory.TriMove

end
