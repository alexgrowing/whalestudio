import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInvLower
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin

noncomputable section

namespace GlobalTheory.TypeAsm.NFEx

section Mat
variable {K : Type} [Field K] [StarRing K]

open Classical in

noncomputable def cb (b : K × ℕ) : Kˣ × ℕ+ :=
  if h : b.1 ≠ 0 ∧ 1 ≤ b.2 then (Units.mk0 (star b.1) (star_ne_zero.2 h.1), ⟨b.2, h.2⟩) else (1, 1)

theorem entry_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (a c : ℕ) :
    Formalism.MainNotions.S.Loc.ptEntryL (bs.map cb) a c = star (Formalism.MainNotions.S.ptEntry bs a c) := by
  induction bs generalizing a c with
  | nil => simp [Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have h := hb (t, s) (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, cb, dif_pos h, Formalism.MainNotions.S.Loc.ptEntryL, Formalism.MainNotions.S.ptEntry, PNat.mk_coe, Units.val_mk0]
    simp only [ih', apply_ite star, star_zero]
    exact if_congr Iff.rfl (if_congr Iff.rfl rfl rfl) (if_congr Iff.rfl rfl rfl)

theorem size_cb (bs : List (K × ℕ)) (hb : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) :
    ((bs.map cb).map (fun b => (b.2 : ℕ))).sum = (bs.map Prod.snd).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have h := hb b (by simp)
    have ih' := ih (fun b hb' => hb b (by simp [hb']))
    simp only [List.map_cons, List.sum_cons, cb, dif_pos h, PNat.mk_coe, ih']

end Mat
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
section Mat2
variable {K : Type} [Field K] [StarRing K]

noncomputable def toPt {n : ℕ} (p : Formalism.MainNotions.S.Point K n) : Formalism.MainNotions.S.Loc.Pt K n where
  blocks := p.1.map cb
  size := (size_cb p.1 p.2.1).trans p.2.2

theorem toPt_mat {n : ℕ} (p : Formalism.MainNotions.S.Point K n) (a b : Fin n) :
    (toPt p).mat a b = star (Formalism.MainNotions.S.ptMat p a b) :=
  entry_cb p.1 p.2.1 a.val b.val

def sgnR (r : ℕ) {n : ℕ} (b : Fin n) : ℤˣ := (-1) ^ (r - b.val)

theorem decomp {n r : ℕ} (Z : Matrix (Fin n) (Fin n) K) (p : Formalism.MainNotions.S.Point K n)
    (h : Formalism.MainNotions.S.IsInCell (fun a b => (-1 : K) ^ (r - b.val) * Z a b) p) :
    ∃ A B : Matrix (Fin n) (Fin n) K, (∀ a b, a < b → A a b = 0 ∧ B b a = 0) ∧ (∀ a, A a a = 1 ∧ B a a = 1) ∧
      Z.map star = A * Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) * B := by
  obtain ⟨L, U, hL, hU, hZ⟩ := h
  set s : Fin n → K := fun b => (-1 : K) ^ (r - b.val) with hs_def
  have hs : ∀ b, s b * s b = 1 := fun b => by
    simp only [hs_def, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hss : ∀ b, star (s b) = s b := fun b => by simp [hs_def]
  have hsg : ∀ b : Fin n, (((sgnR r b : ℤˣ) : ℤ) : K) = s b := fun b => by
    simp [sgnR, hs_def]
  have hZ' : Z = L * Formalism.MainNotions.S.ptMat p * U * Matrix.diagonal s := by
    ext a b
    rw [Matrix.mul_diagonal, ← hZ]
    show Z a b = s b * Z a b * s b
    rw [mul_comm (s b), mul_assoc, hs, mul_one]
  have hD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hs]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  have hDs : (Matrix.diagonal s).map star = Matrix.diagonal s := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hss]
    · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨L.map star, Matrix.diagonal s * U.map star * Matrix.diagonal s, fun a b hab => ⟨?_, ?_⟩, fun a => ⟨?_, ?_⟩, ?_⟩
  · simp [(hL a b).1 hab]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU b a).1 hab]
  · simp [(hL a a).2 rfl]
  · rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [(hU a a).2 rfl, hs]
  · have hP : Matrix.of (fun a b => (toPt p).mat a b * (((sgnR r b : ℤˣ) : ℤ) : K)) =
        (Formalism.MainNotions.S.ptMat p).map star * Matrix.diagonal s := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.of_apply, toPt_mat, hsg, Matrix.map_apply]
    have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map star = M.map star * N.map star := fun M N =>
      (Matrix.map_mul (f := starRingEnd K) (L := M) (M := N))
    rw [hP, hZ', hmap, hmap, hmap, hDs]
    calc L.map star * (Formalism.MainNotions.S.ptMat p).map star * U.map star * Matrix.diagonal s
        = L.map star * (Formalism.MainNotions.S.ptMat p).map star * (Matrix.diagonal s * Matrix.diagonal s) * U.map star *
            Matrix.diagonal s := by rw [hD, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

end Mat2
end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem zhat_eq {D : D7} {X : HidaSetting D} {Y : Full X} {u : D.what₂.Word} (t : GTu Y u)
    (j : ℕ) (hj : j ≤ D.R.rS + 1) :
    (Formalism.HermitianLatticeCounting.S6.Zhat (F0 X u) (Ft t)).submatrix (Fin.castLE hj) (Fin.castLE hj) =
      ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (star : D.host.E → D.host.E) := by
  refine Matrix.ext fun a b => ?_
  exact a_herm (S := VS D) ((F0 X u).e (Fin.castLE hj a)) ((Ft t).e (Fin.castLE hj b))

end GlobalTheory.TypeAsm.NFEx

namespace GlobalTheory.TypeAsm.NFEx
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt
  Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfExC (hHost : HostC) : NFExC := by
  intro D large₂ X Y u hStd t ht
  obtain ⟨hr, hG, -⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  have hjT := index_eq_normalForm t hN
  have hH := hHost D large₂ hStd
  obtain ⟨hrel, -⟩ := relRepC D X Y u u t hr hG
  have hTu := tie_Tu_pos D u
  have hj' : j ≤ D.R.rS + 1 := hj.trans (Nat.le_succ _)
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl (frq X t.rep).fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu (frq X t.rep)) hrel
  have hDG : Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl j ≠ 0 := by
    rw [nf_Dl _ _ (fixedFlag_level_ne_zero D u) (nf_T_ne D u) j hj']
    exact star_ne_zero.2 hN.2.2.1
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point hj'
    ((Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl).submatrix (Fin.castLE hj') (Fin.castLE hj'))
    (by rw [← tie_Dl_eq']; exact hDG) (geo j hj' (Or.inl ⟨hj, hDG⟩))
  obtain ⟨A, B, h0, h1, hZ⟩ := decomp _ p hp
  obtain ⟨N, hNj, -, hNT, hN𝔡, hF, hF'⟩ := GlobalTheory.DegCnt.RatNormal.exists_nf D.host.E (VS D).V (HV D) hH.1 D.R.rS
    (F0 X u) (Ft t) j hj c (Tu D u) (dI D) (toPt p) (fun b => sgnR D.R.rS b) A B hN rfl rfl
    (fun σ => nf_pos _ _ (p_posX D _ hTu _) σ) hH.2.2.2.2.2.2.2.1 hH.2.2.2.2.2.2.2.2.1 h0 h1
    (by rw [zhat_eq t j hj']; exact hZ)
  exact ⟨N, ⟨hN𝔡, hF, hF'⟩, hNj.trans hjT.symm, hNT⟩

end GlobalTheory.TypeAsm.NFEx

theorem GlobalTheory.TypeAsm.nfExC_holds : GlobalTheory.TypeAsm.NFExC := GlobalTheory.TypeAsm.NFEx.nfExC GlobalTheory.T.unitaryHostFieldArithmeticConditions
