import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionConjFrameEqCastReductionAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterInvMulDiagEmbeddingEqCharDetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricCharacterInvEqInvDetBlockStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterComplexEqLevelCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistResidueCharacterComplexEqLevelCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section
namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_self {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : LiftBrg.castGL (rfl : m = m) x = x := by
  ext i j
  simp [LiftBrg.castGL]

theorem coarse_eq_blkOf' {a r t m : ℕ} (hn : a = r + m * t) (i : Fin a) :
    Formalism.L2.Col.coarse r (List.replicate m t) i.val = Formalism.L2.DIV.blkOf r t i := by
  unfold Formalism.L2.DIV.blkOf
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp at hn
        omega
      · exact h0
    rw [Formalism.L2.Col.blkIdx_replicate ht m _ (by omega)]

theorem coarseBlockIndex_single_eq_twoBlock {a r b : ℕ} (hn : a = r + b) (i : Fin a) :
    Formalism.L2.Col.coarse r [b] i.val = Formalism.L2.DIV.blk2 r i := by
  unfold Formalism.L2.DIV.blk2
  split_ifs with hi
  · exact Formalism.L2.Col.coarse_of_lt hi
  · rw [Formalism.L2.Col.coarse_of_le (Nat.not_lt.mp hi)]
    have hi2 := i.2
    have : i.val - r < b := by omega
    simp [Formalism.L2.Col.blkIdx, this]

theorem castGL_inv_mul_diag_mem_HKV {κ : Type} [CommRing κ] {a n r t : ℕ} (h : a = n) (hn : n = r + t) (hra : r ≤ a)
    (hrn : r ≤ n) (y : GL (Fin a) κ) (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t)) :
    (LiftBrg.castGL h y)⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) ∈ Formalism.L2.Col.HKV κ n r t := by
  subst h
  rw [castGL_self]
  have hn' : a = r + 1 * t := by rw [hn, one_mul]
  have hy' : y ∈ Formalism.L2.Col.blockUT _ κ r (List.replicate 1 t) := by
    intro i j hij
    apply hy
    have hij' : Formalism.L2.Col.coarse r (List.replicate 1 t) j.val < Formalism.L2.Col.coarse r (List.replicate 1 t) i.val := hij
    rw [coarse_eq_blkOf' hn', coarse_eq_blkOf' hn'] at hij'
    exact hij'
  have hy2 : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := Formalism.L2.DIV.blockTri_blkOf_le r t hy
  show _ ∈ Formalism.L2.Col.HK a κ r (List.replicate 1 t)
  refine Formalism.L2.Col.mem_HK.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hy')
    (Formalism.L2.Col.diagEmb_mem_blockUT hrn _ _), fun i j hi hj => ?_⟩
  let Y : Formalism.L2.Col.blockUT _ κ r (List.replicate 1 t) := ⟨y, hy'⟩
  let Dd : Formalism.L2.Col.blockUT _ κ r (List.replicate 1 t) :=
    ⟨_, Formalism.L2.Col.diagEmb_mem_blockUT hrn (List.replicate 1 t) (Formalism.L2.DIV.upperLeftBlock hra y)⟩
  have hD : Formalism.L2.Col.blk0 _ κ hrn (List.replicate 1 t) Dd = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val]
    ext i' j'
    exact Formalism.L2.Col.diagMat_of_lt _ (show (Fin.castLE hrn i').val < r from i'.2) (show (Fin.castLE hrn j').val < r from j'.2)
  have hY : Formalism.L2.Col.blk0 _ κ hrn (List.replicate 1 t) Y = Formalism.L2.DIV.upperLeftBlock hra y := by
    apply Units.ext
    rw [Formalism.L2.Col.blockZero_val, Formalism.L2.DIV.upper_block_val_submatrix hra hy2]
    rfl
  have h1 : Formalism.L2.Col.blk0 _ κ hrn (List.replicate 1 t) (Y⁻¹ * Dd) = 1 := by
    rw [map_mul, map_inv, hD, hY, inv_mul_cancel]
  have h2 := congrArg (fun g : GL (Fin r) κ => (g : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩) h1
  simp only [Formalism.L2.Col.blockZero_val, Units.val_one] at h2
  have h3 : ((y⁻¹ * Formalism.L2.Col.diagEmb κ hrn (Formalism.L2.DIV.upperLeftBlock hra y) : GL _ κ) : Matrix _ _ κ) i j =
      (1 : Matrix (Fin r) (Fin r) κ) ⟨i.val, hi⟩ ⟨j.val, hj⟩ := h2
  rw [h3]
  simp only [Matrix.one_apply, Fin.ext_iff]

theorem castGL_inv_mem_HQ {κ : Type} [CommRing κ] {a n r b : ℕ} (h : a = n) (hn : n = r + b) (y : GL (Fin a) κ)
    (hy : y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    (LiftBrg.castGL h y)⁻¹ * 1 ∈ Formalism.L2.Col.HQ κ n r b := by
  subst h
  rw [castGL_self, mul_one]
  refine Subgroup.inv_mem _ ?_
  intro i j hij
  apply hy
  have hij' : Formalism.L2.Col.coarse r [b] j.val < Formalism.L2.Col.coarse r [b] i.val := hij
  rw [coarseBlockIndex_single_eq_twoBlock hn, coarseBlockIndex_single_eq_twoBlock hn] at hij'
  exact hij'

theorem lev_lam_congr' {κ K : Type} [CommRing κ] [Field K] {n : ℕ} {l l' : Formalism.L2.Col.Lev κ K n} (e : l = l')
    {x x' : GL (Fin n) κ} (hx : x ∈ l.H) (hx' : x' ∈ l'.H) (ex : x = x') : l.lam ⟨x, hx⟩ = l'.lam ⟨x', hx'⟩ := by
  subst e
  subst ex
  rfl

theorem mem_inv_grp {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Formalism.L2.Col.LevFam E K n SG) (x : Formalism.L2.Col.GLG E n SG) (h : ∀ w, x w ∈ (Λ w).H) : x ∈ Λ.inv.grp :=
  fun w _ => h w

theorem inv_chr_apply {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Formalism.L2.Col.LevFam E K n SG) (x : Formalism.L2.Col.GLG E n SG) (h : ∀ w, x w ∈ (Λ w).H) :
    Λ.inv.chr ⟨x, mem_inv_grp Λ x h⟩ = ∏ w, ((Λ w).lam ⟨x w, h w⟩)⁻¹ := by
  exact Formalism.L2.Col.piChar_apply (fun w => (Λ.inv w).H) (fun w => (Λ.inv w).lam) ⟨x, mem_inv_grp Λ x h⟩

theorem prod_of_mem_or {α β : Type} [CommMonoid β] {A B S : Finset α} (hS : ∀ x, x ∈ S ↔ x ∈ A ∨ x ∈ B)
    (h : Disjoint A B) (f : α → β) : ∏ x ∈ S, f x = (∏ x ∈ A, f x) * ∏ x ∈ B, f x := by
  classical
  rw [← Finset.prod_union h]
  congr 1
  ext x
  rw [hS, Finset.mem_union]

end GlobalTheory.Mem.R3.LiftBrg.ActQ

noncomputable section
namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

set_option maxHeartbeats 4000000 in

theorem inv_redZ_mul_g0Hat_type : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
      ∃ hh : (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (LiftBrg.ActQ.redQ X I U L eG i t κ) ∈
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
        X.toD7.what₂.embLL (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr ⟨_, hh⟩ : X.B.fields.Kˣ) : X.B.fields.K) =
          (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) := by
  intro X px I U L eG hI hV hL hG i t A k hF κ
  classical
  set y := Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) with hy
  have hQ : y ∈ Formalism.L2.DIV.parLev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (L.datVt i t) := mem_parLev_of_Q X I U L i t κ
  have hZ : ∀ w, redZ X I U L i t A k κ w =
      LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1 y) := GlobalTheory.T.reduction_conj_frame_eq_cast_reduction_at_level_prime X px I U L hL i t A k hF κ
  have hn : X.B.R.nV = X.B.R.r + X.B.R.t := rfl
  have hgg : ∀ (w : Pl X.toD7.host.E) (hw : w ∈ (X.B.primes px).vGs) (hPg : w ∈ L.Pg) (z : G0 L.Pg X.toD7.R.r),
      (eG.symm z) ⟨w, hw⟩ = z ⟨w, hPg⟩ := fun w hw hPg z => by
    rw [← hG (eG.symm z) w hw hPg, MulEquiv.apply_symm_apply]
  have hG1 : ∀ (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (hw : w.1 ∈ (X.B.primes px).vGs),
      Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ) w =
        Formalism.L2.Col.diagEmb (𝓞 X.B.fields.E ⧸ w.1.asIdeal) (Formalism.L2.Col.r_le_nV X.B.R)
          (Formalism.L2.DIV.upperLeftBlock (L.datVt i t).hr (Formalism.L2.DIV.redFn (L.βV i) w.1 y)) := fun w hw => by
    have hPg : w.1 ∈ L.Pg := by rw [hL.Pg]; exact hw
    rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_mem _ w hw]
    show Formalism.L2.Col.diagEmb _ (Formalism.L2.Col.r_le_nV X.B.R) ((redQ X I U L eG i t κ) ⟨w.1, hw⟩) = _
    rw [redQ_apply, hgg w.1 hw hPg]
    rfl
  have hG2 : ∀ (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (hw : w.1 ∉ (X.B.primes px).vGs),
      Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ) w = 1 := fun w hw => by
    rw [Formalism.L2.Col.unipotentGroupBlockEmbedding, MonoidHom.comp_apply, Formalism.L2.Col.extGLG_of_not _ w hw]
  have eQ : L.Q t = Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
    rw [hL.Q t]
    simp only [ColIn.Q, tup_ixOf]
    rfl
  have hwQ : ∀ (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1), w.1 ∉ (X.B.primes px).vGs →
      w.1 ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) := fun w hw =>
    (Finset.mem_union.1 w.2).resolve_left hw
  have hM1 : ∀ (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (hw : w.1 ∈ (X.B.primes px).vGs),
      Formalism.L2.DIV.redFn (L.βV i) w.1 y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) := fun w hw => by
    have hPg : w.1 ∈ (L.datVt i t).Pg := by show w.1 ∈ L.Pg; rw [hL.Pg]; exact hw
    exact Formalism.L2.DIV.parLev_g hQ hPg
  have hM2 : ∀ (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (hw : w.1 ∉ (X.B.primes px).vGs),
      Formalism.L2.DIV.redFn (L.βV i) w.1 y ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 X.B.R.r) := fun w hw => by
    have hq : w.1 ∈ (L.datVt i t).Q := by show w.1 ∈ L.Q t; rw [eQ]; exact hwQ w hw
    exact Formalism.L2.DIV.parLev_q hQ hq
  have hmem : ∀ w, ((redZ X I U L i t A k κ)⁻¹ *
      Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ)) w ∈
        (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H := fun w => by
    show (redZ X I U L i t A k κ w)⁻¹ * _ ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H
    rw [hZ w]
    by_cases hw : w.1 ∈ (X.B.primes px).vGs
    · rw [Formalism.L2.Col.mtTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw, hG1 w hw]
      exact castGL_inv_mul_diag_mem_HKV _ hn _ _ _ (hM1 w hw)
    · rw [Formalism.L2.Col.mtTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw, hG2 w hw]
      exact castGL_inv_mem_HQ _ hn _ (hM2 w hw)
  refine ⟨mem_inv_grp _ _ hmem, ?_⟩
  rw [inv_chr_apply _ _ hmem]
  set F : Pl X.toD7.host.E → ℂ := fun P => if P ∈ (X.B.primes px).vGs then
      (((L.chi ((i : ℕ) + 1) P)⁻¹ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ)
    else ((L.xiR t P (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 X.B.R.r) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) with hFdef
  have hF1 : ∀ P (h : P ∈ (X.B.primes px).vGs), F P =
      (((L.chi ((i : ℕ) + 1) P)⁻¹ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) :=
    fun P h => if_pos h
  have hF2 : ∀ P (h : P ∉ (X.B.primes px).vGs), F P =
      ((L.xiR t P (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 X.B.R.r) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) :=
    fun P h => if_neg h
  have hval : ∀ w, X.toD7.what₂.embLL ((((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam ⟨_, hmem w⟩)⁻¹ :
      X.B.fields.Kˣ) : X.B.fields.K) = F w.1 := fun w => by
    by_cases hw : w.1 ∈ (X.B.primes px).vGs
    · have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w = Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hw⟩ := by
        rw [Formalism.L2.Col.mtTyKK, Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw]
      have hz := castGL_inv_mul_diag_mem_HKV (LiftBrg.rkEq X i).symm hn (L.datVt i t).hr (Formalism.L2.Col.r_le_nV X.B.R) _ (hM1 w hw)
      have ex : ((redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ)) w =
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1 y))⁻¹ *
            Formalism.L2.Col.diagEmb _ (Formalism.L2.Col.r_le_nV X.B.R) (Formalism.L2.DIV.upperLeftBlock (L.datVt i t).hr (Formalism.L2.DIV.redFn (L.βV i) w.1 y)) := by
        show (redZ X I U L i t A k κ w)⁻¹ * _ = _
        exact congrArg₂ (· * ·) (congrArg (·⁻¹) (hZ w)) (hG1 w hw)
      rw [lev_lam_congr' e (hmem w) hz ex]
      have key : (Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hw⟩).lam ⟨_, hz⟩ =
          Formalism.L2.Col.chiAt I.Ch ⟨w.1, hw⟩ (i : ℕ) (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) 1 (Formalism.L2.DIV.redFn (L.βV i) w.1 y)) :=
        GlobalTheory.T.levelCharacter_inv_mul_diagEmbedding_eq_char_det (LiftBrg.rkEq X i).symm hn (L.datVt i t).hr (Formalism.L2.Col.r_le_nV X.B.R) _ (hM1 w hw) _ hz
      rw [key, Units.val_inv_eq_inv_val]
      erw [map_inv₀]
      rw [hF1 _ hw, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      exact congrArg (·⁻¹) (GlobalTheory.T.column_character_complex_eq_level_character X px I U L hI hL i w.1 hw _)
    · have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w =
          Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K)) ⟨w.1, hwQ w hw⟩ := by
        rw [Formalism.L2.Col.mtTyKK, Formalism.L2.Col.LevFam.glue_of_not _ _ w hw]
      have hz := castGL_inv_mem_HQ (LiftBrg.rkEq X i).symm hn _ (hM2 w hw)
      have ex : ((redZ X I U L i t A k κ)⁻¹ *
          Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_nV X.B.R) (redQ X I U L eG i t κ)) w =
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1 y) :
            GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal))⁻¹ * 1 := by
        show (redZ X I U L i t A k κ w)⁻¹ * _ = _
        exact congrArg₂ (· * ·) (congrArg (·⁻¹) (hZ w)) (hG2 w hw)
      rw [lev_lam_congr' e (hmem w) hz ex]
      have key : (Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K))
          ⟨w.1, hwQ w hw⟩).lam ⟨_, hz⟩ =
          (Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w.1
            (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 X.B.R.r) 1 (Formalism.L2.DIV.redFn (L.βV i) w.1 y)))⁻¹ :=
        GlobalTheory.T.upperParahoric_character_inv_eq_inv_det_block (LiftBrg.rkEq X i).symm hn _ (hM2 w hw) _ hz
      rw [key, inv_inv, hF2 _ hw]
      exact GlobalTheory.T.twist_residue_character_complex_eq_level_character X px I U L hI hV hL t w.1 (hwQ w hw) _
  have hdis : Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K)) :=
    GlobalTheory.NormOneUnit.disjoint_vGs_QE t.1 (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1 hI.sel_ok hI.g_mem
  have eL : X.toD7.what₂.embLL ((∏ w, ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam ⟨_, hmem w⟩)⁻¹ :
      X.B.fields.Kˣ) : X.B.fields.K) = ∏ w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1, F w.1 := by
    rw [Units.coe_prod]
    erw [map_prod]
    exact Finset.prod_congr rfl fun w _ => hval w
  have eR : (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).ch κ : ℂˣ) : ℂ) =
      (∏ P ∈ L.Pg, (((L.chi ((i : ℕ) + 1) P)⁻¹
        (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ)) *
      ∏ P ∈ L.Q t, ((L.xiR t P (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 X.B.R.r) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) := by
    show ((Formalism.L2.DIV.levFn (L.βV i) (flagL (L.datVt i t)) y : ℂˣ) : ℂ) = _
    have e0 : Formalism.L2.DIV.ext1 (flagL (L.datVt i t)).P.H (flagL (L.datVt i t)).P.chi
        (Formalism.L2.DIV.rTup (L.βV i) (flagL (L.datVt i t)) y) = 1 := by
      unfold Formalism.L2.DIV.ext1
      split_ifs <;> rfl
    unfold Formalism.L2.DIV.levFn
    rw [e0, one_mul, Units.val_mul]
    congr 1
    · rw [Units.coe_prod]
      exact Finset.prod_congr rfl fun P _ => congrArg Units.val (Finset.prod_range_one _)
    · rw [Units.coe_prod]
      rfl
  have hA : ∏ P ∈ (X.B.primes px).vGs, F P =
      ∏ P ∈ L.Pg, (((L.chi ((i : ℕ) + 1) P)⁻¹
        (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf X.B.R.r X.B.R.t) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) := by
    rw [hL.Pg]
    exact Finset.prod_congr rfl fun P hP => hF1 P hP
  have hB : ∏ P ∈ Formalism.L2.Col.QE I.sel (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K), F P =
      ∏ P ∈ L.Q t, ((L.xiR t P (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 X.B.R.r) 1 (Formalism.L2.DIV.redFn (L.βV i) P y)) : ℂˣ) : ℂ) := by
    rw [eQ]
    exact Finset.prod_congr rfl fun P hP => hF2 P (Finset.disjoint_right.1 hdis hP)
  rw [eL]
  exact (Finset.prod_coe_sort _ F).trans ((prod_of_mem_or (fun x => Finset.mem_union) hdis F).trans
    ((congrArg₂ (· * ·) hA hB).trans eR.symm))

end GlobalTheory.Mem.R3.LiftBrg.ActQ
