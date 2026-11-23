import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies

noncomputable section

open scoped Classical
open Matrix

namespace Formalism.L2.SG.DetUU

section Gram

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

open Formalism.MainNotions.S

def uCat (F : FlagG S r T) (F' : FlagG S r T') : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fvec F'.fvec

def gramCat (F : FlagG S r T) (F' : FlagG S r T') : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  Matrix.of fun i j => S.hT (uCat F F' i) (uCat F F' j)

def lastDiag (c : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem fvec_castSucc (F : FlagG S r T) (a : Fin r) : F.fvec (Fin.castSucc a) = F.e a := by
  simp [FlagG.fvec]

theorem gram_self (F : FlagG S r T) :
    (Matrix.of fun a b => S.hT (F.fvec a) (F.fvec b)) = lastDiag (-T) := by
  ext a b
  simp only [Matrix.of_apply, lastDiag]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm]; simp
    | cast b =>
      rw [fvec_last, fvec_castSucc]
      have h1 := S.herm.eq (F.e b) F.z
      rw [F.z_orth b, map_zero] at h1
      rw [← h1]
      simp [Fin.castSucc_ne_last]
  | cast a =>
    induction b using Fin.lastCases with
    | last => rw [fvec_castSucc, fvec_last, F.z_orth]; simp [Fin.castSucc_ne_last]
    | cast b => rw [fvec_castSucc, fvec_castSucc, F.e_iso]; simp [Fin.castSucc_ne_last]

theorem gramCat_eq (F : FlagG S r T) (F' : FlagG S r T') :
    gramCat F F' = Matrix.fromBlocks (lastDiag (-T)) (Zhat F F') (Zhat F F')ᴴ (lastDiag (-T')) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁]
    exact congrFun (congrFun (gram_self F) a) b
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂]
    rfl
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply]
    show S.hT (F'.fvec a) (F.fvec b) = star (S.hT (F.fvec b) (F'.fvec a))
    rw [← S.herm.eq (F.fvec b) (F'.fvec a)]
    rfl
  · simp only [gramCat, uCat, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂]
    exact congrFun (congrFun (gram_self F') a) b

theorem lastDiag_mul_mul (c c' : E) (X : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    lastDiag c * X * lastDiag c' = lastDiag (c * X (Fin.last r) (Fin.last r) * c') := by
  ext a b
  simp only [lastDiag, Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]

theorem det_sub_lastDiag (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c : E) :
    (M - lastDiag c).det = M.det - c * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  have h1 : M - lastDiag c = M.updateRow (Fin.last r) (M (Fin.last r) - c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb
        simp [lastDiag]
      · simp [lastDiag, hb, Pi.single_apply]
    · simp [lastDiag, Matrix.updateRow_ne ha, ha]
  rw [h1, sub_eq_add_neg (M (Fin.last r)), ← neg_smul, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, neg_mul, ← sub_eq_add_neg]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · simp [Matrix.updateRow_self, Fin.succAbove_last]
    congr 1
    ext a b
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]
  · intro j _ hj
    simp [Matrix.updateRow_self, Pi.single_apply, hj]
  · simp

theorem leadMinor_full (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : leadMinorE B (r + 1) = B.det := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  congr 1

theorem leadMinor_r (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE B r = (B.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dif_pos (Nat.le_succ r)]
  rfl

theorem gram_det_eq (F : FlagG S r T) (F' : FlagG S r T') (hB : (Zhat F F').det ≠ 0) :
    ∃ s : E, s * s = 1 ∧ (gramCat F F').det = s * Gflag F F' := by
  set B := Zhat F F' with hBdef
  letI : Invertible B := invertibleOfIsUnitDet B (isUnit_iff_ne_zero.2 hB)
  set P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E := Matrix.fromBlocks 0 1 1 0 with hP
  have hPP : P * P = 1 := by
    rw [hP, Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have hs : P.det * P.det = 1 := by rw [← det_mul, hPP, det_one]
  have hsw : gramCat F F' * P = Matrix.fromBlocks B (lastDiag (-T)) (lastDiag (-T')) Bᴴ := by
    rw [gramCat_eq, hP, Matrix.fromBlocks_multiply]; simp [hBdef]
  have h1 := congrArg Matrix.det hsw
  rw [det_mul, det_fromBlocks₁₁ B (lastDiag (-T)) (lastDiag (-T')) Bᴴ] at h1
  have hm : lastDiag (-T') * ⅟B * lastDiag (-T) = lastDiag ((-T') * (⅟B) (Fin.last r) (Fin.last r) * (-T)) :=
    lastDiag_mul_mul _ _ _
  rw [hm, det_sub_lastDiag, det_conjTranspose] at h1
  have hsub : (Bᴴ.submatrix Fin.castSucc Fin.castSucc) = (B.submatrix Fin.castSucc Fin.castSucc)ᴴ := by
    ext a b; simp
  rw [hsub, det_conjTranspose] at h1
  have hinv : (⅟B) (Fin.last r) (Fin.last r) = B.det⁻¹ * (B.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [invOf_eq_nonsing_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
      adjugate_fin_succ_eq_det_submatrix]
    simp only [Fin.succAbove_last, Fin.val_last, smul_eq_mul]
    rw [← two_mul, pow_mul]
    norm_num
  rw [hinv] at h1
  refine ⟨P.det, hs, ?_⟩
  have key : (gramCat F F').det = P.det * (B.det * (star B.det - (-T') * (B.det⁻¹ *
      (B.submatrix Fin.castSucc Fin.castSucc).det) * (-T) * star (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
    calc (gramCat F F').det = (gramCat F F').det * (P.det * P.det) := by rw [hs, mul_one]
      _ = P.det * ((gramCat F F').det * P.det) := by ring
      _ = _ := by rw [h1]
  rw [key]
  unfold Gflag Dl
  rw [← hBdef, leadMinor_full, leadMinor_r]
  field_simp

end Gram

section Conc

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsTies Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def pseudoLat {ι : Type} (u : ι → (hS D).V) (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) (hS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ j, ∃ x ∈ I j, y = x • u j}

def GenIdxPseudo : Prop :=
  ∀ (D : D7) (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → (hS D).V)
    (I : ι → FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E),
    LinearIndependent D.host.E u → (∀ j, I j ≠ 0) → (∀ j, ∀ x ∈ I j, star x ∈ I j) →
    (Matrix.of fun i j => (hS D).hT (u i) (u j)).det ≠ 0 →
    genIdx (hS D) (dualIn (hS D) (pseudoLat u I)) (pseudoLat u I) =
      |((Algebra.norm ℚ (Matrix.of fun i j => (hS D).hT (u i) (u j)).det : ℚ) : ℝ)| *
        ∏ j, ((FractionalIdeal.absNorm (I j) : ℚ) : ℝ) ^ 2

def aaF (D : D7) (a : Fin (D.R.rS + 1)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  if (a : ℕ) < D.R.rS then ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) else 1

theorem aaF_castSucc (a : Fin D.R.rS) : aaF D (Fin.castSucc a) = ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) := by
  unfold aaF
  rw [if_pos (by simp)]
  simp

theorem aaF_last : aaF D (Fin.last D.R.rS) = 1 := by
  unfold aaF
  rw [if_neg (by simp)]

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
  exact differentIdeal_ne_bot

theorem aaF_ne_zero (a : Fin (D.R.rS + 1)) : aaF D a ≠ 0 := by
  unfold aaF
  split_ifs
  · exact zpow_ne_zero _ ddS_ne_zero
  · exact one_ne_zero

theorem aaF_star (a : Fin (D.R.rS + 1)) : ∀ x ∈ aaF D a, star x ∈ aaF D a := by
  intro x hx
  unfold aaF at hx ⊢
  split_ifs at hx ⊢ with h
  · have ha : (a : ℕ) ≤ D.R.rS := h.le
    have e : ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) =
        (((dI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
      rw [show (-((D.R.rS : ℤ) - (a : ℕ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℤ)) by push_cast [Nat.cast_sub ha]; ring,
        _root_.zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
      rfl
    rw [e] at hx ⊢
    exact star_mem_inv _ hx
  · obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨o', ho'⟩ := star_int o
    exact (FractionalIdeal.mem_one_iff _).2 ⟨o', by rw [← ho']⟩

theorem uu_eq (Λ : Submodule (𝓞 D.host.E) (hS D).V) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)
    (F' : LFlag (hS D) D.R.rS T') (hX : XLam Λ F = XS D F.fl) (hX' : XLam Λ F' = XS D F'.fl)
    (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    UU Λ F F' = pseudoLat (DetUU.uCat F.fl F'.fl) (Sum.elim (aaF D) (aaF D)) := by
  unfold UU
  rw [hX, hX', hz, hz']
  apply le_antisymm
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.subset_span ⟨Sum.inl (Fin.castSucc a), x, ?_, ?_⟩
      · simpa [aaF_castSucc] using hx
      · simp [DetUU.uCat, DetUU.fvec_castSucc]
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      refine Submodule.subset_span ⟨Sum.inl (Fin.last _), 1, ?_, ?_⟩
      · simp only [Sum.elim_inl, aaF_last]; exact FractionalIdeal.one_mem_one _
      · simp [DetUU.uCat, DetUU.fvec_last]
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      refine Submodule.subset_span ⟨Sum.inr (Fin.castSucc a), x, ?_, ?_⟩
      · simpa [aaF_castSucc] using hx
      · simp [DetUU.uCat, DetUU.fvec_castSucc]
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      refine Submodule.subset_span ⟨Sum.inr (Fin.last _), 1, ?_, ?_⟩
      · simp only [Sum.elim_inr, aaF_last]; exact FractionalIdeal.one_mem_one _
      · simp [DetUU.uCat, DetUU.fvec_last]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, x, hx, rfl⟩
    rcases j with a | a
    · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
      · simp only [Sum.elim_inl, aaF_castSucc] at hx
        simp only [DetUU.uCat, Sum.elim_inl, DetUU.fvec_castSucc]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left
          (Submodule.subset_span ⟨a', x, hx, rfl⟩)))
      · simp only [Sum.elim_inl, aaF_last] at hx
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
        simp only [DetUU.uCat, Sum.elim_inl, DetUU.fvec_last]
        rw [algebraMap_smul]
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
          (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))))
    · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
      · simp only [Sum.elim_inr, aaF_castSucc] at hx
        simp only [DetUU.uCat, Sum.elim_inr, DetUU.fvec_castSucc]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a', x, hx, rfl⟩))
      · simp only [Sum.elim_inr, aaF_last] at hx
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
        simp only [DetUU.uCat, Sum.elim_inr, DetUU.fvec_last]
        rw [algebraMap_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ o (Submodule.mem_span_singleton_self _))

theorem uCat_indep {T T' : D.host.E} (F : FlagG (hS D) D.R.rS T) (F' : FlagG (hS D) D.R.rS T')
    (h : (DetUU.gramCat F F').det ≠ 0) : LinearIndependent D.host.E (DetUU.uCat F F') := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hG : (DetUU.gramCat F F').mulVec c = 0 := by
    funext k
    have h1 := congrArg (fun v => (hS D).hT (DetUU.uCat F F' k) v) hc
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h1
    simp only [DetUU.gramCat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero h hG) i

end Conc

section Final

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsTies Formalism.L2.SG.NGCut.LeadingMinorIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sum_sub_eq_frameExp : ∑ a : Fin D.R.rS, (D.R.rS - (a : ℕ)) = frameExp D.R.rS D.R.rS := by
  rw [Fin.sum_univ_eq_sum_range (fun a => D.R.rS - a), frameExp]
  have key : ∀ n r : ℕ, ∑ a ∈ Finset.range n, (r - a) = ∑ a ∈ Finset.Icc 1 n, (r + 1 - a) := by
    intro n r
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      congr 1
      omega
  exact key _ _

theorem prod_absNorm_aaF :
    ∏ a : Fin (D.R.rS + 1), ((FractionalIdeal.absNorm (aaF D a) : ℚ) : ℝ) =
      (((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ frameExp D.R.rS D.R.rS := by
  have hN : ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = (D.host.rdE ^ D.R.f) ^ 2 := by
    show ((FractionalIdeal.absNorm ((dI D : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℚ) : ℝ) = _
    rw [FractionalIdeal.coeIdeal_absNorm, ← absNorm_dI]
    push_cast; rfl
  rw [Fin.prod_univ_castSucc, aaF_last, map_one, Rat.cast_one, mul_one]
  have e : ∀ a : Fin D.R.rS, ((FractionalIdeal.absNorm (aaF D (Fin.castSucc a)) : ℚ) : ℝ) =
      (((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ (D.R.rS - (a : ℕ)) := by
    intro a
    have ha : (a : ℕ) ≤ D.R.rS := a.isLt.le
    rw [aaF_castSucc, show (-((D.R.rS : ℤ) - (a : ℕ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℤ)) by
      push_cast [Nat.cast_sub ha]; ring, _root_.zpow_neg, zpow_natCast, map_inv₀, map_pow]
    push_cast
    rw [hN, inv_pow]
  rw [Finset.prod_congr rfl fun a _ => e a, Finset.prod_pow_eq_pow_sum, sum_sub_eq_frameExp]

theorem embS_gval_real (T : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') (τ : D.what₂.Tau) :
    embS D τ (Gval (T.fl t) (T.fl' t)) = (((embS D τ (Gval (T.fl t) (T.fl' t))).re : ℝ) : ℂ) := by
  have e1 : ∀ x : D.host.E, embS D τ (x * star x) = ((Complex.normSq (embS D τ x) : ℝ) : ℂ) := by
    intro x; rw [map_mul, Formalism.MainNotions.S.Pv.HH.embS_star, Complex.mul_conj]
  have hG : embS D τ (Gval (T.fl t) (T.fl' t)) =
      (((Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) (D.R.rS + 1)))) -
        ((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ) *
          Complex.normSq (embS D τ (leadMinorE (ZhatL (T.fl t) (T.fl' t)) D.R.rS)) : ℝ) : ℂ) := by
    show embS D τ (Gflag (T.fl t).fl (T.fl' t).fl) = _
    unfold Gflag Dl
    rw [map_sub, e1, map_mul, e1, map_mul, map_natCast, map_natCast]
    push_cast
    ring
  rw [hG, Complex.ofReal_re]

theorem detUUC_of (hGI : GenIdxPseudo) : DetUUC := by
  intro D X Y hF hI W H A hV u u' t hG
  set T := termTieOf W hI H A hV with hTdef
  have hX : XLam (T.abelian₂ t) (T.fl t) = XS D (T.fl t).fl :=
    ((Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D (W.δ u) (W.isom u) (X.Fu u) (Y.what₂ u) (Y.rowsOK u)).1 _
      (lamOf_mem W hI t)).2.2
  have hX' : XLam (T.abelian₂ t) (T.fl' t) = XS D (T.fl' t).fl := (pdC W hI t).2.2.2
  have hz : (T.fl t).zt = (T.fl t).fl.z := (T.fixed t).2.2.1.2
  have hz' : (T.fl' t).zt = (T.fl' t).fl.z := (T.lift' t).2
  have hD1 : (Zhat (T.fl t).fl (T.fl' t).fl).det ≠ 0 := by
    have h := (Formalism.MainNotions.BridgeLemma.GDr_of_tie T u u' t hG).1
    unfold Dl at h
    rwa [leadMinor_full] at h
  obtain ⟨s, hs, hdet⟩ := gram_det_eq (T.fl t).fl (T.fl' t).fl hD1
  have hGv : Gval (T.fl t) (T.fl' t) ≠ 0 := Formalism.MainNotions.BridgeLemma.tie_Gval_ne T t hG
  have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hs
  have hdet0 : (gramCat (T.fl t).fl (T.fl' t).fl).det ≠ 0 := by
    rw [hdet]; exact mul_ne_zero hs0 hGv
  have hgi := hGI D (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (uCat (T.fl t).fl (T.fl' t).fl)
    (Sum.elim (aaF D) (aaF D)) (uCat_indep _ _ hdet0) (by rintro (a | a) <;> exact aaF_ne_zero a)
    (by rintro (a | a) <;> exact aaF_star a) hdet0
  have hdet' : (Matrix.of fun i j => (hS D).hT (uCat (T.fl t).fl (T.fl' t).fl i)
      (uCat (T.fl t).fl (T.fl' t).fl j)).det = s * Gval (T.fl t) (T.fl' t) := hdet
  rw [hdet'] at hgi
  have hNs : |(Algebra.norm ℚ s : ℚ)| = 1 := by
    have h1 := congrArg (Algebra.norm ℚ) hs
    rw [map_mul, map_one] at h1
    have h2 : |(Algebra.norm ℚ s : ℚ)| * |(Algebra.norm ℚ s : ℚ)| = 1 := by rw [← abs_mul, h1, abs_one]
    nlinarith [abs_nonneg (Algebra.norm ℚ s : ℚ)]

  have hL : NG (T.abelian₂ t) (T.fl t) (T.fl' t) =
      Real.sqrt (|((Algebra.norm ℚ (Gval (T.fl t) (T.fl' t)) : ℚ) : ℝ)|) *
        ((((D.host.rdE ^ D.R.f) ^ 2)⁻¹) ^ frameExp D.R.rS D.R.rS) ^ 2 := by
    show Real.sqrt (genIdx (hS D) (dualIn (hS D) (UU (T.abelian₂ t) (T.fl t) (T.fl' t))) (UU (T.abelian₂ t) (T.fl t) (T.fl' t))) = _
    rw [uu_eq (T.abelian₂ t) (T.fl t) (T.fl' t) hX hX' hz hz', hgi, map_mul, Rat.cast_mul, abs_mul,
      show |((Algebra.norm ℚ s : ℚ) : ℝ)| = 1 by rw [← Rat.cast_abs, hNs, Rat.cast_one], one_mul,
      Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_pow, prod_absNorm_aaF, ← mul_pow, Real.sqrt_mul (abs_nonneg _),
      Real.sqrt_sq (by positivity)]
    ring

  have hpos : ∀ τ, 0 < (embS D τ (Gval (T.fl t) (T.fl' t))).re := fun τ =>
    Formalism.MainNotions.BridgeLemma.tie_G_pos T t hG (embS D τ)
  have hnorm : ∀ τ, ‖embS D τ (Gval (T.fl t) (T.fl' t))‖ = (embS D τ (Gval (T.fl t) (T.fl' t))).re := by
    intro τ
    rw [embS_gval_real T t τ, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_pos (hpos τ)]
  have hprod : ∏ τ, (embS D τ (Gval (T.fl t) (T.fl' t))).re =
      Real.sqrt (|((Algebra.norm ℚ (Gval (T.fl t) (T.fl' t)) : ℚ) : ℝ)|) := by
    have h := Formalism.L2.SG.WConst.prod_normSq_embS D (Gval (T.fl t) (T.fl' t))
    rw [← Finset.prod_congr rfl fun τ _ => hnorm τ, ← Rat.cast_abs, ← h, Finset.prod_pow,
      Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
  have hrd := rd_pos (D := D)
  have hW : Formalism.MainNotions.S.Pv.HH.wG D ^ 2 = ((D.host.rdE ^ (2 * frameExp D.R.rS D.R.rS)) ^ 2)⁻¹ := by
    unfold Formalism.MainNotions.S.Pv.HH.wG
    have e : (2 * (frameExp D.R.rS D.R.rS : ℝ)) = ((2 * frameExp D.R.rS D.R.rS : ℕ) : ℝ) := by push_cast; ring
    rw [e, rpow_negNat hrd, inv_pow]
  rw [hL, Finset.prod_congr rfl fun τ _ => gz_eq T t τ, Finset.prod_mul_distrib, hprod, Finset.prod_const,
    Finset.card_univ, D.what₂.card_Tau, hW]
  congr 1
  rw [inv_pow, inv_pow]
  congr 1
  simp only [← pow_mul]
  ring_nf

theorem gram_determinant_of_generic_index (hGI : GenIdxPseudo) : GramDeterminantCount := gramDeterminant_of_unipotent_det (detUUC_of hGI)

end Final

end Formalism.L2.SG.DetUU
