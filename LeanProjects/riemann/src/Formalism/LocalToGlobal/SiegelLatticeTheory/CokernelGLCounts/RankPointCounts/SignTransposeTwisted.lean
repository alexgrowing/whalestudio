import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MapInvMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModelKS

noncomputable section

namespace Formalism.L2.SG.Pf.TupGlobApprox

open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.Pf.ProdEApprox Formalism.L2.SG.Pf.PCount ValuativeRel

section Theta

variable {K : Type*} [CommRing K] {r : ℕ}

theorem signMatrix_transpose : (Sg K r).transpose = Sg K r := Matrix.diagonal_transpose _

theorem theta_mul (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M * N).transpose * Sg K r = (Sg K r * N.transpose * Sg K r) * (Sg K r * M.transpose * Sg K r) := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Sg K r) (Sg K r), sg_sq, Matrix.one_mul]

theorem theta_theta (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Sg K r * M.transpose * Sg K r).transpose * Sg K r = M := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, signMatrix_transpose, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [sg_sq, Matrix.mul_one, ← Matrix.mul_assoc, sg_sq, Matrix.one_mul]

theorem theta_stab {a Y b : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : a * Y * b = Y) :
    (Sg K r * b.transpose * Sg K r) * (Sg K r * Y.transpose * Sg K r) * (Sg K r * a.transpose * Sg K r) =
      Sg K r * Y.transpose * Sg K r := by
  rw [← theta_mul, ← theta_mul, ← Matrix.mul_assoc, h]

theorem theta_sub_one (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (M - 1).transpose * Sg K r = Sg K r * M.transpose * Sg K r - 1 := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, sg_sq]

theorem theta_lo {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUp U) : IsLo (Sg K r * U.transpose * Sg K r) :=
  isLo_conj (isLo_transpose h) _ _ (fun a => sgn_sq' r a)

theorem theta_up {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLo L) : IsUp (Sg K r * L.transpose * Sg K r) :=
  isUp_conj (isUp_transpose h) _ _ (fun a => sgn_sq' r a)

theorem neg_one_pow_mem (J : AddSubgroup K) (k : ℕ) {x : K} (hx : x ∈ J) : (-1 : K) ^ k * x ∈ J := by
  rcases neg_one_pow_eq_or K k with h | h <;> rw [h]
  · rwa [one_mul]
  · rw [neg_one_mul]; exact J.neg_mem hx

theorem ent_theta {J : AddSubgroup K} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : EntIn J M) :
    EntIn J (Sg K r * M.transpose * Sg K r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  rw [mul_comm]
  exact neg_one_pow_mem J _ (neg_one_pow_mem J _ (h j i))

theorem sign_transpose_twisted (s e : K) (cf : Fin (r + 1) → K) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (s • (Matrix.diagonal cf * (Z.transpose * Sg K r) * Matrix.diagonal cf) - e • Ecorner r).transpose *
      Sg K r = s • (Matrix.diagonal cf * (Z * Sg K r) * Matrix.diagonal cf) - e • Ecorner r := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Ecorner, Matrix.of_apply]
  have hs := sgn_sq' (R := K) r
  by_cases hij : i = Fin.last r ∧ j = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · have hji : ¬ (j = Fin.last r ∧ i = Fin.last r) := fun h => hij ⟨h.2, h.1⟩
    rw [if_neg hij, if_neg hji]
    linear_combination (s * cf i * cf j * Z i j * (-1 : K) ^ (r - j.val)) * hs i

theorem theta_move (cf cfi : Fin (r + 1) → K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Sg K r * (Matrix.diagonal cfi * (Sg K r * A.transpose * Sg K r) * Matrix.diagonal cf).transpose * Sg K r =
      Matrix.diagonal cf * A * Matrix.diagonal cfi := by
  ext i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  have hs := sgn_sq' (R := K) r
  linear_combination (cf i * A i j * cfi j * (-1 : K) ^ (r - j.val) * (-1 : K) ^ (r - j.val)) * hs i +
    (cf i * A i j * cfi j) * hs j

end Theta

section ModelR

variable {Fp Ep : Type} [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [CommRing Ep] [Algebra Fp Ep]
  [TopologicalSpace Ep] [MeasurableSpace Ep]

theorem mem_R_of (M : Formalism.MainNotions.S.Loc.Model Fp Ep) (g : Formalism.MainNotions.S.Loc.SplitG M.L) (hM : M.split = some g) (x : Ep)
    (h1 : (g.e x).1 ∈ 𝒪[Fp]) (h2 : (g.e x).2 ∈ 𝒪[Fp])
    (h3 : ∃ t ∈ 𝒪[Fp], (g.e x).1 - (g.e x).2 = (g.q : Fp) * t) : x ∈ M.R := by
  obtain ⟨L, sp, mu⟩ := M
  change Formalism.MainNotions.S.Loc.SplitG L at g
  obtain rfl : sp = some g := hM
  exact (Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x).2 ⟨h1, h2, h3⟩

end ModelR

section Place

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.TupGlob
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem ptMat_mono' (w : Point D.host.E (D.R.rS + 1)) : ptMat w = mono (fσ w) (fun a => pv w.1 a) := by
  ext a b
  rw [ptMat_fσ]
  rfl

def gX (L₁ X' : PairVal.MatR D) : PairVal.MatR D := L₁ * X' * L₁⁻¹

def gY (w : Point D.host.E (D.R.rS + 1)) (U₁ X' : PairVal.MatR D) : PairVal.MatR D :=
  U₁⁻¹ * (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹ * U₁

theorem glob_stab (w : Point D.host.E (D.R.rS + 1)) {Z₁ L₁ U₁ X' : PairVal.MatR D} (hL₁ : IsLo L₁) (hU₁ : IsUp U₁)
    (hZ : Z₁ * Sg D.host.E D.R.rS = L₁ * ptMat w * U₁) (hX' : IsLo X')
    (hpat : ∀ i j, fσ w j < fσ w i → X' i j = 0) :
    IsLo (gX L₁ X') ∧ IsUp (gY w U₁ X') ∧
      gX L₁ X' * (Z₁ * Sg D.host.E D.R.rS) * gY w U₁ X' = Z₁ * Sg D.host.E D.R.rS := by
  have hν : ∀ a : Fin (D.R.rS + 1), IsUnit (pv w.1 a) := fun a => IsUnit.mk0 _ (pv_ne' w a)
  have hup := cOf_up (fσ_fσ w) (fun a => pv w.1 a) X' hX'.1 hpat hν
  have hc : IsUp (cOf (fσ w) (fun a => pv w.1 a) X') := ⟨hup.1, fun a b hab => hup.2 b a hab⟩
  have hdc : IsUnit (cOf (fσ w) (fun a => pv w.1 a) X').det := by rw [det_up' hc]; exact isUnit_one
  have hdL : IsUnit L₁.det := by rw [det_lo' hL₁]; exact isUnit_one
  have hdU : IsUnit U₁.det := by rw [det_up' hU₁]; exact isUnit_one
  refine ⟨isLo_mul (isLo_mul hL₁ hX') (isLo_inv hL₁), isUp_mul (isUp_mul (isUp_inv hU₁) (isUp_inv hc)) hU₁, ?_⟩
  have hfix := fix_cOf (fσ_fσ w) (fun a => pv w.1 a) hν X'
  rw [hZ, ptMat_mono']
  simp only [gX, gY, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc L₁⁻¹ L₁, Matrix.nonsing_inv_mul _ hdL, Matrix.one_mul, ← Matrix.mul_assoc U₁ U₁⁻¹,
    Matrix.mul_nonsing_inv _ hdU, Matrix.one_mul, ← Matrix.mul_assoc X' (mono (fσ w) (fun a => pv w.1 a)), hfix,
    Matrix.mul_assoc (mono (fσ w) (fun a => pv w.1 a)),
    ← Matrix.mul_assoc (cOf (fσ w) (fun a => pv w.1 a) X') (cOf (fσ w) (fun a => pv w.1 a) X')⁻¹,
    Matrix.mul_nonsing_inv _ hdc, Matrix.one_mul]

theorem locL_lo (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsLo (locL Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locL, hM]
  · exact isLo_conj (isLo_map _ hA) _ _ (fun a => by simp only [← map_mul, cf_cfi, map_one])
  · exact isLo_glue _ (isLo_conj (isLo_map _ hA) _ _ (cf_cfi Zd p))
      (isLo_conj (theta_lo (isUp_map _ hB)) _ _ (cf_cfi Zd p))

theorem locR_up (p : PlF D) {A B : PairVal.MatR D} (hA : IsLo A) (hB : IsUp B) : IsUp (locR Zd p A B) := by
  rcases hM : (Zd.M p).split with _ | g <;> simp only [locR, hM]
  · exact isUp_conj (isUp_map _ hB) _ _ (fun a => by simp only [← map_mul, cfi_cf, map_one])
  · exact isUp_glue _ (isUp_conj (isUp_map _ hB) _ _ (cfi_cf Zd p))
      (isUp_conj (theta_up (isLo_map _ hA)) _ _ (cfi_cf Zd p))

theorem key_stab (p : PlF D) {l ρ L R Yp : MatP D p} (hl : TieN.IntLow (Zd.M p) l) (hρ : TieN.IntUp (Zd.M p) ρ)
    (h : L * Yp * R = l * Yp * ρ) : (l⁻¹ * L) * Yp * (R * ρ⁻¹) = Yp := by
  obtain ⟨-, hll, -⟩ := ZsVolGrp.intLow_inv (Zd.M p) hl
  obtain ⟨-, -, hρρ⟩ := ZsVolGrp.intUp_inv (Zd.M p) hρ
  calc (l⁻¹ * L) * Yp * (R * ρ⁻¹) = l⁻¹ * (L * Yp * R) * ρ⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Yp := by
      rw [h]
      simp only [Matrix.mul_assoc]
      rw [hρρ, Matrix.mul_one, ← Matrix.mul_assoc, hll, Matrix.one_mul]

theorem corr_move (u u' : D.what₂.Word) (p : PlF D) {Z₁ A₀ B₀ X Y : PairVal.MatR D} (hA₀ : IsLo A₀) (hB₀ : IsUp B₀)
    (hX : IsLo X) (hY : IsUp Y) (hst : X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS) :
    locL Zd p (A₀ * X) (Y * B₀) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
        locR Zd p (A₀ * X) (Y * B₀) =
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ := by
  have h2 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ := by
    rw [Matrix.mul_assoc (A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀), sg_sq, Matrix.mul_one]
  have h3 : A₀ * (Z₁ * Sg D.host.E D.R.rS) * B₀ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS =
      (A₀ * X) * (Z₁ * Sg D.host.E D.R.rS) * (Y * B₀) := by
    rw [h2]
    conv_lhs => rw [← hst]
    simp only [Matrix.mul_assoc]
  exact (locMove Zd u u' p (isLo_mul hA₀ hX) (isUp_mul hY hB₀) h3).symm.trans (locMove Zd u u' p hA₀ hB₀ h2)

theorem locL_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locL Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
      A.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
  simp only [locL, hM]

theorem locR_L (p : PlF D) (hM : (Zd.M p).split = none) (A B : PairVal.MatR D) :
    locR Zd p A B = Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) *
      B.map (D.s.atP p).ιE * Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := by
  simp only [locR, hM]

section Typed

variable (p : PlF D) {g : Loc.SplitG (Zd.M p).L} (hM : (Zd.M p).split = some g)
  {e : (D.s.atP p).Ep ≃ₐ[(D.s.atP p).Fp] (D.s.atP p).Fp × (D.s.atP p).Fp} (hge : g.e = e)
include hM hge

theorem leftLocal_firstProj (A B : PairVal.MatR D) : (locL Zd p A B).map (p1 e) =
    Matrix.diagonal (cf Zd p) * A.map ((p1 e).comp (D.s.atP p).ιE) * Matrix.diagonal (cfi Zd p) := by
  simp only [locL, hM, hge, glue_map_fst]

theorem leftLocal_secondProj (A B : PairVal.MatR D) : (locL Zd p A B).map (p2 e) =
    Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 e).comp (D.s.atP p).ιE)).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cfi Zd p) := by
  simp only [locL, hM, hge, glue_map_snd]

theorem rightLocal_firstProj (A B : PairVal.MatR D) : (locR Zd p A B).map (p1 e) =
    Matrix.diagonal (cfi Zd p) * B.map ((p1 e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p) := by
  simp only [locR, hM, hge, glue_map_fst]

theorem rightLocal_secondProj (A B : PairVal.MatR D) : (locR Zd p A B).map (p2 e) =
    Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS * (A.map ((p2 e).comp (D.s.atP p).ιE)).transpose *
      Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p) := by
  simp only [locR, hM, hge, glue_map_snd]

end Typed

end Place

end Formalism.L2.SG.Pf.TupGlobApprox
