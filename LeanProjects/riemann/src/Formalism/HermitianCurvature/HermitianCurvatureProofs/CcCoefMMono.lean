import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousUnipotentVectorScalar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem xs_eq_phi {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (a : Wd.Ix (Fin w.length)) (h0 : C.LPt) (n : ℕ) (t : ℂ) (hc : r - i = r - D.ptSize (h0 ++ [(n + 1, t)]))
    (hpb : ∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) (ht : t ≠ 0) (hsz : D.ptSize (h0 ++ [(n + 1, t)]) = i)
    (e1 : r = D.ptSize h0 + (n + 1) + (r - i)) (e2 : D.ptSize h0 + (n + 1) + (r - i) = r)
    (hh : B.Mat k r → (Wq →L[ℂ] Wp)) :
    PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) hc hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
  subst hsz
  have hP : D.ptSize (h0 ++ [(n + 1, t)]) = D.ptSize h0 + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h0 (n + 1) t
  have hloc : D.IsLocPt (h0 ++ [(n + 1, t)]) (D.ptSize (h0 ++ [(n + 1, t)])) := by
    refine ⟨fun b hb => ?_, rfl⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact hpb b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact ⟨by omega, ht⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h0)) (Fin.cast hP q)).val = (D.ptPerm (h0 ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h0 ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h0) t (Fin.cast hP q) = D.ptDiag (h0 ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h0 q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h0
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h0) ⟨q.val - D.ptSize h0, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  set ρ := r - D.ptSize (h0 ++ [(n + 1, t)]) with hρ
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h0 ++ [(n + 1, t)]) γ =
      U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  unfold PBE.xs
  rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
  funext γ
  exact hS _ γ

theorem ccCoefM_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {e e' : ℝ} {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : JC.CCCoefM Bs A mm e F) (he : e' ≤ e) : JC.CCCoefM Bs A mm e' F :=
  ⟨h.1, h.2.1, fun g hg hne => le_trans he (h.2.2 g hg hne)⟩

theorem sliceContQa : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∀ (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreCont
  refine ⟨16 * Cp, by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hPt : ∀ t : ℂ, D.ptSize (h0 ++ [(n + 1, t)]) = i := fun t => by
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append]; exact hsz
  have hd0 : ∀ q, D.ptDiag h0 q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h0 hpb q q.2
  have e1 : r = D.ptSize h0 + (n + 1) + (r - i) := by omega
  have e2 : D.ptSize h0 + (n + 1) + (r - i) = r := by omega
  have hj1 : 1 ≤ D.ptSize h0 + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (D.ptSize h0 + (n + 1)) (r - i) Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) =
        D.uwG k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (D.ptSize h0 + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hsz.symm _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (D.ptSize h0 + (n + 1) + (r - i)), U.DjU k (D.ptSize h0 + (n + 1)) (r - i) g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (D.ptSize h0 + (n + 1) + (r - i)) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (D.ptSize h0 + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((D.ptSize h0 + (n + 1) + (r - i) : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast e2
  obtain ⟨ε', hε', hQ⟩ := hCp k (D.ptSize h0) n (r - i) Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h0) (D.ptDiag h0) t0 hd0 ht0 As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [e2]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hz1 : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z) = (T.bs i).z := by
    have hzl : T.base.z = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z) := (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  have hz1' : U.lowV k (D.ptSize h0 + (n + 1)) (r - i) (D.castV e1 T.base.z') = (T.bs i).z' := by
    have hzl' : T.base.z' = D.castV (by omega) (liftVec k i (r - i) (T.bs i).z') := (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hsz _ _
  refine ⟨ε', hε', fun hh c hsm hcl => ?_⟩
  obtain ⟨δ, Kb, Dd, hδ, hDd, hnear⟩ := hQ (D.castF e2 hh) c (PBE.ccle_castF e2 hcl) _ (hFrel hh hsm)
  have key : ∀ t : ℂ, t ≠ 0 → PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ :=
    fun t ht => xs_eq_phi T χ ε i hi w a h0 n t (hc t) hpb ht (hPt t) e1 e2 hh
  obtain ⟨-, -, hsupp0, -⟩ := hnear t0 (by rw [dist_self]; exact hδ)
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨htne, hB, hsupp, hD⟩ := hnear t ht
  have hsub : PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t)]) (hc t) hh a -
      PBE.xs T χ ε i hi w (h0 ++ [(n + 1, t0)]) (hc t0) hh a =
      fun γ => U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ -
        U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ := by
    rw [key t htne, key t0 ht0]; rfl
  rw [hsub, key t htne]
  refine ⟨htne, ⟨hB.1, ⟨_, hB⟩, fun γ hγ hne => ?_⟩, hB, ⟨hD.1, ⟨_, hD⟩, fun γ hγ hne => ?_⟩, hD⟩
  · have := hsupp γ hγ hne
    rwa [hz1, hz1'] at this
  · by_cases h1 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ = 0
    · have hne0 : U.PhiFun (p := D.ptSize h0 + (n + 1)) (s := 0) k (r - i) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h0))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h0) t0) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)) (fun a => a.elim0) γ ≠ 0 := by
        intro h2; apply hne; simp only [h1, h2, sub_zero]
      have := hsupp0 γ hγ hne0
      rwa [hz1, hz1'] at this
    · have := hsupp γ hγ h1
      rwa [hz1, hz1'] at this

theorem sliceContQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
    ∀ (h0 : C.LPt) (m : ℕ) (hc : ∀ t : ℂ, r - i = r - D.ptSize (h0 ++ [(m, t)])),
    (∀ b ∈ h0, 1 ≤ b.1 ∧ b.2 ≠ 0) → 1 ≤ m → D.ptSize h0 + m = i →
    ∀ t0 : ℂ, t0 ≠ 0 → ∃ ε' : ℝ, 0 < ε' ∧ ∀ (a : Wd.Ix (Fin w.length))
      (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a) Kb ∧
          JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε'
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) ∧
          B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N)
            (PBE.xs T χ ε i hi w (h0 ++ [(m, t)]) (hc t) h a - PBE.xs T χ ε i hi w (h0 ++ [(m, t0)]) (hc t0) h a) (Dd t) := by
  obtain ⟨Cs, hCs0, hCs⟩ := sliceContQa
  refine ⟨Cs, hCs0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0
  have H := fun a : Wd.Ix (Fin w.length) =>
    hCs Cc hCc k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw h0 m hc hpb hm hsz t0 ht0 a
  choose ef hef hP using H
  refine ⟨Finset.univ.inf' Finset.univ_nonempty ef,
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 (fun a _ => hef a), fun a hh c hsm hcl => ?_⟩
  have hle : Finset.univ.inf' Finset.univ_nonempty ef ≤ ef a := Finset.inf'_le _ (Finset.mem_univ a)
  obtain ⟨δ, Kb, Dd, hδ, hDd, hn⟩ := hP a hh c hsm hcl
  refine ⟨δ, Kb, Dd, hδ, hDd, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn t ht
  exact ⟨h1, ccCoefM_mono h2 hle, h3, ccCoefM_mono h4 hle, h5⟩

end Formalism.FourierDecayAlt.P.LastBlockContinuity
