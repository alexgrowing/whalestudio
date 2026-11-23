import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6.Lev0

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lev0Q {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (0 + ρ) + k + 1) → ℂ) (χ : ℝ → ℝ) (hχ : C6.IsCut0 χ) (ε : ℝ) (hε : 0 < ε)
    (A₀ A : ℝ) (mm : ℕ) (hA : A + 2 * (((0 + ρ : ℕ) : ℝ) + 1) * (mm : ℝ) ≤ A₀) :
    ∃ ε' C : ℝ, 0 < ε' ∧ 0 ≤ C ∧ ∀ (f : B.Mat k (0 + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm f c →
      B.CCle A mm (fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g) (C * c) ∧
      ∀ g ∈ B.GV k (0 + ρ), ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g ≠ 0 → ε' ≤ Gf k (0 + ρ) z z' g := by
  obtain ⟨δ, hδ, hG, hsupp⟩ := isCutG_div hχ hε
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k 0 ρ Wp Wq z z' 0 0 (idOp k (0 + ρ) Wp Wq) bumpOne
    (fun x => χ (x / ε)) (δ * ε) (inDD_idOp k ρ Wp Wq) isCutC_bumpOne hG mm mm A₀ (by simp)
  refine ⟨δ * ε, max C 0, by positivity, le_max_right _ _, fun f c hc => ?_⟩
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hS := hC f c hc
  have hF : B.opApply (idOp k (0 + ρ) Wp Wq) (U.cutDG k 0 ρ z z' bumpOne (fun x => χ (x / ε)) f) =
      fun g => ((χ (Gf k (0 + ρ) z z' g / ε) : ℝ) : ℂ) • f g := by
    rw [opApply_idOp]
    funext g
    simp [U.cutDG, U.DjU, bumpOne_one]
  rw [hF] at hS
  obtain ⟨hck, -, hbd⟩ := hS
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.compactly_supported_monotone k (0 + ρ) _
      (A₀ - ((0 : ℕ) : ℝ) - ((0 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) - 2 * (((0 + ρ : ℕ) : ℝ) + 1) * ((mm + 0 : ℕ) : ℝ))
      A (C * c) mm _ ?_ ⟨hck, ?_⟩) (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0), ?_⟩
  · push_cast at hA ⊢; linarith
  · intro u v hu hv hl g hg
    refine hbd u v ?_ ?_ hl g hg
    · intro X hX; exact ⟨⟨(hu X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hu X hX).2⟩
    · intro X hX; exact ⟨⟨(hv X hX).1, fun i b hb => absurd hb (Nat.not_lt_zero _)⟩, (hv X hX).2⟩
  · intro g hg hne
    have h1 : χ (Gf k (0 + ρ) z z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [h0]
    have h2 := hsupp _ h1
    rw [le_div_iff₀ hε] at h2
    linarith

def xs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (ε : ℝ) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) (p : C.LPt) (hc : r - i = r - D.ptSize p) (h : B.Mat k r → (Wq →L[ℂ] Wp))
    (a : Wd.Ix (Fin w.length)) : B.Mat k (r - i) → (Wq →L[ℂ] Wp) :=
  D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ h ε) i hi w a) p)

theorem sliceQ : ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ Cc : ℝ, Cs ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (a : Wd.Ix (Fin w.length)),
      ∃ ε' K : ℝ, 0 < ε' ∧ 0 ≤ K ∧
      (∀ (h : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) h →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h c →
        JC.CCCoefM (T.bs i) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε' (xs T χ ε i hi w p hc h a) ∧
        B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xs T χ ε i hi w p hc h a) (K * c)) ∧
      ∀ (h₁ h₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV k r) h₁ → B.CkOn ⊤ (B.GV k r) h₂ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₁ c₁ →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) h₂ c₂ →
        ∀ γ ∈ B.GV k (r - i), xs T χ ε i hi w p hc h₁ a γ - xs T χ ε i hi w p hc h₂ a γ =
          xs T χ ε i hi w p hc (fun g => h₁ g - h₂ g) a γ := by
  obtain ⟨Cp, hCp0, hL⟩ := levQ
  refine ⟨max 150 (16 * Cp), by positivity, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi w hw p hc hp a
  rcases Nat.eq_zero_or_pos i with h0 | h1
  · subst h0
    obtain rfl : p = [] := by
      cases p with
      | nil => rfl
      | cons b p =>
        exfalso
        have h1 := (hp.1 b (by simp)).1
        have h2 := hp.2
        simp [D.ptSize] at h2
        omega
    have hfun : ∀ h : B.Mat k r → (Wq →L[ℂ] Wp), xs T χ ε 0 hi w [] hc h a =
        (if a = Wd.e1 then D.cutF T.base χ h ε else 0) := by
      intro h
      funext γ
      have hcm : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by
        ext i j; rfl
      simp only [xs, D.castF]
      rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
    obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
    have hb := Formalism.FourierDecayAlt.P.JCTx6.Link.budget0 (0 + ρ) k N hk2 A₀ Cc (le_trans (le_max_left _ _) hCc) hA₀
    obtain ⟨ε', C, hε', hC0, hQ⟩ := lev0Q (Wp := Wp) (Wq := Wq) T.base.z T.base.z' χ hχ ε hε A₀ (P5.Auser P0 N + 1) (P5.mmUser P0 N) (by
        simp only [P5.Auser, P5.mmUser, P5.nV, hPk, hPr]
        push_cast
        push_cast at hb
        linarith)
    have hmmM : P5.mmUser P0 N ≤ 3 * (11 * (N * (2 * (0 + ρ) + k + 1) ^ 2 + (2 * (0 + ρ) + k + 1) ^ 3) + 5) := by
      obtain ⟨-, -, b3, -, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs (0 + ρ) k N 0 0 hk2 (Nat.zero_le _) (Nat.zero_le _)
      have : P5.mmUser P0 N = 5 + 3 * ((0 + ρ) + 1) * (N + 2) * (2 * (0 + ρ) + k + 1) + N * (0 + ρ) := by
        simp only [P5.mmUser, P5.nV, hPk, hPr]
      omega
    refine ⟨ε', C, hε', hC0, ?_, ?_⟩
    · intro h c _ hcl
      have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hcl
      rw [hfun h]
      by_cases ha : a = Wd.e1
      · rw [if_pos ha]
        obtain ⟨q1, q2⟩ := hQ h c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmmM hcl)
        exact ⟨⟨q1.1, ⟨_, q1⟩, q2⟩, q1⟩
      · rw [if_neg ha]
        have hz : B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (0 : B.Mat k (0 + ρ - 0) → (Wq →L[ℂ] Wp)) (C * c) :=
          Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (mul_nonneg hC0 hc0)
        exact ⟨⟨hz.1, ⟨_, hz⟩, fun g _ hne => (hne rfl).elim⟩, hz⟩
    · intro h₁ h₂ c₁ c₂ _ _ _ _ γ _
      rw [hfun h₁, hfun h₂, hfun (fun g => h₁ g - h₂ g)]
      by_cases ha : a = Wd.e1
      · simp only [if_pos ha, D.cutF, smul_sub]
      · simp only [if_neg ha, Pi.zero_apply, sub_zero]
  · obtain ⟨ε', K, hε', hK, hQ1, hQ2⟩ := hL Cc (le_trans (le_max_right _ _) hCc) k r Wp Wq T χ A₀ N P0 hPk hPr hk2 hχ
      hA₀ ε hε i hi h1 w hw p hc hp a
    exact ⟨ε', K, hε', hK, hQ1, hQ2⟩

theorem auser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.Auser P0 L ≤ P5.Auser P0 N := by
  unfold P5.Auser
  have : (L : ℝ) ≤ N := by exact_mod_cast h
  gcongr

theorem mmUser_mono (P0 : M.Par) {L N : ℕ} (h : L ≤ N) : P5.mmUser P0 L ≤ P5.mmUser P0 N := by
  unfold P5.mmUser
  gcongr

theorem formLev_limit {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := Formalism.FourierDecayAlt.P.level_form_sesquilinear_moderate Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

end Formalism.FourierDecayAlt.P.PBE
