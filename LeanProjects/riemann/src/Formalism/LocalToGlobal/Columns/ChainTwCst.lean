import Formalism.LocalToGlobal.Columns.ChainTwOk

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwCstL

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {G : ChGlob X R.m}

open Classical

theorem twCst_D_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).D P = 1 := if_pos hP
theorem twCst_D_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : (twCst Ch sel mu G).D P = 2 * R.m := if_neg hP
theorem twCst_psi_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).psi P = ciPsi Ch P := if_pos hP
theorem twCst_psi_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) :
    (twCst Ch sel mu G).psi P = twPsiQ G.σ₀ G.xi0 P.1 (2 * R.m) := if_neg hP
theorem twCst_sq_g {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) : (twCst Ch sel mu G).sq P = ciSq Ch P.1 := if_pos hP
theorem twCst_sq_Q {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) : (twCst Ch sel mu G).sq P = twSqrt P.1 := if_neg hP

theorem twCst_ok (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (hK : TwCstQ (Pr := Pr) sel mu G) :
    (twCst Ch sel mu G).Ok := by
  have hc := ciCst_ok (Ch := Ch) hPr hCh (SB := Pr.vGs) (fun _ h => h) h4 (mq := fun _ _ => 1)
  have h2 := R.two_le_m
  exact
    { psi_add := fun P x y hx hy => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_D_g hP] at hx hy
          rw [twCst_psi_g hP]
          exact hc.psi_add ⟨P.1, hP⟩ x y hx hy
        · rw [twCst_D_Q hP] at hx hy
          rw [twCst_psi_Q hP]
          exact hK.psi_add P hP x y hx hy
      psi_int := fun P x hx => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_psi_g hP]
          exact hc.psi_int ⟨P.1, hP⟩ x hx
        · rw [twCst_psi_Q hP]
          exact hK.psi_int P hP x hx
      psi_ne := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_psi_g hP]
          exact hc.psi_ne ⟨P.1, hP⟩
        · rw [twCst_psi_Q hP]
          exact hK.psi_ne P hP
      D_pos := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_D_g hP]
        · rw [twCst_D_Q hP]; omega
      sq_sq := fun P => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [twCst_sq_g hP]
          exact hc.sq_sq ⟨P.1, hP⟩
        · rw [twCst_sq_Q hP]
          exact hK.sq_sq P hP
      M_pos := by show 1 ≤ R.m; omega
      M_le_A := by show R.m ≤ R.m + 1; omega
      M_le_B := by show R.m ≤ R.m + 1; omega
      B_pos := by show 1 ≤ R.m + 1; omega }

theorem localConstants_psi_depth_one (hPr : Pr.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (a : X.E) (ha : IntAt P.1 a) :
    (twCst Ch sel mu G).psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a) := by
  rw [twCst_psi_g hP]
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr hP).ne_zero
  unfold ciPsi
  rw [mul_div_cancel₀ _ hq0, if_pos ha]

theorem twCst_weil (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : Ch.WeilTied G.σ₀ G.xi0) (hK : TwCstQ (Pr := Pr) sel mu G) :
    (twCst Ch sel mu G).WeilTied G.σ₀ G.xi0 := by
  intro P a b ha hab
  by_cases hP : P.1 ∈ Pr.vGs
  · have hw := ciCst_weil Ch hX hPr (SB := Pr.vGs) (fun _ h => h) (fun _ _ => 1) hW (fun P hP => (ookXiUnit hCh hW P hP).1)
    rw [twCst_D_g hP] at ha hab ⊢
    rw [twCst_psi_g hP]
    exact hw ⟨P.1, hP⟩ a b ha hab
  · rw [twCst_D_Q hP] at ha hab ⊢
    rw [twCst_psi_Q hP]
    exact hK.weil P hP a b ha hab

theorem twCst_base (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (hK : TwCstQ (Pr := Pr) sel mu G) {m2 : ℕ}
    (hm : R.m = m2 + 2) : OcbBase Ch sel mu (twCst Ch sel mu G) m2 where
  hX := hX
  hPr := hPr
  hCh := hCh
  hm := hm
  cst_ok := twCst_ok hPr hCh h4 hK
  sharp := rfl
  psi0 P a hP ha := localConstants_psi_depth_one hPr P hP a ha
  depthG _ hP := twCst_D_g hP

end TwCstL

end Formalism.L2.Col
