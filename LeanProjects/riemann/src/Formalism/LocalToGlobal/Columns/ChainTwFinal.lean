import Formalism.LocalToGlobal.Columns.ExistsNeZeroOfFirstUnfoldingNeZero
import Formalism.LocalToGlobal.Columns.ChainLawXiQF

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwFinal

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem characterNonvanishing_holds {G : ChGlob X R.m} {m2 : ℕ} (hm : R.m = m2 + 2) (hc : (twCst Ch sel mu G).Ok) :
    TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2 := by
  intro i hi P hP hd hal h hba _ hbb _ hint hne
  exact clXQ_chrOk_holds hc hP hd (by omega) (by rw [twCst_D_Q hP]; omega) hba hbb hint hne

theorem twIdx_ok_left (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (HL : UnfoldingNonvanishingLeftCoset Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 := by
  have hK := twCstQ_of hd hz hs hxi
  have hc := twCst_ok hPr hCh h4 hK
  have hsq : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → (twCst Ch sel mu G).sq P ≠ 0 := fun P hP => by
    rw [twCst_sq_Q hP]
    intro h0
    have h1 := hK.sq_sq P hP
    rw [h0, zero_pow two_ne_zero] at h1
    exact (show (qOf P.1 : X.K) ≠ 0 by exact_mod_cast (hd P hP).1.ne_zero) h1.symm
  exact twistedIndex_firstUnfolding_ok hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (doubleCoset_of_leftR1 hm hsq HL) (characterNonvanishing_holds hm hc)

end TwFinal

end Formalism.L2.Col
