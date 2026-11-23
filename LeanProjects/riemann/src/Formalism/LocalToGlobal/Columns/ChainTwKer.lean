import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Formalism.LocalToGlobal.Columns.ChainLawXiQF
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TwKer

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem kerEquivC_tw (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (A : Amb X) (u : Pr.Word)
    (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (hST : Pr.T u ∈ S)
    (hOk : ChTh.Ok (Ch := Ch) (twCst Ch sel mu G) (chTh W Ch sel mu (twCst Ch sel mu G) A u m2))
    (b : (twIdx Ch sel mu (twCst Ch sel mu G) m2).β (m2 + 1))
    (hY : YbHyp (R := R) sel mu (twCst Ch sel mu G) (twIdx Ch sel mu (twCst Ch sel mu G) m2) u m2 b) :
    KerEquivC W Ch sel mu (twCst Ch sel mu G) (twIdx Ch sel mu (twCst Ch sel mu G) m2) A u m2 b hY (rPsymF Ch) := by
  have hL := twIdx_ok_closed hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi
  have hK := twCstQ_of hd hz hs hxi
  have hNall := twNormAt_all (Ch := Ch) (twNormDC_of (Ch := Ch) (unfoldingNonvanishingDoubleCoset_holds (Ch := Ch) G hm hK)) hd
  have hb : ∀ j (b' : (twIdx Ch sel mu (twCst Ch sel mu G) m2).β j) (w : rowSG Pr sel mu), w.1 ∉ Pr.vGs →
      TwBdd (Pr := Pr) j w.1 ((twIdx Ch sel mu (twCst Ch sel mu G) m2).h j b' w) :=
    fun j b' w hw => twSt_bdd hNall j b' w hw
  have hD : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → m2 ≤ (twCst Ch sel mu G).D w := fun w hw => by
    rw [twCst_D_Q hw]
    omega
  exact kerEquivC_repOne W Ch sel mu (twCst Ch sel mu G) (twIdx Ch sel mu (twCst Ch sel mu G) m2) A u m2 hL hX hPr hCh hsel hS hST
    rfl (by show R.m ≤ R.m + 1; omega) (fun j _ b' P hP => twIdx_h_g (Ch := Ch) (cst := twCst Ch sel mu G) (m2 := m2) hP) hOk b hY
    (fun i hi al be => clXQ_xiLawQ_holds hL hd hb hD hi al be)

end TwKer

end Formalism.L2.Col
