import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwNormLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne
import Formalism.LocalToGlobal.Columns.ChainTwAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwAux

theorem twNormRep {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (hd : TwDegOne X P) (h : AutY X R j) (hb : TwBdd (Pr := Pr) j P h) :
    ∃ h', SameDC (Pr := Pr) sharp j P h h' ∧ TwBdd (Pr := Pr) j P h' ∧ TwNF (Pr := Pr) j P h' ∧
      prCat (Pr := Pr) sharp j P h' ≤ GLint X.E (R.N j) P := by
  have hL : lamYat (Pr := Pr) (R := R) j P = LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    unfold lamYat; rw [if_neg hP]
  have hJ : Jat (Pr := Pr) (R := R) sharp j P = LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hb0 : PI.TwNormLat.Bdd P (R.N j) (cOf R j) j h := by
    intro x hx
    have := hb x (by rw [hL]; exact hx)
    rw [hL] at this
    exact this
  obtain ⟨r, hr, κ, hκ, hb', hnf, hpr⟩ := _root_.TwNormLat X.E P (R.N j) (cOf R j) (R.k + j) j hd.1 hd.2 h hb0
  refine ⟨r * h * κ, ⟨r, hr, κ, by rw [hJ]; exact hκ, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    rw [hL] at hx ⊢
    exact hb' x hx
  · obtain ⟨n, z, hn, hz, hv⟩ := hnf
    refine ⟨n, z, hn, hz, fun v => ?_⟩
    rw [hL]
    exact hv v
  · unfold prCat
    rw [hJ]
    exact hpr

theorem twChrOk_one {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hpsi : ∀ x, IntAt P.1 x → cst.psi P x = 1) : TwChrOk Ch sel mu cst j P 1 := by
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp j P.1 = LocE.JQ P.1 (qOf P.1) (R.k + j) (R.N j) (cOf R j) := by
    unfold Jat; rw [if_neg hP]
  have hchi : ∀ r, chiInv Ch sel mu cst j P 1 r =
      PI.TwChrOne.ChiL P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) 1 r := by
    intro r
    unfold chiInv lamRow
    rw [if_neg hP]
    rfl
  obtain ⟨h1, h2⟩ := _root_.TwChrOne X.E X.K P.1 (cst.psi P) (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + j) (R.N j) (cOf R j) hpsi
  refine ⟨fun r hr => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · rw [hchi]
    rw [hJ] at hr
    exact h1 r hr
  · rw [hchi, hchi, hchi]
    rw [hJ] at hr hr' hr''
    exact h2 r hr r' hr' r'' hr'' hx

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def UnfoldingNonvanishingDoubleCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h h' : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h → TwBdd (Pr := Pr) (i + 1) P.1 h' →
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h'

def TwChrNFQ (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)),
    TwBdd (Pr := Pr) i P.1 hal → TwNF (Pr := Pr) i P.1 hal →
    TwBdd (Pr := Pr) (i + 1) P.1 h → TwNF (Pr := Pr) (i + 1) P.1 h → prCat (Pr := Pr) cst.sharp (i + 1) P.1 h ≤ GLint X.E (R.N (i + 1)) P.1 →
      FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → TwChrOk Ch sel mu cst (i + 1) P h

variable {Ch sel mu cst}

theorem twNormDC_of {m2 : ℕ} (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu cst m2) : TwNormDC Ch sel mu cst m2 := by
  intro i hi P hP hdeg hal h hbal _ hb hne
  obtain ⟨h', hs, hb', hnf, hpr⟩ := twNormRep (Pr := Pr) cst.sharp (i + 1) hP hdeg h hb
  exact ⟨h', hs, hb', hnf, hpr, HE i hi P hP hdeg hal h h' hbal hb hb' hs hne⟩

theorem twChrQ_of {m2 : ℕ} (HF : TwChrNFQ Ch sel mu cst m2) (hpsi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∀ x, IntAt P.1 x → cst.psi P x = 1) :
    TwChrQ Ch sel mu cst m2 :=
  ⟨HF, fun P hP _ => twChrOk_one Ch sel mu cst (m2 + 1) P hP (hpsi P hP)⟩

theorem twistedIndex_firstUnfolding_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X R.m)
    {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E} (hT : Ch.Tied G.σ₀ e G.mu0 eta) (hW : Ch.WeilTied G.σ₀ G.xi0)
    (hval : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    {m2 : ℕ} (hm : R.m = m2 + 2) (hQG : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs)
    (hd : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1)
    (hz : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs →
      ∃ z : X.K, G.σ₀ z = Complex.exp (2 * Real.pi * Complex.I / ((qOf P.1 ^ (2 * R.m) : ℕ) : ℂ)))
    (hs : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ z : X.K, z ^ 2 = (qOf P.1 : X.K))
    (hxi : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → IntAt P.1 G.xi0 ∧ redP P.1 G.xi0 ≠ 0)
    (HE : UnfoldingNonvanishingDoubleCoset Ch sel mu (twCst Ch sel mu G) m2) (HF : TwChrNFQ Ch sel mu (twCst Ch sel mu G) m2) :
    (twIdx Ch sel mu (twCst Ch sel mu G) m2).Ok Ch sel mu (twCst Ch sel mu G) G m2 :=
  twIdx_ok_full hX hPr hCh h4 G hT hW hval hm hQG hd hz hs hxi (twNormDC_of HE)
    (twChrQ_of HF fun P hP x hx => (twCst_ok hPr hCh h4 (twCstQ_of hd hz hs hxi)).psi_int P x hx)

end TwAux

end Formalism.L2.Col
