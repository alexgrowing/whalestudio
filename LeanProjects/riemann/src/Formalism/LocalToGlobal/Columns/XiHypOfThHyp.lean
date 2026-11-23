import Formalism.LocalToGlobal.Columns.KernelEquivTrivialTuple

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Hyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {hQ : QE sel (mu : Chr X.F X.E X.K) = ∅} {m2 : ℕ} {al : ∀ j, j ≤ m2 + 1 → L.β j} {Am : Amb X} {u : Pr.Word}

theorem xiHyp_of_thHyp {σ₀ : X.K →+* ℂ} {G : ChainGlob W σ₀} (hm : R.m = m2 + 2) (hσ : Am.σ₀ = σ₀) (hPr : Pr.Ok)
    (hTh : ThHyp W Ch sel mu cst Am u m2)
    (hχ : ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
      Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') ≠ 0)
    (hρ : RhoScal W Λ Ch sel mu cst G Am u) :
    XiHyp W Λ Ch sel mu cst Am u (refXi1 Ch sel mu cst L hQ m2 al u) G := by
  have hA : ∀ i, i < R.m → Am.AnaStep (R.N i) (R.N (i + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) := by
    intro i hi
    rcases Nat.lt_or_ge m2 i with h | h
    · have e : i = m2 + 1 := by omega
      subst e
      have h2 := hTh.2.1
      rw [hm] at h2
      exact h2
    · exact hTh.1 i h
  exact
    { sig := hσ
      T_pos := (hPr.T_prime u).pos
      smooth := fun i hi => (hA i hi).2.1
      rat := fun i hi => (hA i hi).2.2
      chi_ne := hχ
      rho := hρ
      above := fun i hi p p' x => refXi1_above Ch sel mu cst L hQ m2 al u hm i hi p p' x }

end Hyp

end Formalism.L2.Col
