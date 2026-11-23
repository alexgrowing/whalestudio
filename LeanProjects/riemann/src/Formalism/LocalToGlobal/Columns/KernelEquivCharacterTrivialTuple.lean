import Formalism.LocalToGlobal.Columns.KerRefArgDUnf
import Formalism.LocalToGlobal.Columns.ChainLawPhiTop
import Formalism.LocalToGlobal.Columns.ChainTwKer
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkEqcar
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkVolLaHyp

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Car

variable {D : Formalism.L2.Ker.Car} {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (s : Cd.Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ) (χ : Cd.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) {m2 : ℕ}

structure CarNum : Prop where
  hS : (∀ l ∈ D.host.small, l ∈ S) ∧ D.host.q ∈ S ∧ D.host.d ∈ S ∧ Pr.T u ∈ S ∧ (∀ i, Pr.g i ∈ S)
  hSc : ∀ p : ℕ, p.Prime → p ∣ Ideal.absNorm cc → p ∈ S
  hT : Pr.T u ∉ D.host.small ∧ Pr.T u ≠ D.host.q ∧ Pr.T u ≠ D.host.d ∧ (Pr.T u).Coprime (Ideal.absNorm cc)
  hg : ∀ i, Pr.g i ∉ D.host.small ∧ Pr.g i ≠ D.host.q ∧ Pr.g i ≠ D.host.d ∧ (Pr.g i).Coprime (Ideal.absNorm cc)

variable {W Ch sel mu}

end Car

end Formalism.L2.Col
