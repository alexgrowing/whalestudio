import Formalism.LocalToGlobal.Columns.XiFirstLawAllLevels
import Formalism.LocalToGlobal.Columns.ChainLawPhiPf
import Formalism.LocalToGlobal.Columns.ChainLawXi
import Formalism.LocalToGlobal.Columns.ChainLawXiTgt

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Final

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem clX_phiHyp {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) {i : ℕ} (hi : i < m2) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    PhiGSLawHyp P.1 (qOf P.1) R.k R.rS R.r R.t (i + 1) (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) := by
  obtain ⟨hk0, hr0, hN0, ht0⟩ := ranks_frame_inequalities R hB.hm (j := i) (by omega)
  obtain ⟨hk1, -, hN1, -⟩ := ranks_frame_inequalities R hB.hm (j := i + 1) (by omega)
  exact ⟨ciQ_mem P.1, ciQ_notMem_sq hB.hX hB.hPr hP, by omega, hk0, hk1, hr0, ht0, by rw [Nat.add_sub_cancel]; exact hN0.symm,
    hN1.symm⟩

theorem clX_phiLaw_steps {m2 : ℕ} (hB : OcbBase Ch sel mu cst m2) :
    ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → PhiGSLaw P.1 (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (i + 1)
      (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) :=
  fun _ hi P hP => clPf_phiGSLaw (clX_phiHyp hB hi P hP) _ _

end Final

end Formalism.L2.Col
