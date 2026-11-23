import Formalism.LocalToGlobal.Columns.UnfoldingPhiCompLeftUnipotentSource
import Formalism.LocalToGlobal.Columns.FreePointColumnFormula

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

theorem clS_card {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem clS_covS : TruncatedUnfoldingChangeOfVarsSource := by
  intro E _ _ _ P K _ n' c' n c hc hp hu psi D a b e hadd hint Ψ hsupp haD hinv r hr g hg hx hre _ heD A B hA hB _ wt y
  subst hc
  exact clS_cov (ciQ_mem P) hu hp (clS_card P) psi D a b e hadd hint Ψ hsupp haD hinv hr hg hx hre heD A B hA hB wt y

section Close

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_xiLawQ_ofT {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ} (hCT : TruncatedUnfoldingChangeOfVarsTarget)
    (hok : L.Ok Ch sel mu cst G m2) (hd : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → TwDegOne X w.1)
    (hb : ∀ j (b : L.β j) (w : rowSG Pr sel mu), w.1 ∉ Pr.vGs → TwBdd (Pr := Pr) j w.1 (L.h j b w))
    (hD : ∀ w : rowSG Pr sel mu, w.1 ∉ Pr.vGs → m2 ≤ cst.D w) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) :
    XiLawQ Ch sel mu cst L i al be :=
  clXQ_xiLawQ_of hCT clS_covS hok hd hb hD hi al be

end Close

end Formalism.L2.Col
