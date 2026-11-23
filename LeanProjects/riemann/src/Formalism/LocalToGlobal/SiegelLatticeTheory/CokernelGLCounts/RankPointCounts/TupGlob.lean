import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def IntFr (U : PairVal.MatR D) : Prop :=
  ∀ c b : Fin (D.R.rS + 1), c < b → ∀ x ∈ FibQ.aaF D b, x * U c b ∈ FibQ.aaF D c

def TieG (U U' : PairVal.MatR D) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ c b : Fin (D.R.rS + 1),
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * (U c b - U' c b) = ((Lat.gS D : ℕ) : D.host.E) * o

variable (D) in

def GlobMove (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ Z₂ : PairVal.MatR D), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    AtMat w Z₁ → AtMat w Z₂ → (∀ p, tupZ M δ u u' Z₁ p = tupZ M δ u u' Z₂ p) →
    ∃ U U' : PairVal.MatR D, IsUpUni U ∧ IsUpUni U' ∧ IntFr U ∧ IntFr U' ∧ TieG U U' ∧ Z₂ = U.conjTranspose * Z₁ * U'

end Formalism.L2.SG.Pf.TupGlob
