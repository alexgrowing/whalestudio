import Mathlib
import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LvSite

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}

set_option maxHeartbeats 4000000 in

def StepTiesD {i : ℕ} (hi : i + 1 ≤ D.R.m) (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (c : LatCmp D) : Prop :=
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)),
    x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F) →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) →
    x ∈ ulocOf Fo β w') ∧
  (∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F)), x ∈ ulocOf Fo β w' →
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F) ∧
    (∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) :
        Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈ w'.adicCompletionIntegers D.host.F)) ∧
  (∀ w' ∈ Fo.bad, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal) ∧
  cT (sigD D : D.host.E →+* D.host.E) (reGL (rankN D (i + 1) hi) D.host.E S.B).1 * gramN D (i + 1) hi *
    (reGL (rankN D (i + 1) hi) D.host.E S.B).1 = 1 ∧
  (∀ β, UnitCharacterChartCompatibility hi (Fo.K β).lev (c.embW u w hg) (S.ψ β)) ∧
  (∀ β cl, ∃ r : D.what₂.LL, D.what₂.embLL r = ((Fo.tw β).ch ((Fo.K β).y cl) : ℂ)) ∧
  Fo.okW w ∧
  ¬ D.what₂.places.resChar w ∣ Fo.T

end GlobalTheory.Mem.Top.KerOne.CertEq

end
