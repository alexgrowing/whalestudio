import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Full (D : D7) : Type 1 extends Top D where
  cE : ∀ (j : ℕ) (σ : Q.c.F →+* ℂ), (U j σ).Comp → ℂ
  chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle
  x₀ : ℕ → (Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ
  iota : ∀ j : ℕ, (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)
  xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ
  half₂ : Ideal (𝓞 D.host.E)

variable {D : D7}

def Full.J (T : Full D) : CoreJ D :=
  { toCore := T.toTop.toCore, cE := T.cE, chiW := T.chiW, x₀ := T.x₀, iota := T.iota }

def Full.XiVal (T : Full D) (j n : ℕ) : Prop :=
  ∃ (hr : (T.V j T.σ₀).rank = D.R.r) (U₂ : _) (dict₂ : _),
    CXiVal (T.V j T.σ₀) hr T.σ₀ (Tup := Unit) (fun _ => T.dδ j n) U₂ dict₂
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) (T.x₀ j T.σ₀) fun _ => T.xi

structure LawsFull (T : Full D) : Prop where
  p : LawsP T.toTop
  j : LawsJ T.J
  sh : LawsSh T.toTop

  canon : T.Q.Canon

  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1

  halfI : ∀ j, InR D j → ∀ n, (T.dδ j n).I = T.half₂

  shUniq : ∀ j, InR D j → ∀ n (_ : StarRing (𝓞 D.host.E)) (nab' : NabV (T.dδ j n).Xo₂ (T.dδ j n).c₂),
    IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ nab' → ∀ a, Dom a n →
      shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n { T.dδ j n with nab₂ := nab' } =
        shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n)

  xiVal : ∀ j, InR D j → ∀ n, T.XiVal j n

def FullExists (D : D7) (pb : Fin 2 → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (chi₀ : ℕ → (AE D)ˣ →* Circle)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (I : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ T : Full D, LawsFull T ∧ T.pb = pb ∧ (∀ j, T.chiW j T.σ₀ = chi₀ j) ∧ T.xi = xi ∧ T.half₂ = I

end Formalism.L2.Pj
