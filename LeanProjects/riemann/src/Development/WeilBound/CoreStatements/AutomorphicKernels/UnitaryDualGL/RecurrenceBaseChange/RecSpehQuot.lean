import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.UdReth

def TempCsd (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (a : ℕ) (P : CuspSub E a), 1 ≤ a → P.IsCsd →
    (∀ τ : E →+* ℂ, ∃ m : Multiset ℂ, P.HasInfChar τ m ∧ m.Nodup) →
    (∃ f : ℂ, ∀ τ m, P.HasInfChar τ m → ∀ z ∈ m, ∃ k : ℤ, z = f + k) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
      IsTemperedGL σ.ρ

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def RecSpehT (rc : RecMap A) : Prop :=
  ∀ (w : PlE H) (a d n : ℕ) (h : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
    IsTemperedGL σ.ρ → IsSpehQuot h σ σ' →
    rc w n σ' = lpSumList ((List.range d).map fun k : ℕ => A.lpTw (rc w a σ) (((d : ℝ) - 1) / 2 - k))

end PositivityTheory.UdReth

end
