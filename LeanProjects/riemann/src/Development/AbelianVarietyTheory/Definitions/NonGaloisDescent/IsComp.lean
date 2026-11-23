import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesConjOfAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

namespace GlobalTheory.TypeRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance factG (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

structure Ident (D : D7) where
  i : ∀ (k : Fin 2) (v : D.nd.PlG k), ℚ_[D.host.g k] ≃+* (D.naut.plGw k v).adicCompletion D.host.E
  cont : ∀ k v, Continuous (i k v)

def pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) :
    Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]) :=
  Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom))

def IsRc (hL : GlobalTheory.Published.LocalLanglandsGL) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D)
    (rc : GlobalTheory.SerSys.Corr D) : Prop :=
  ∀ k v n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])), Nonempty (π ≅ pull I k v σ) →
    T.e _ (rc k v n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)

def IsComp {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (cp : GlobalTheory.GoodTypes.Comp D) : Prop :=
  ∀ σ k v, ∃ (s : SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ cp σ k v = pull I k v τ

end GlobalTheory.TypeRec

end
