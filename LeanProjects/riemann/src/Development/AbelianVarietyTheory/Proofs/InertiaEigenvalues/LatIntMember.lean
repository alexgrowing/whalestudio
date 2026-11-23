import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty

theorem latInt_member : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, Built A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
