import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatTied

theorem latStable_tied : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)),
    (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) →
    ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  intro D M Tn Q hQ hI j w h1 h2 hw
  classical
  by_cases hne : (D.nd.locs j w).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hwi : D.nd.w i = w := ((D.nd.locs_mem j w i).1 hi).2
    have hQc : Tn.B.Qc j w = Q w := by rw [← Tn.Q_eq j w i hi, hQ i, hwi]
    apply GlobalTheory.T.heckeStableLocalLattice_of_integral D M Tn.B j h1 h2 w
    rw [hQc]; exact hI j h1 h2 w hw
  · have hsub : Subsingleton (heckeAlg Tn.B j w) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨I, hI'⟩ := Ideal.exists_maximal (heckeAlg Tn.B j w)
      obtain ⟨i, hi, -⟩ := Tn.mx_all j w h1 h2 hw I hI'
      exact hne ⟨i, hi⟩
    have h10 : (1 : Module.End (FractionRing (Tn.B.Oc j w)) (Tn.B.V j w)) = 0 := by
      have := congrArg Subtype.val (Subsingleton.elim (1 : heckeAlg Tn.B j w) 0)
      simpa using this
    have hx : ∀ y : Tn.B.V j w, y = 0 := fun y => by
      have := LinearMap.congr_fun h10 y
      simpa using this
    intro v k _ x _
    rw [hx (Tn.B.hK j w v k x)]
    exact Submodule.zero_mem _

end GlobalTheory.LatTied

end
