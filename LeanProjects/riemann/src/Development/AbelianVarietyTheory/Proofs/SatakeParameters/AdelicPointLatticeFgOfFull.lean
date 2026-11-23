import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

open NumberField IsDedekindDomain Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

namespace GlobalTheory.LatAdFG

theorem latAd_eq_globLat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latAd x Lb = Formalism.UG.CS.globLat x Lb := by
  unfold latAd
  exact Submodule.span_eq (Formalism.UG.CS.globLat x Lb)

theorem latAd_fg_of_full : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → ∀ (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (latAd x Lb).FG := by
  intro F E _ _ _ _ _ N Lb hfin hspan x
  rw [latAd_eq_globLat]
  exact (Formalism.UG.P.global_lattice_isLattice_holds F E (Fin N) Lb hfin hspan x).fg

end GlobalTheory.LatAdFG
