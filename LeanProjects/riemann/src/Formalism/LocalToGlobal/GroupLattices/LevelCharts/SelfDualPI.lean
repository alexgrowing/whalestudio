import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitStab
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SelfDualLoc

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.G

theorem self_dual_lattice_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ) (hfin : Module.Finite (𝓞 E) Lb)
    (hint : ∀ x ∈ Lb, ∀ y ∈ Lb, Formalism.UG.hform (σ : E →+* E) J x y ∈ Formalism.UG.intOE E)
    (hdual : ∀ y : Fin n → E, (∀ x ∈ Lb, Formalism.UG.hform (σ : E →+* E) J x y ∈ Formalism.UG.intOE E) → (T : E) • y ∈ Lb)
    (hT : (T : 𝓞 F) ∉ v.asIdeal) : SelfDualAt σ J v Lb :=
  self_dual_local F E n σ J v Lb T hfin hint hdual hT

end Formalism.L2.G
