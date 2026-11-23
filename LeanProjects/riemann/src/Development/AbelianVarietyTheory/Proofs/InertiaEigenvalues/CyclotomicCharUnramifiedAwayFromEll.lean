import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CycUnram

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  intro D i v hv γ hγ
  have hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by simpa [placesOver] using hv
  have h1 : cycZ D.host.E D.nd.Om (D.nd.l i) γ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hl (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hγ.2 x hx) n]
    simp
  have h2 : epsU D.nd i γ = 1 := by
    unfold epsU Glob.epsO
    rw [MonoidHom.comp_apply, h1, map_one]
  refine ⟨h2, fun c hc1 hc2 => ?_⟩
  change D.nd.chi i c γ = D.nd.chi i 1 γ
  rw [D.nd.chi_def i c hc1 hc2, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, h1, map_one,
    one_zpow, mul_one]

end GlobalTheory.CycUnram
