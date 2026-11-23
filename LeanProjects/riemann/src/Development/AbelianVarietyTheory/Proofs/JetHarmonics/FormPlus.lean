import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

namespace GlobalTheory.ShortMove

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

def Marked {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D) {r : ℕ} (hr : V.rank = r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (l : Level H)
    (Λ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (mk : Dw.La → (Fin r → D.host.E)) (h : GA D V) : Prop :=
  (Λ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V h : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∃ w ∈ latGHat V h, finVec V (mk a ∘ Fin.cast hr) - (finHom V h).1.mulVec (finVec V (io a)) = (l.M : ℕ) • w

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

def FormPlus {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (V : HSp D)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) : Prop :=
  ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
    Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y)))

end GlobalTheory.ShortMove
