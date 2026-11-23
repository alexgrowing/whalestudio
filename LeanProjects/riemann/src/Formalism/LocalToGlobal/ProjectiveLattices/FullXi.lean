import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def cjFin (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  Units.map (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.conjF).toRingHom.toMonoidHom

def XiTilde (xi δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) : Prop := ∀ x, xi (x / cjFin D x) = δ x

def FullExists2 (D : D7) (pb : Fin 2 → IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) (chi₀ : ℕ → (AE D)ˣ →* Circle)
    (δ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (I : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ T : Full D, LawsFull T ∧ T.pb = pb ∧ (∀ j, T.chiW j T.σ₀ = chi₀ j) ∧ XiTilde T.xi δ ∧ T.half₂ = I

end Formalism.L2.Pj
