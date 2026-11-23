import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def latVWS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, (∀ v ∈ S, evalV D.host.F v α = 0) ∧
    ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ L0c D V, ∃ y ∈ L0c D W,
      w = Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (if V.rank ≤ W.rank then a * star (x i) * y j else a * x i * star (y j))}

def UnramOutside (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D →
    (∀ v ∈ S, Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D (x : AE D)) = 1) →
    χ x = 1

def WeilUnramifiedCondition {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S, UnramOutside D (T.eChr χ) S → UnramOutside D (T.eChr χ') S →
    ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : X.Sch V W,
      (∀ u ∈ latVWS V W S, Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) = Wl.evS V W Φ) →
      Wl.om V W χ χ' (k, k') Φ = Φ

end Formalism.L2.Theta

end
