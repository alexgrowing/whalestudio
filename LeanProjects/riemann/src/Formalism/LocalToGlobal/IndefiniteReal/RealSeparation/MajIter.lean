import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.UnfDefs
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.BesPerSt
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def MajIter (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau →
    ∀ (ρ : ℕ) (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E) (T0 : HSp D)
      (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E), IsQuotFrame T C C' T0 B0 →
    ∀ (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
      IsQuotFrame S CS CS' S0 BS →
    ∀ (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D ρ S.rank) 𝓕 μ →
    ∀ (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)), μS.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T0.rank ρ) 𝓕S μS →
    ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
      ∃ (N : ℕ) (c : ℝ), ∀ k ∈ K, ∀ k' ∈ K', ∀ a ∈ GinfC S, ∀ b' ∈ GinfC T,
        Summable (fun q : Matrix (Fin ρ) (Fin S.rank) D.host.E × Matrix (Fin T0.rank) (Fin ρ) D.host.E =>
          ‖RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 (om (a * k, b' * k') f)
            (embI S T C' (q.1.map (incA D)) + embI S T B0 x0)) (embP S T0 CS' (q.2.map (incA D)))‖) ∧
        ∑' q : Matrix (Fin ρ) (Fin S.rank) D.host.E × Matrix (Fin T0.rank) (Fin ρ) D.host.E,
          ‖RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 (om (a * k, b' * k') f)
            (embI S T C' (q.1.map (incA D)) + embI S T B0 x0)) (embP S T0 CS' (q.2.map (incA D)))‖ ≤
          c * (normInf θ S a * normInf θ T b') ^ N

end Formalism.IndefR.Mi

end
