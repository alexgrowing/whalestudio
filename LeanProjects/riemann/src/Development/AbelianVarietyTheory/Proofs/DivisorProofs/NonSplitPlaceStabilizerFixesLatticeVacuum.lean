import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramified

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem nonSplit_fixes_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (H : Geo.Tor.Host D.host.E) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f, IsThetaFunO ψ V W f → IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f → ∀ v ε (k : GA D W), GlobalTheory.WeilParts.NonSplitAt D v ε → GlobalTheory.WeilParts.SuppPl ε W k → (∀ u, u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) ↔ actO V W 1 k u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True)) → om (1, k) f = f ∧ (V.rank ≠ 0 → mu k = 1) := by
  intro D ψ θ V W χV χW om hP mu hmu _ ΛV ΛW hV hW f hf hvac v ε k hv hk hst
  obtain ⟨uV, uW⟩ := hP.unr v ε hv
  refine ⟨?_, fun _ => ?_⟩
  · have h1 : GlobalTheory.WeilParts.SuppPl ε V 1 := fun i j => by
      rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
    refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hP.weil.std V W ΛV ΛW hV hW χV χW om hP.eta hP.weil v ε hv uV uW 1 k h1 hk
      (fun u => ?_) f hf fun u hu => ?_
    · rw [GlobalTheory.InertVac.mem_latO_place_iff hv.1, GlobalTheory.InertVac.mem_latO_place_iff hv.1, ← hst,
        ← GlobalTheory.FinWeilO.actO_smul, (GlobalTheory.InertVac.actO_injective 1 k).eq_iff]
    · obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
      have h1 : 2 • (a • u) = u := by
        rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.InertVac.placeIdem_smul_eq hv.1 hu]
      have h2 := hvac.1 (a • u)
        (GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a ha u (GlobalTheory.PlaceModel.latO_le_top _ hu))
      rwa [h1] at h2
  · obtain ⟨x, hx, -, xs, x1, x2⟩ := GlobalTheory.VacInert.exists_unit_root hv W k hk
    rw [hmu.2 k x hx, uV x xs x1 x2, Circle.coe_one]

end GlobalTheory.AdTh
