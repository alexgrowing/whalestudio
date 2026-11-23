import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestFunctionsTransportLocalLatticeIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableOrbitalIntegralPreservedLatticeIsometryStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceEqTwo

theorem traceEq_of_geomExpansion : GeomExpansion → TraceEq := by
  intro hG D V lam S M T U μa μf μ _ _ fa ff hTD V' hr S' M' hlam' j hj μa' μ' _ _ fa' hR' hA'
  obtain ⟨-, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF, hTF⟩ := hTU T U
  obtain ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩ := hTD
  set lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr) with hlamdef
  have hTD' : IsTestData V' lam' M' T' U' μa' (fun v => (μf v).map (j v)) μ' fa' (transfer j ff) := by
    refine ⟨hr ▸ hodd, ?_, hlam', hNF hnf, hR', hA', hTF μf ff hTFin⟩
    intro ρ i k hik
    have h := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    simpa [hr, lam'] using h
  choose dta dtf dt hdt using fun (r : ℕ) (P : PPol D.sp.cm.sig r) => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.exists_isTorusMeas P
  obtain ⟨hFin, -, hTr⟩ := hG D V lam S M T U μa μf μ fa ff ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩
    (dta _) (dtf _) (dt _) (hdt _)
  obtain ⟨hFin', -, hTr'⟩ := hG D V' lam' S' M' T' U' μa' _ μ' fa' _ hTD' (dta _) (dtf _) (dt _) (hdt _)

  have gen : ∀ (r : ℕ) (h : r = V.rank),
      (∀ (P : PPol D.sp.cm.sig r) v, PhiOK (J := V.gram) (μf v) (dtf r P v) (ff v)) ∧
      ∑ᶠ P : PPol D.sp.cm.sig r, ((GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.torVol P (dt r P)).toReal : ℂ) *
          (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf r P v) (ff v)) *
          ∏ ρ : D.what₂.Tau, PhiReal P (embOverOf D ρ) (fun i => lam ρ (i.cast h)) (dta r P (placeOf D ρ)) =
        ∑ᶠ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta _ P) (dtf _ P) (dt _ P) := by
    intro r h
    subst h
    exact ⟨fun P v => (hFin P).2.1 v, rfl⟩
  refine ⟨_, hTr, ?_⟩
  convert hTr' using 1
  rw [← (gen _ hr).2]
  refine finsum_congr fun P => ?_
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
  congr 2
  refine finprod_congr fun v => ?_
  exact (GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry D V V' _ P v (j v) (hj v) (μf v) (dtf _ P v) (ff v) (hRP.2.1 v) ((hdt _ P).2.1 v) ((gen _ hr).1 P v) ((hFin' P).2.1 v)).symm

end GlobalTheory.TraceEqTwo

end
