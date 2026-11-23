import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrMult

theorem strictAnti_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) : StrictAnti lam := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by obtain ⟨k, hk⟩ := hr; omega⟩
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

theorem geomExpansion_of_parts : EllTrace → EllipticPart → RealStable → GeomExpansion := by
  intro hE hP hR D V lam S M T U μa μf μ _ _ fa ff hT dta dtf dt hdt
  obtain ⟨hOK, hfin, -, hint⟩ := hP D V lam S M T U μa μf μ fa ff hT dta dtf dt hdt
  have heq : ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb V μa μf fa ff P (dta P) (dtf P) (dt P) = GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta P) (dtf P) (dt P) := by
    intro P
    unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
    congr 1
    rw [← (Equiv.ofBijective _ (GlobalTheory.AdelicU.placeOf_bijective D)).prod_comp]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    exact hR D V lam S M μa fa hT.1 (fun ρ => strictAnti_of_gap hT.1 (hT.2.1 ρ)) hT.2.2.1 hT.2.2.2.2.1.1
      hT.2.2.2.2.2.1 P ρ (dta P (GlobalTheory.AdelicU.placeOf D ρ)) ((hdt P).1 _)
  have hfun : (fun P => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)) =
      fun P => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta P) (dtf P) (dt P) := funext heq
  refine ⟨fun P => (hOK P).1, hfun ▸ hfin, ?_⟩
  have h1 := hE D V lam S M T U μa μf μ fa ff hT
  rw [hint, hfun] at h1
  exact h1

end GlobalTheory.TrMult

end
