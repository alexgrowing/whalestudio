import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem hkSat_of_isTripleWith (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    HkSat D.naut i s (ρ.ι.toRingHom.comp ρ.κ) (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) := by
  intro P hP hs k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hs hP
  refine ⟨x, h1.symm, h2.trans ?_⟩
  have hμ := mu_unr C (jIdx s) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  rw [(twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv).2, heckeVal, satake, Multiset.map_map]
  have e1 : ((k : ℂ) * ((D.R.r : ℂ) - k)) / 2 = ((k * (D.R.r - k) / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_half D.R hk)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at this
    rw [← this]
    push_cast
    ring
  have e2 : -((D.R.r : ℂ) + D.R.t) / 2 = -((D.R.nV / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_nV_half D.R)
    rw [Nat.cast_mul, Nat.cast_add] at this
    rw [← this]
    push_cast
    ring
  rw [e1, e2, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [mul_comm]
end Triple
end GlobalTheory.TripleLocal
end
end
