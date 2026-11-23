import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.conjLoc :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.ConjLoc := by
  intro E _ _ _ a u
  have hp : ∀ (b : Af E) (v : Plc E), b v = pLoc E v b := fun _ _ => rfl
  refine ⟨fun h => ?_, ?_, fun m => ?_, ?_, continuous_conjFin _⟩
  · rw [hp, pLoc_conjFin, ← hp, h, map_one]
  · rw [hp, pLoc_conjFin, (conjLoc_spec (conjE E) u).2.2, ← hp]
  · have h := (conjLoc_spec (conjE E) u).2.2 ((m : ℕ) : (cj u).adicCompletion E)
    rwa [map_natCast] at h
  · refine FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_
    rw [hp, hp a, pLoc_conjFin, pLoc_conjFin, GlobalTheory.SplitPts.conjLoc_pLoc, GlobalTheory.SplitPts.conjLoc_psi]
