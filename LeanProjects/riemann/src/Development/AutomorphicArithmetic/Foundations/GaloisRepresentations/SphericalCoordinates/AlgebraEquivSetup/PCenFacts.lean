import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCenFacts :
    Sides → CenFacts := by
  intro hS E _ _ _ A n _ x hx q hq hsp w hw z hz
  obtain ⟨-, -, -, h4, -⟩ := hS E A x hx q hq hsp w hw
  have hscal : ∀ (u : Plc E) (a : GL (Fin n) (u.adicCompletion E)), comp u z * a = a * comp u z := by
    intro u a
    by_cases h : UpperTheory.Gal.CertificateRingHomMap.SameK x (UpperTheory.Gal.CertificateRingHomMap.cj u) w
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, (hz u).1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    · rw [(hz u).2 h, one_mul, mul_one]
  refine ⟨fun g => UpperTheory.Gal.CertificateRingHomMap.guf_ext ?_ fun u => ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_mul, map_mul, hscal]
  · refine (hz u).2 fun h => hu ?_
    have h' := h4 _ h
    have e : (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal = _ :=
      (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
    rw [e, Ideal.mem_comap, map_natCast] at h'
    exact h'
