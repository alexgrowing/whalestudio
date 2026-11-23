import ReciprocityTheory.DualLattices.DvdOfCoeffZero
import ReciprocityTheory.DualLattices.ValUntiltESubOne
import ReciprocityTheory.DualLattices.MulIterateRootEqZero
import ReciprocityTheory.DualLattices.ZmodTrichotomy
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

namespace ReciprocityTheory.PGsh

theorem a0 (p : ℕ) [Fact p.Prime] : TiltStructureStatement p := by
  intro C _ _ _ v O _ _ hv _ _
  have hK : KerThetaStatement p O := kerTheta (p := p) (C := C) (v := v) (O := O) hv
  have hO : ∀ x : O, (p : O) * x = 0 → x = 0 := by
    intro x hx
    have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)
    have h1 := congrArg (algebraMap O C) hx
    rw [map_mul, map_natCast, map_zero] at h1
    apply hv.hom_inj
    rw [map_zero]
    exact (mul_eq_zero.mp h1).resolve_left hp0
  obtain ⟨pf, hpf⟩ := exists_pflat (p := p) (hv := hv)
  exact ⟨⟨pf, hpf⟩, exists_eps (p := p) (hv := hv), hK,
    xiNu p C v O hK, regular (p := p) (O := O) (hO := hO), flatW' (p := p) (O := O)⟩

end ReciprocityTheory.PGsh
