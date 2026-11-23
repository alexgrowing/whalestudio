import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.large₂.redOne :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (m : ℕ), l.Coprime m → ∀ x : c.Oˣ, x ^ m = 1 → residue c.O (x : c.O) = 1 → x = 1 := by
  intro l _ c m hm x hx hres
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, -, -, -, -, -, -, hunit⟩ := dvrFacts l c.O
  have hmu : IsUnit ((m : ℕ) : c.O) :=
    hunit m ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hm)
  have hgeom : (∑ i ∈ Finset.range m, (x : c.O) ^ i) * ((x : c.O) - 1) = 0 := by
    rw [geom_sum_mul, ← Units.val_pow_eq_pow_val, hx, Units.val_one, sub_self]
  have hsum : IsUnit (∑ i ∈ Finset.range m, (x : c.O) ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hr := hmu.map (residue c.O)
    rw [map_natCast] at hr
    exact hr.ne_zero
  have h0 : (x : c.O) - 1 = 0 := (hsum.mul_right_eq_zero).1 hgeom
  exact Units.ext (sub_eq_zero.1 h0)
