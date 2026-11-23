import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem crt_unit (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) (a : (ZMod M)ˣ) :
    ∃ u : (ZMod (M * N))ˣ, ZMod.unitsMap (Nat.dvd_mul_right M N) u = a ∧
      ZMod.unitsMap (Nat.dvd_mul_left N M) u = 1 := by
  set e := ZMod.chineseRemainder h
  have h1 : ZMod.castHom (Nat.dvd_mul_right M N) (ZMod M) = (RingHom.fst _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  have h2 : ZMod.castHom (Nat.dvd_mul_left N M) (ZMod N) = (RingHom.snd _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (MulEquiv.prodUnits.symm (a, 1)), ?_, ?_⟩
  · ext
    rw [ZMod.unitsMap_def, h1]
    simp [MulEquiv.prodUnits]
  · ext
    rw [ZMod.unitsMap_def, h2]
    simp [MulEquiv.prodUnits]

theorem UpperTheory.V.Ws.large₂.clsIndep :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M N : ℕ) [NeZero M] [NeZero N], M.Coprime N → ∀ a : (ZMod M)ˣ,
      ∃ g : G ℚ Ω, Chr.cls ℚ Ω M g = a ∧ ∀ (N' : ℕ) [NeZero N'], N' ∣ N → Chr.cls ℚ Ω N' g = 1 := by
  intro Ω _ _ _ M N _ _ hMN a
  obtain ⟨u, hu1, hu2⟩ := crt_unit M N hMN a
  obtain ⟨g, hg⟩ := (UpperTheory.V.Chr.clsOnto Ω (M * N)).1 u
  have hres := (UpperTheory.V.Chr.clsFacts ℚ Ω (M * N)).2.1
  refine ⟨g, ?_, ?_⟩
  · rw [← hres M (Nat.dvd_mul_right M N), MonoidHom.comp_apply, hg, hu1]
  · intro N' _ hN'
    rw [← hres N' (hN'.trans (Nat.dvd_mul_left N M)), MonoidHom.comp_apply, hg,
      ← ZMod.unitsMap_comp hN' (Nat.dvd_mul_left N M), MonoidHom.comp_apply, hu2, map_one]
