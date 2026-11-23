import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

def cocOff {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (S : Set Γ) : Submodule R (Γ → M) where
  carrier := {z | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + ρ g (z h)) ∧ ∀ g ∈ S, z g = 0}
  zero_mem' := ⟨IsLocallyConstant.const _, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g h => by simp only [Pi.add_apply, ha.2.1, hb.2.1, map_add]; abel,
    fun g h => by simp [ha.2.2 g h, hb.2.2 g h]⟩
  smul_mem' c a ha := ⟨ha.1.comp (c • ·), fun g h => by simp [ha.2.1], fun g h => by simp [ha.2.2 g h]⟩

def plDvd (F : Type) [Field F] (N : ℕ) : Set (HeightOneSpectrum (𝓞 F)) := {v | ((N : ℕ) : 𝓞 F) ∈ v.asIdeal}

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

def prodS (D : Raw Ω c) : ℕ := ∏ p ∈ D.S, p

def kerQ (D : Raw Ω c) (F : IntermediateField ℚ Ω) : Subgroup (G ℚ Ω) :=
  F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker

variable {D : Raw Ω c} (T : Tower D)

def Tower.Kr : Subgroup (G T.F Ω) := (kerQ D T.F).comap (resQ T.F)

def Tower.rbU (w : ℤ × ℤ) : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt w)

end UpperTheory.V.Ws

end
