import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleTypeIIBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdmissibleRankTwoSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.KillsComp
end GlobalTheory.KillsComp
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.IrrTransfer
end GlobalTheory.Ord2.IrrTransfer
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2
open UpperTheory.V.Base UpperTheory.V.U3 in
theorem admissible_typeII_block_alt : U3.CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* U3.GG 3 (PadicAlgCl l)} (_ : D.IsPt U g₁ r) (ι : Qbar l ≃+* ℂ), U3.TypeII D.η r → ∀ W : R2 Ω l, D.IsExt r W → Continuous W → (∀ g, (mat W g).det = ((D.η g : ℤˣ) : ℤ)) → D.IsModularDense ι W → admitted ι e W := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ hM r h ι hII W hext hcont hdet hmod
  have hdt : ∀ g, (dt W g : Qbar l) = ((D.η g : ℤˣ) : ℤ) := fun g => hdet g
  obtain ⟨A, hA, -, hIA, -, -, -, -⟩ := dat_loc D
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hl1⟩ := dat_facts D
  obtain ⟨hIk, -⟩ := hl1 A hA
  let ψQ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω ψ)
  let χ : G ℚ Ω →* (Qbar l)ˣ := (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom).comp (Chr.dirG ℚ Ω (HV.comp l ψ))
  have hΨ : ∀ g, D.ΨQ g = cycBar ℚ Ω l g ^ (e : ℤ) * ψQ g := fun g => by
    show Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom (chiO ℚ Ω l c.O g ^ (e : ℤ) * Chr.dirG ℚ Ω ψ g) = _
    rw [map_mul, map_zpow]
    rfl
  have hχ2 : ∀ g, χ g * χ g = 1 := fun g => by
    have h1 : Chr.dirG ℚ Ω (HV.comp l ψ) g * Chr.dirG ℚ Ω (HV.comp l ψ) g = 1 := by
      apply Units.ext
      show (HV.comp l ψ) (Chr.cls ℚ Ω N g) * (HV.comp l ψ) (Chr.cls ℚ Ω N g) = 1
      rw [← MulChar.mul_apply, ← sq, D.gd.ine, MulChar.one_apply (Units.isUnit _)]
    show Units.map _ _ * Units.map _ _ = 1
    rw [← map_mul, h1, map_one]
  have hψχ : ∀ s ∈ Ine (F := ℚ) A, ψQ s = χ s := fun s hs => by
    rw [← hIA] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    show Units.map _ _ = Units.map _ _
    rw [psi_ine D g hg]
  obtain ⟨κ, hflag, hκ⟩ := flag_block hC D hM h hII W hext hdet A hA
  refine ⟨hcont, ?_, fun s hs => Units.ext ?_, GlobalTheory.Ord2.irr_transfer D.η D.η_ker W hdet (typeII_irr_cyc hC D hM h hII W hext),
    levelAway_block hC D hM h hII W hext hdet, ?_, A, χ, κ, ?_, fun s hs => ?_, hflag, fun s hs => ?_, fun s hs => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    rw [MonoidHom.one_apply, Units.val_one, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hdt]
    rcases Int.units_eq_one_or (D.η g) with h1 | h1 <;> simp [h1]
  · rw [hdt, conj_eta D s hs]
    simp
  · obtain ⟨f, hf⟩ := _root_.UpperTheory.GalN.V.mod0'_alt hmod
    refine ⟨f, 1, 1, le_rfl, fun _ _ => rfl, ?_⟩
    rw [mul_one]
    exact hf
  · obtain ⟨h1, h2, h3, -⟩ := places ℚ Ω l A
    have hne : A ≠ ⊤ := fun ht => (h2 ht).2 hA
    obtain ⟨v, hv⟩ := h1 hne
    exact ⟨v, hv, (h3 v hv).1 hA⟩
  · show Units.map _ _ = 1
    rw [GlobalTheory.killsMu_comp_of_sq_eq_one ψ D.gd.l_odd D.gd.ine s hs, map_one]
  · rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hdt, hIk hs]
    simp
  · rw [(hκ s hs).1, (hκ s hs).2, hΨ, hψχ s hs, mul_inv, ← zpow_neg]
    refine ⟨rfl, ?_⟩
    congr 1
    exact inv_eq_of_mul_eq_one_right (hχ2 s)
end GlobalTheory.Ord2
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2.TwDet
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
end GlobalTheory.Ord2.TwDet
namespace GlobalTheory.Ord2
open TwDet
end GlobalTheory.Ord2
end
end
