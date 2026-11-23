import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PurLocSW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinFreePU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.FreeFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RatioT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open UpperTheory.GalN.V UpperTheory.Zero.LLC UpperTheory.V.Z.Win
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private ex_elt algPow_const flag_cont cyc_cont from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
open private ratio_lt from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PurLocSW
open private place_under pow_eq_one_of_kills charpoly_of_flag from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinFreePU

namespace UpperTheory.V.Z.Win.RR

theorem local_condition_of_flag_of_characters_not_cyclotomic_shift {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (h : IsPlaceOver A w)
    {ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ} (hf : W.HasFlag (r.comp (Dec (F := F) A).subtype) ψ)
    (hg : ∀ i j, ψ i ≠ ψ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) : Unl1 r w := by
  intro B hB
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) h hB
  have m1 : ∀ s : ↥(Dec (F := F) (g • A)), g⁻¹ * (s : G F Ω) * g ∈ Dec (F := F) A := fun s => by
    have h1 : (s : G F Ω) • g • A = g • A := s.2
    show (g⁻¹ * (s : G F Ω) * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  have m2 : ∀ s : ↥(Dec (F := F) A), g * (s : G F Ω) * g⁻¹ ∈ Dec (F := F) (g • A) := fun s => by
    have h1 : (s : G F Ω) • A = A := s.2
    show (g * (s : G F Ω) * g⁻¹) • g • A = g • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  let c : ↥(Dec (F := F) (g • A)) →* ↥(Dec (F := F) A) :=
    MonoidHom.mk' (fun s => ⟨_, m1 s⟩) fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun i => (ψ i).comp c, ⟨p * (r g)⁻¹, fun s => ?_⟩, fun i j e => hg i j (MonoidHom.ext fun s => ?_)⟩
  · have e1 : p * (r g)⁻¹ * r s * (p * (r g)⁻¹)⁻¹ = p * r (g⁻¹ * (s : G F Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    rw [e1]
    exact hp (c s)
  · have e2 := DFunLike.congr_fun e ⟨_, m2 s⟩
    have e3 : c ⟨_, m2 s⟩ = s := Subtype.ext (by
      show g⁻¹ * (g * (s : G F Ω) * g⁻¹) * g = s
      group)
    change ψ i (c ⟨_, m2 s⟩) = ψ j (c ⟨_, m2 s⟩) * cycBar F Ω l (g * (s : G F Ω) * g⁻¹) at e2
    rw [e3, map_mul (cycBar F Ω l), map_mul (cycBar F Ω l), map_inv, mul_inv_cancel_comm] at e2
    exact e2

def AutPA {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutP ι r ∧ (Continuous r → WitA ι r)

end UpperTheory.V.Z.Win.RR
