import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatAtLQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Ord2.LevelOfOrd

theorem asIdeal_eq_span (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (h : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
    exact Nat.prime_iff_prime_int.1 Fact.out
  exact ((((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
    (mt Ideal.span_singleton_eq_bot.1 hp.ne_zero)).eq_of_le v.isPrime.ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  intro l _ Ω _ _ _ e M V A κ he _ hcont haway hA hflag hine
  obtain ⟨v, hvA, hlv⟩ := hA
  have hval : A.valuation (l : Ω) < 1 := by
    have := (hvA ((l : ℕ) : 𝓞 ℚ)).2 hlv
    simpa using this
  let m : Fin 2 → ℤ := ![(e : ℤ), -(e : ℤ)]
  have hm : ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → κ i s = cycBar ℚ Ω l s ^ m i := by
    intro i s hs
    fin_cases i
    · exact (hine s hs).1
    · exact (hine s hs).2
  refine ⟨hcont, haway, ?_⟩
  intro w hw
  have hwv : w = v := HeightOneSpectrum.ext ((asIdeal_eq_span l w hw).trans (asIdeal_eq_span l v hlv).symm)
  subst hwv
  refine ⟨A, hvA, fun _ => 1, κ, fun i s _ => rfl, hflag, fun i s hs => by rw [hm i s hs]; exact (mul_one _).symm, Or.inl ?_⟩
  intro i j h
  have hn : m i - m j - 1 ≠ 0 := by
    have : (1 : ℤ) ≤ e := by exact_mod_cast he
    fin_cases i <;> fin_cases j <;> simp [m] <;> omega
  obtain ⟨g, hg, hgn⟩ := UpperTheory.V.Ws.Pt.cycIne ℚ Ω l A hval _ hn
  apply hgn
  have hD : g ∈ Dec (F := ℚ) A := Ine_le_Dec A hg
  have h1 := DFunLike.congr_fun h ⟨g, hD⟩
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hm i ⟨g, hD⟩ hg, hm j ⟨g, hD⟩ hg] at h1
  change cycBar ℚ Ω l g ^ m i = cycBar ℚ Ω l g ^ m j * cycBar ℚ Ω l g at h1
  rw [sub_sub, zpow_sub, zpow_add_one, ← h1, mul_inv_cancel]

end GlobalTheory.Ord2.LevelOfOrd

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.LocLanglands GlobalTheory.LocGL Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_flag_inertia_weights : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e M : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
    1 ≤ e → 1 ≤ M → Continuous V → LevelAway l M V → OverL l A → IsFlagOn V (Dec (F := ℚ) A) κ →
    (∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      κ 0 s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar ℚ Ω l s ^ (-(e : ℤ))) →
    Level l M ![(e : ℤ), -(e : ℤ)] V := by
  first | exact @GlobalTheory.Ord2.LevelOfOrd.main | exact GlobalTheory.Ord2.LevelOfOrd.main | (intros; apply GlobalTheory.Ord2.LevelOfOrd.main <;> assumption)

end
