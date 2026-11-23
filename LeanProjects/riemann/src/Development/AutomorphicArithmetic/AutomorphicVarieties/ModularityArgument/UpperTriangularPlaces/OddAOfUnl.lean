import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelKO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AbsCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SplitIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AdmissibleLevelRestriction.UnlOfOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatFrobT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf

open private infOf_of_weights not_mem_of_not_dvd from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelKO

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Lev UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Keep

theorem sphV {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRecV h rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h0 : (rc (algNorm σ)).mono0) (d : ℕ)
    (hI : ∀ s : ↥(Ine (F := F) A), (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ d) : GlobalTheory.SmGL.IsSpherical σ.ρ := by
  obtain ⟨a, ha, ε, H⟩ := hrc
  have hu : (rc (algNorm σ)).unr := by
    obtain ⟨k, b, e⟩ := WD.exists_rep (rc (algNorm σ))
    rw [← e] at h0 hI ⊢
    rw [WD.unr_mk]
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 h0, fun s => ?_⟩
    have h1 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h s))
    have h2 := hI s
    rw [WD.charPol_mk] at h2
    rw [h2, map_pow, map_sub, aeval_X, map_one] at h1
    have hs : Module.End.IsSemisimple (b.ρ (ineIncl h s) - algebraMap ℂ (Module.End ℂ (Fin k → ℂ)) 1) :=
      Module.End.isSemisimple_sub_algebraMap_iff.2 (b.semisimple _)
    rw [map_one] at hs
    exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ hs)
  obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hu)
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 g.2, hv0⟩

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n : ℕ}

def OddA (l : ℕ) [Fact l.Prime] (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Unl1 r w ∨ PotUnl r w

example : type_of% @OddU := @OddA

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem oddTw' (μ : G F Ω →* (Qbar l)ˣ) (h : OddA l r) : OddA l (tw r μ) := fun w hw =>
  (h w hw).imp (((flagLaws F Ω l n r).2.1 μ).2.2 w).1.1 (((flagLaws F Ω l n r).2.1 μ).2.2 w).2.1

theorem oddA_of_unl {M : ℕ} {m : Fin n → ℤ} (h : Th.Unl l M m r) : OddA l r := fun w hw => by
  obtain ⟨A, hA, κ, ⟨χ, -, h2, -⟩, hu⟩ := h w hw
  exact Or.inl (A4.unlOfOne F Ω l n r w A hA κ h2 hu)
end

def LevelKA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Level l M m r → OddA l r → WitA ι r → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

end UpperTheory.V.Keep
