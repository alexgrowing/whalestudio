import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.FixedKOneTransport

theorem fixed_ne_bot_of_equiv {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (f : G →* G') (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V')
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' (f g) (e v)) (H : Subgroup G) (H' : Subgroup G')
    (hH : H' ≤ H.map f) (h : GlobalTheory.PRep.fixed ρ H ≠ ⊥) : GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine fun hb => hv0 (e.injective ?_)
  have hmem : e v ∈ GlobalTheory.PRep.fixed ρ' H' := by
    intro h'
    obtain ⟨g, hg, hfg⟩ := hH h'.2
    have hgv : ρ g v = v := by simpa using hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [← hfg, ← he, hgv]
  rw [hb] at hmem
  simpa using hmem

open ValuativeRel

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def integerEquiv (i : k ≃+* k') (hi : Continuous i) : 𝒪[k] ≃+* 𝒪[k'] :=
  (i.subringMap (s := 𝒪[k])).trans (RingEquiv.subringCongr (GlobalTheory.LocalFieldIso.map_integer i hi))

theorem kOne_le_map (i : k ≃+* k') (hi : Continuous i) (n : Type) [Fintype n] [DecidableEq n] :
    GlobalTheory.SplitWeil.KOne k' n ≤ (GlobalTheory.SplitWeil.KOne k n).map (Matrix.GeneralLinearGroup.map i.toRingHom) := by
  rintro _ ⟨a', ha', rfl⟩
  set u := integerEquiv i hi
  let ψ : 𝓀[k'] →+* 𝓀[k] := IsLocalRing.ResidueField.map (u.symm : 𝒪[k'] →+* 𝒪[k])
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (Matrix.GeneralLinearGroup.map (u.symm : 𝒪[k'] →+* 𝒪[k]) a'),
    ⟨_, ?_, rfl⟩, ?_⟩
  · simp only [SetLike.mem_coe, MonoidHom.mem_ker] at ha' ⊢
    have h1 : Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])
        (Matrix.GeneralLinearGroup.map (u.symm : 𝒪[k'] →+* 𝒪[k]) a') =
        Matrix.GeneralLinearGroup.map ψ (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k']) a') := by
      ext p q
      simp [ψ]
    rw [h1, ha', map_one]
  · ext p q
    simp only [u]
    exact congrArg Subtype.val ((integerEquiv i hi).apply_symm_apply _)

end GlobalTheory.FixedKOneTransport

theorem GlobalTheory.FixedKOneTransport.fixed_kOne_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'),
    Continuous i → ∀ (x : GlobalTheory.LocGL.IrrGL k) (x' : GlobalTheory.LocGL.IrrGL k'), GlobalTheory.LocLanglands.RepRel i x x' →
      GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' H hx
  rw [← GlobalTheory.LocLanglands.FieldCompat.cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel _ H
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  refine GlobalTheory.FixedKOneTransport.fixed_ne_bot_of_equiv (Matrix.GeneralLinearGroup.map i.toRingHom) x.rep
    π'.cl.rep.ρ (e.trans φ.toLinearEquiv) (fun g v => ?_) _ _ (GlobalTheory.FixedKOneTransport.kOne_le_map i hi _) hx
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, he, h2]
