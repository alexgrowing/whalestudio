import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KOneTransport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] →+* 𝒪[k'] :=
  (i.toRingHom.comp (𝒪[k]).subtype).codRestrict 𝒪[k'] fun x => (hv x).2 x.2

theorem intMap_coe (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) (x : 𝒪[k]) :
    ((intMap i hv x : 𝒪[k']) : k') = i x := rfl

theorem symm_hv (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    ∀ y : k', valuation k (i.symm y) ≤ 1 ↔ valuation k' y ≤ 1 := fun y => by
  have := hv (i.symm y); rw [RingEquiv.apply_symm_apply] at this; exact this.symm

theorem isLocalHom_intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    IsLocalHom (intMap i hv) := by
  refine ⟨fun a ha => ?_⟩
  have h := ha.map (intMap i.symm (symm_hv i hv))
  have e : intMap i.symm (symm_hv i hv) (intMap i hv a) = a := Subtype.ext (by
    rw [intMap_coe, intMap_coe, RingEquiv.symm_apply_apply])
  rwa [e] at h

theorem map_mem_kOne (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}
    {g : GL (Fin n) k} (hg : g ∈ GlobalTheory.SplitWeil.KOne k (Fin n)) :
    GeneralLinearGroup.map i.toRingHom g ∈ GlobalTheory.SplitWeil.KOne k' (Fin n) := by
  haveI := isLocalHom_intMap i hv
  obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.1 hg
  refine Subgroup.mem_map.2 ⟨GeneralLinearGroup.map (intMap i hv) g0, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hg0 ⊢
    ext a b
    have h := congrArg (fun m : GL (Fin n) (IsLocalRing.ResidueField 𝒪[k]) => (m.val : Matrix (Fin n) (Fin n) _) a b) hg0
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at h ⊢
    rw [← IsLocalRing.ResidueField.map_residue, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · ext a b
    simp [GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.KOneTransport

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL in

theorem GlobalTheory.KOneTransport.fixed_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' H hx
  obtain ⟨-, hv, -⟩ := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel _ H
  obtain ⟨v, hv0, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [Submodule.ne_bot_iff]
  refine ⟨φ.toLinearEquiv (e v), fun h => ?_, ?_⟩
  · have hg : GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k') ∈ GlobalTheory.SplitWeil.KOne k (Fin x.1) :=
      GlobalTheory.KOneTransport.map_mem_kOne i.symm (GlobalTheory.KOneTransport.symm_hv i hv) h.2
    have hfx : x.rep (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v = v := by
      have := hv0 ⟨_, hg⟩
      simpa using this
    have h3 := he (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v
    rw [map_map_symm] at h3
    show π'.cl.rep.ρ (h : GL (Fin x.1) k') (φ.toLinearEquiv (e v)) = ((1 : _ →* ℂˣ) h : ℂ) • φ.toLinearEquiv (e v)
    rw [← h2, ← h3]
    erw [hfx]
    simp
  · intro h0
    apply hvne
    have : e v = 0 := φ.toLinearEquiv.map_eq_zero_iff.1 h0
    exact e.map_eq_zero_iff.1 this
