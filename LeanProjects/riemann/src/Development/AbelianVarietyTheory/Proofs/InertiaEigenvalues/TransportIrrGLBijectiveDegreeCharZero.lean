import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section General
variable {G H : Type} [Group G] [Group H]

def compEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W} (φ : ρ.Equiv τ) (f : G →* H) :
    Representation.Equiv (ρ.comp f : Representation ℂ G V) (τ.comp f : Representation ℂ G W) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    have := congrArg (fun L => L v) (φ.toIntertwiningMap.isIntertwining' (f g))
    simpa using this

def compCompEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G)
    (g : G →* H) (h : ∀ x, f (g x) = x) : Representation.Equiv ((ρ.comp f).comp g : Representation ℂ G V) ρ :=
  .mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun v => by simp [h]

variable [TopologicalSpace G] [TopologicalSpace H]

def pullRep (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) (σ : IrrRep H) : IrrRep G :=
  ⟨σ.V, σ.ρ.comp f, fun v => (σ.smooth v).preimage hf,
    GlobalTheory.JacFactor.isIrreducible_comp_surj σ.ρ f hs σ.irr⟩

end General

section GLmap
variable {R S : Type} [CommRing R] [CommRing S]

abbrev mapGL (e : R ≃+* S) (n : ℕ) : GL (Fin n) R →* GL (Fin n) S := GeneralLinearGroup.map e.toRingHom

theorem mapGL_symm_mapGL (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) R) : mapGL e.symm n (mapGL e n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_mapGL_symm (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) S) : mapGL e n (mapGL e.symm n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_surjective (e : R ≃+* S) (n : ℕ) : Function.Surjective (mapGL e n) :=
  fun g => ⟨_, mapGL_mapGL_symm e n g⟩

theorem continuous_mapGL [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (n : ℕ) :
    Continuous (mapGL e n) :=
  Units.continuous_map (continuous_id.matrix_map he)

end GLmap
end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Fields
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def transportFun (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL k) : IrrGL k' :=
  ⟨x.1, (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep).cl⟩

theorem transportFun_left (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) (x : IrrGL k) :
    transportFun i.symm (by simpa using hi) (transportFun i hi' x) = x := by
  refine congrArg (Sigma.mk x.1) ((IrrRep.cl_eq_iff.2 ?_).trans x.2.cl_rep)
  obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep
    (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep)
  exact ⟨(compEquiv ψ (mapGL i.symm.symm x.1)).trans
    (compCompEquiv x.2.rep.ρ (mapGL i.symm x.1) (mapGL i.symm.symm x.1) fun g => mapGL_symm_mapGL i x.1 g)⟩

theorem repRel_iff (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL k) (x' : IrrGL k') :
    RepRel i x x' ↔ transportFun i hi' x = x' := by
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, he⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
    obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep π
    refine ⟨(compEquiv ψ (mapGL i.symm n)).trans (.mk e fun g => LinearMap.ext fun v => ?_)⟩
    have := he (mapGL i.symm n g) v
    rw [show GeneralLinearGroup.map i.toRingHom (mapGL i.symm n g) = g from mapGL_mapGL_symm i n g] at this
    simpa using this
  · rintro rfl
    refine ⟨x.1, x.2.rep, pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1)
      (mapGL_surjective i.symm x.1) x.2.rep, LinearEquiv.refl ℂ _,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, rfl, fun g v => ?_⟩
    show x.2.rep.ρ g v = x.2.rep.ρ (mapGL i.symm x.1 (mapGL i x.1 g)) v
    rw [mapGL_symm_mapGL]

theorem exists_transport (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) :
    ∃ T : IrrGL k ≃ IrrGL k', (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  have hi2 : Continuous i.symm.symm := by simpa using hi
  refine ⟨⟨transportFun i hi', transportFun i.symm hi2, fun x => transportFun_left i hi hi' x, fun y => ?_⟩,
    repRel_iff i hi', fun x => rfl⟩
  have := transportFun_left i.symm hi' hi2 y
  simpa using this

end Fields
end GlobalTheory.FieldTransport

open GlobalTheory.FieldTransport in

theorem GlobalTheory.transport_irrGL_bijective : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL k ≃ IrrGL k', (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact exists_transport i hi (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
