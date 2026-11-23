import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTheRecOfIsRec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityUniqueOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL

namespace GlobalTheory.TheRecTransport

theorem exists_contra_equiv {H H' V V' : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : H →* H') (f' : H' →* H) (hf : Continuous f) (hf' : Continuous f') (hff : ∀ g, f (f' g) = g)
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H' V') (e : V ≃ₗ[ℂ] V')
    (he : ∀ g v, e (ρ g v) = ρ' (f g) (e v)) :
    ∃ d : smoothPart ρ.dual ≃ₗ[ℂ] smoothPart ρ'.dual, ∀ g l, d (contra ρ g l) = contra ρ' (f g) (d l) := by
  have key : ∀ g (l : Module.Dual ℂ V), e.symm.dualMap (ρ.dual g l) = ρ'.dual (f g) (e.symm.dualMap l) := by
    intro g l
    ext v
    obtain ⟨v, rfl⟩ := e.surjective v
    show l (ρ g⁻¹ (e.symm (e v))) = l (e.symm (ρ' (f g)⁻¹ (e v)))
    rw [← map_inv f, ← he, e.symm_apply_apply, e.symm_apply_apply]
  have hmap : (smoothPart ρ.dual).map (e.symm.dualMap : Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V') = smoothPart ρ'.dual := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ.dual g l = l} from hl).preimage hf').mem_nhds (by
          show ρ.dual (f' 1) l = l
          rw [map_one, map_one]; rfl)) fun g hg => ?_)
      have h1 : ρ.dual (f' g) l = l := hg
      show ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l
      rw [← hff g, ← key, h1]
    · intro l' hl'
      obtain ⟨l, rfl⟩ := e.symm.dualMap.surjective l'
      refine ⟨l, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((show IsOpen {g | ρ'.dual g (e.symm.dualMap l) = e.symm.dualMap l} from hl').preimage hf).mem_nhds
          (by
            show ρ'.dual (f 1) _ = _
            rw [map_one, map_one]; rfl)) fun g hg => ?_), rfl⟩
      have h1 : ρ'.dual (f g) (e.symm.dualMap l) = e.symm.dualMap l := hg
      show ρ.dual g l = l
      apply e.symm.dualMap.injective
      rw [key, h1]
  exact ⟨e.symm.dualMap.ofSubmodules _ _ hmap, fun g l => Subtype.ext (key g l)⟩

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem exists_of_repRel {i : k ≃+* k'} {n : ℕ} (π : IrrRep (GL (Fin n) k)) {x' : IrrGL k'} (H : RepRel i (cls π) x') :
    ∃ (π' : IrrRep (GL (Fin n) k')) (e : π.V ≃ₗ[ℂ] π'.V), x' = cls π' ∧
      ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v) := by
  obtain ⟨m, π₀, π', e, h1, rfl, he⟩ := H
  obtain rfl : n = m := congrArg Sigma.fst h1
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := π.ρ) (σ := π₀.ρ) (hs := π.smooth) (hi := π.irr) (hs' := π₀.smooth)
    (hi' := π₀.irr)).1 h1
  refine ⟨π', φ.toLinearEquiv.trans e, rfl, fun g v => ?_⟩
  have h2 : φ.toLinearEquiv (π.ρ g v) = π₀.ρ g (φ.toLinearEquiv v) := φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h2, he]

theorem continuous_glMap (i : k ≃+* k') (hi : Continuous i) (n : ℕ) :
    Continuous (GeneralLinearGroup.map (n := Fin n) i.toRingHom) :=
  Continuous.units_map _ (continuous_matrix fun a b => hi.comp (continuous_id.matrix_elem a b))

theorem contra_transport (i : k ≃+* k') (hi : Continuous i) (hs : Continuous i.symm) {n : ℕ}
    (π τ : IrrRep (GL (Fin n) k)) (π' τ' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (u : τ.V ≃ₗ[ℂ] τ'.V) (hu : ∀ g v, u (τ.ρ g v) = τ'.ρ (GeneralLinearGroup.map i.toRingHom g) (u v))
    (φ : τ.ρ.Equiv (contra π.ρ)) : Nonempty (τ'.ρ.Equiv (contra π'.ρ)) := by
  obtain ⟨d, hd⟩ := exists_contra_equiv (GeneralLinearGroup.map (n := Fin n) i.toRingHom)
    (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom) (continuous_glMap i hi n) (continuous_glMap i.symm hs n)
    (map_map_symm i) π.ρ π'.ρ e he
  refine ⟨.mk (u.symm.trans (φ.toLinearEquiv.trans d)) fun g => LinearMap.ext fun v => ?_⟩
  have h2 : ∀ g v, φ.toLinearEquiv (τ.ρ g v) = contra π.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  show d (φ.toLinearEquiv (u.symm (τ'.ρ g v))) = contra π'.ρ g (d (φ.toLinearEquiv (u.symm v)))
  rw [symm_rel i τ τ' u hu, h2, hd, map_map_symm]

theorem central_transport (i : k ≃+* k') {x : IrrGL k} {x' : IrrGL k'} (H : RepRel i x x') {ω : kˣ →* ℂˣ}
    (hω : HasCentralChar x.rep ω) :
    HasCentralChar x'.rep (ω.comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := exists_of_repRel _ H
  intro z v
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective v
  obtain ⟨v, rfl⟩ := e.surjective v
  have hz : GeneralLinearGroup.scalar (Fin x.1) z = GeneralLinearGroup.map i.toRingHom
      (GeneralLinearGroup.scalar (Fin x.1) (Units.map i.symm.toRingHom.toMonoidHom z)) := by
    ext a b
    by_cases hab : a = b <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal_apply, hab]
  show π'.cl.rep.ρ (GeneralLinearGroup.scalar (Fin x.1) z) (φ.toLinearEquiv (e v)) = _
  rw [← h2, hz, ← he, hω, map_smul, map_smul]
  rfl

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem equiv_lpDual (P : PlaceIso A w A' w' φ j i) (S : WD h ≃ WD h') (hS : ∀ y y', WDRel φ y y' ↔ S y = y')
    (y : WD h) : S y.lpDual = (S y).lpDual := by
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i P
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth g →
      GlobalTheory.WeilDeligne.IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : GlobalTheory.WeilDeligne.IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hF : ∀ y, S y = GlobalTheory.WDTransport.pullWD c.symm.toMonoidHom hd1 hq.symm hs1 y := fun y => by
    obtain ⟨n, b, rfl⟩ := WD.exists_rep y
    refine (hS _ _).1 ⟨n, b, GlobalTheory.WDTransport.pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl,
      (GlobalTheory.WDTransport.pullWD_mk _ _ _ _ b).symm, rfl, fun σ σ' hσ => ?_⟩
    rw [← (hc σ σ').mp hσ]
    simp
  obtain ⟨n, b, rfl⟩ := WD.exists_rep y
  rw [hF, hF, WD.lpDual_mk, GlobalTheory.WDTransport.pullWD_mk, GlobalTheory.WDTransport.pullWD_mk, WD.lpDual_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  show b.ρ.dual (c.symm.toMonoidHom σ) v = Representation.dual (b.ρ.comp c.symm.toMonoidHom) σ v
  simp only [Representation.dual_apply, MonoidHom.comp_apply, map_inv]

end GlobalTheory.TheRecTransport

end
