import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedBasePointFreeGenericFibre
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadConn

variable {S : Scheme.{0}}

theorem unit_comp (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := by
  have h := Over.w (η[G])
  have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
  rwa [h2] at h

theorem hom_unit (G : Over S) [GrpObj G] (s : S) : G.hom ((η[G]).left s) = s := by
  rw [← Scheme.Hom.comp_apply, unit_comp]
  rfl

theorem isConnected_fibre (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : G.hom ⁻¹' {s} ⊆ U) : _root_.IsConnected (G.hom ⁻¹' {s}) := by
  have hu : (η[G]).left s ∈ G.hom ⁻¹' {s} := hom_unit G s
  have he : connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) = G.hom ⁻¹' {s} := by
    refine (connectedComponentIn_subset _ _).antisymm fun x hx => ?_
    have h1 := (hU x).1 (h hx)
    have hx' : G.hom x = s := hx
    rwa [hx'] at h1
  rw [← he]
  exact isConnected_connectedComponentIn_iff.2 hu

theorem subset_of_isPreconnected (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : _root_.IsPreconnected (G.hom ⁻¹' {s})) : G.hom ⁻¹' {s} ⊆ U := by
  intro x hx
  have hx' : G.hom x = s := hx
  refine (hU x).2 ?_
  rw [hx']
  exact h.subset_connectedComponentIn (hom_unit G s) subset_rfl hx

theorem geometricallyConnected_fibre (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] (s : S) (h : _root_.IsConnected (G.hom ⁻¹' {s})) :
    GeometricallyConnected (G.hom.fiberToSpecResidueField s) := by
  have hc : ConnectedSpace (G.hom.fiber s) :=
    (G.hom.fiberHomeo s).connectedSpace_iff.2 (isConnected_iff_connectedSpace.1 h)
  exact GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint (S.residueField s)
    (Over.mk (G.hom.fiberToSpecResidueField s))
    (inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField s))))
    (inferInstanceAs (QuasiCompact (pullback.snd G.hom (S.fromSpecResidueField s)))) hc
    ⟨Over.homMk (pullback.lift (S.fromSpecResidueField s ≫ (η[G]).left) (𝟙 _)
      (by rw [Category.assoc, unit_comp, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _)⟩

theorem isConnected_of_geometricallyConnected_fibre {X : Scheme.{0}} (f : X ⟶ S) (s : S)
    (h : GeometricallyConnected (f.fiberToSpecResidueField s)) : _root_.IsConnected (f ⁻¹' {s}) := by
  have hc : ConnectedSpace (f.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s)
  exact isConnected_iff_connectedSpace.2 ((f.fiberHomeo s).connectedSpace_iff.1 hc)

end GlobalTheory.SpreadConn

namespace GlobalTheory.SpreadConn

theorem geometricallyConnected_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  intro R _ _ _ G _ hs hq K _ e he hgc
  obtain ⟨G₀, _, j, -, hjo, hj⟩ := GlobalTheory.identityComponentOpen (Sp R) G hs
  let U : Set G.left := Set.range j.left
  let η₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η₀ ∈ Set.range (spMap e) := ⟨(default : PrimeSpectrum K), by
    apply PrimeSpectrum.ext
    change Ideal.comap e (default : PrimeSpectrum K).asIdeal = ⊥
    have h0 : (default : PrimeSpectrum K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h0]
    exact Ideal.comap_bot_of_injective _ he⟩
  have hgen : GeometricallyConnected (G.hom.fiberToSpecResidueField η₀) :=
    GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom (spMap e)
      ((Sp R).fromSpecResidueField η₀)
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hη) hgc
  have hsub0 : G.hom ⁻¹' {η₀} ⊆ U := subset_of_isPreconnected G U hj η₀
    (isConnected_of_geometricallyConnected_fibre G.hom η₀ hgen).isPreconnected
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have hUo : IsOpen U := j.left.isOpenEmbedding.isOpen_range
  have hZ : Topology.IsConstructible Uᶜ :=
    (IsRetrocompact.isConstructible hUo fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _).compl
  have hC : Topology.IsConstructible (G.hom '' Uᶜ) := G.hom.isConstructible_image hZ
  obtain ⟨V, hV, h1, h2⟩ := GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible continuous_id hC.compl
  rw [Set.preimage_id] at h1 h2
  have hηC : η₀ ∈ (G.hom '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, hxη⟩
    exact hx (hsub0 hxη)
  have hgenz : ∀ p : Sp R, η₀ ⤳ p := fun p =>
    (PrimeSpectrum.le_iff_specializes (η₀ : PrimeSpectrum R) (p : PrimeSpectrum R)).1
      (show (⊥ : Ideal R) ≤ (p : PrimeSpectrum R).asIdeal from bot_le)
  have hcl : closure (G.hom '' Uᶜ)ᶜ = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    exact closure_mono (Set.singleton_subset_iff.2 hηC) (specializes_iff_mem_closure.1 (hgenz p))
  rw [hcl, Set.inter_univ] at h1 h2
  have hVne : V.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h2
    exact Set.empty_ne_univ h2
  obtain ⟨p₀, hp₀⟩ := hVne
  have hηV : η₀ ∈ V := (hgenz p₀).mem_open hV hp₀
  obtain ⟨_, ⟨f, rfl⟩, hf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηV hV
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).1 hf ?_, fun F _ ψ hψ => ?_⟩
  · rw [he (h0.trans (map_zero e).symm)]
    exact zero_mem _
  · let p : Sp R := spMap ψ (default : PrimeSpectrum F)
    have hpf : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine (PrimeSpectrum.mem_basicOpen f (p : PrimeSpectrum R)).2 fun hfp => ?_
      change ψ f ∈ (default : PrimeSpectrum F).asIdeal at hfp
      exact (default : PrimeSpectrum F).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfp hψ)
    have hpC : p ∉ G.hom '' Uᶜ := h1 (hfV hpf)
    have hsub : G.hom ⁻¹' {p} ⊆ U := fun x hx => by
      by_contra hxU
      exact hpC ⟨x, hxU, hx⟩
    have hfib := geometricallyConnected_fibre G p (isConnected_fibre G U hj p hsub)
    refine GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom
      ((Sp R).fromSpecResidueField p) (spMap ψ) ?_ hfib
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨y, rfl⟩
    show spMap ψ y = p
    rw [Subsingleton.elim (α := PrimeSpectrum F) y default]

end GlobalTheory.SpreadConn
