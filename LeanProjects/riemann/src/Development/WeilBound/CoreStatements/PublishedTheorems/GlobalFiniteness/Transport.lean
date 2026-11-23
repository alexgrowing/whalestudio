import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIso

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GFTransport

theorem gsEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) :
    Nonempty (GS Ω S ≃ₜ* galUnramifiedOutside F Ω S) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let E := maxUnramifiedOutside F Ω S
  let φ : G F Ω →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective Ω
  have hNS : NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
    le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)
  have hker : φ.ker = NS Ω S := by
    rw [hNS]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS Ω S ≃* Gal(E/F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G F Ω) := inferInstance
  have : CompactSpace (GS Ω S) := Quotient.compactSpace
  exact ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }⟩

theorem gsTransportK (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : Finite S')
      (_ : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'),
      ∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S' := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨K, ψ, e, he⟩ := GlobalTheory.CompanionTheory.GSCd.Transport.exists_embedded F Ω
  classical
  let T : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    S.map (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv ψ)).toEmbedding
  have hC : GlobalTheory.CompanionTheory.GSCd.Transport.Corr ψ (S : Set (HeightOneSpectrum (𝓞 F)))
      (T : Set (HeightOneSpectrum (𝓞 K.1))) := by
    intro v
    simp [T]
  obtain ⟨θ⟩ := GlobalTheory.CompanionTheory.GSCd.Transport.nonempty_gal ψ e he hC
  refine ⟨K, (T : Set (HeightOneSpectrum (𝓞 K.1))), inferInstance, θ, ?_⟩
  intro n hn w hw
  have hv : (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv ψ)).symm w ∈ S := by
    apply hn
    change RingOfIntegers.mapRingEquiv ψ (n : 𝓞 F) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨_, hv, (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv _).apply_symm_apply w⟩)

theorem mapAlong_eq_id_of_eq_id {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (A : Rep.{0} k G) [IsDiscreteRep A] (χ : G →* G) (hχ : Continuous χ) (h : χ = MonoidHom.id G)
    (u : Rep.res χ A ⟶ A) (hu : ∀ a, u.hom a = a) (n : ℕ) :
    cohomologyMapAlong χ hχ u n = 𝟙 _ := by
  subst h
  have : u = 𝟙 A := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => hu a))
  subst this
  exact cohomologyMapAlong_id n

theorem mapAlong_transport_comp {k G H : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H)
    (A : Rep.{0} k G) [IsDiscreteRep A] (n : ℕ) :
    have := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A
    ∃ (p : cohomology A n ⟶ cohomology (Rep.res (θ.symm : H ≃* G).toMonoidHom A) n)
      (q : cohomology (Rep.res (θ.symm : H ≃* G).toMonoidHom A) n ⟶ cohomology A n), p ≫ q = 𝟙 _ := by
  have := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A
  let φ : H →* G := (θ.symm : H ≃* G).toMonoidHom
  let ψ : G →* H := (θ : G ≃* H).toMonoidHom
  have hφ : Continuous φ := θ.symm.continuous
  have hψ : Continuous ψ := θ.continuous
  let g : Rep.res ψ (Rep.res φ A) ⟶ A :=
    Rep.ofHom ⟨LinearMap.id, fun x => LinearMap.ext fun a => by
      show A.ρ (θ.symm (θ x)) a = A.ρ x a
      simp⟩
  refine ⟨cohomologyMapAlong φ hφ (𝟙 _) n, cohomologyMapAlong ψ hψ g n, ?_⟩
  rw [← cohomologyMapAlong_comp]
  exact mapAlong_eq_id_of_eq_id A (φ.comp ψ) (hφ.comp hψ)
    (MonoidHom.ext fun x => by show θ.symm (θ x) = x; simp)
    ((Rep.resFunctor ψ).map (𝟙 (Rep.res φ A)) ≫ g) (fun a => by first | rfl | simp [g]) n

theorem finite_cohomology_transport {k G H : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H)
    (A : Rep.{0} k G) [IsDiscreteRep A] (n : ℕ)
    (h : haveI := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A;
      Finite (cohomology (Rep.res (θ.symm : H ≃* G).toMonoidHom A) n)) :
    Finite (cohomology A n) := by
  have := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A
  obtain ⟨p, q, hpq⟩ := mapAlong_transport_comp θ A n
  refine Finite.of_surjective q.hom fun x => ⟨p.hom x, ?_⟩
  rw [← ModuleCat.comp_apply, hpq]
  rfl

theorem subsingleton_cohomology_transport {k G H : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H)
    (A : Rep.{0} k G) [IsDiscreteRep A] (n : ℕ)
    (h : haveI := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A;
      Subsingleton (cohomology (Rep.res (θ.symm : H ≃* G).toMonoidHom A) n)) :
    Subsingleton (cohomology A n) := by
  have := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A
  obtain ⟨p, q, hpq⟩ := mapAlong_transport_comp θ A n
  refine ⟨fun x y => ?_⟩
  have hx : q.hom (p.hom x) = x := by rw [← ModuleCat.comp_apply, hpq]; rfl
  have hy : q.hom (p.hom y) = y := by rw [← ModuleCat.comp_apply, hpq]; rfl
  rw [← hx, ← hy, Subsingleton.elim (p.hom x) (p.hom y)]

theorem cohDict {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hc : ContAction rhoS) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
      (_ : IsDiscreteRep A), Finite A.V ∧ (∀ a : A.V, (l ^ r) • a = 0) ∧
      Nonempty (H1 rhoS ≃+ cohomology A 1) ∧ Nonempty (H2 rhoS ≃+ cohomology A 2) ∧
      ∀ n : ℕ, Nonempty (Hn rhoS n ≃+ cohomology A n) := by
  obtain ⟨e0⟩ := gsEquiv F Ω (S : Set (HeightOneSpectrum (𝓞 F)))
  let e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := e0.symm
  have hc' := ReciprocityTheory.Neutral.Bridge.contAction_comp e hc
  let rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))
  obtain ⟨A, hA, eA, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'
  have hAf : Finite A.V := Finite.of_equiv _ eA.toEquiv
  have hn : ∀ a : A.V, (l ^ r) • a = 0 := by
    intro a
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  refine ⟨A, hA, hAf, hn, ⟨t1.toAddEquiv.trans e1⟩, ⟨t2.toAddEquiv.trans e2⟩, fun n => ?_⟩
  obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn _ (ZMod (l ^ r)) M rho' A eA he n
  exact ⟨(ReciprocityTheory.Neutral.Bridge.isoHn e rhoS rho' (fun _ _ => rfl) n).toAddEquiv.trans en⟩

end PositivityTheory.Lit1.GFTransport
