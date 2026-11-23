import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.Narrow
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkDictfwdB

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GEN.W_dictfwd_a

noncomputable section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def resS (S : Set (HeightOneSpectrum (𝓞 F))) : G F Ω →* galUnramifiedOutside F Ω S :=
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside F Ω S)

theorem card_fix_conj {k Γ : Type} [CommRing k] [Group Γ] (A : Rep.{0} k Γ) (g c : Γ) :
    Nat.card {a : A // A.ρ (g * c * g⁻¹) a = a} = Nat.card {a : A // A.ρ c a = a} := by
  have key : ∀ x y : Γ, ∀ a : A, A.ρ x (A.ρ y a) = A.ρ (x * y) a := fun x y a => by
    rw [map_mul, Module.End.mul_apply]
  refine Nat.card_congr
    { toFun := fun a => ⟨A.ρ g⁻¹ a.1, ?_⟩
      invFun := fun a => ⟨A.ρ g a.1, ?_⟩
      left_inv := fun a => Subtype.ext ?_
      right_inv := fun a => Subtype.ext ?_ }
  · conv_rhs => rw [← a.2]
    rw [key, key]
    congr 1
    group
  · conv_rhs => rw [← a.2]
    rw [key, key]
    congr 1
    group
  · show A.ρ g (A.ρ g⁻¹ a.1) = a.1
    rw [key, mul_inv_cancel, map_one, Module.End.one_apply]
  · show A.ρ g⁻¹ (A.ρ g a.1) = a.1
    rw [key, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isCCAt_conj {w : InfinitePlace F} (hw : w.IsReal) {c c' : G F Ω} (hc : IsCCAt w c)
    (hc' : IsCCAt w c') : ∃ g : G F Ω, c' = g * c * g⁻¹ := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.isCCAt_conj hw hc hc'

theorem exists_fieldTransport :
    ∃ (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1),
      ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ) := by
  let σ0 : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let K : FiniteSubfield := ⟨σ0.fieldRange,
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ0).toLinearEquiv⟩
  letI : Algebra F (AlgebraicClosure ℚ) := σ0.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun q => (σ0.commutes q).symm
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosure F (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  let τ : Ω ≃ₐ[F] AlgebraicClosure ℚ := IsAlgClosure.equiv F Ω (AlgebraicClosure ℚ)
  refine ⟨K, τ.toRingEquiv, (AlgEquiv.ofInjectiveField σ0).toRingEquiv, fun x => ?_⟩
  show τ (algebraMap F Ω x) = _
  rw [τ.commutes]
  rfl

theorem places_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.places_transport K τ σ hτ S

def tauE (τ : Ω ≃+* AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 F))) {K : FiniteSubfield}
    (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    maxUnramifiedOutside F Ω S ≃+* maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' where
  toFun x := ⟨τ (x : Ω), (hmem x).1 x.2⟩
  invFun y := ⟨τ.symm y, (hmem _).2 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply (x : Ω))
  right_inv y := Subtype.ext (τ.apply_symm_apply (y : AlgebraicClosure ℚ))
  map_mul' x y := Subtype.ext (map_mul τ (x : Ω) y)
  map_add' x y := Subtype.ext (map_add τ (x : Ω) y)

def galTransport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    galUnramifiedOutside F Ω S ≃* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' where
  toFun h := AlgEquiv.ofRingEquiv (f := (tauE τ S S' hmem).symm.trans (h.toRingEquiv.trans (tauE τ S S' hmem)))
    fun k => Subtype.ext (by
      show τ ((h ⟨τ.symm k, _⟩ : maxUnramifiedOutside F Ω S) : Ω) = (k : AlgebraicClosure ℚ)
      have hk : τ.symm (k : AlgebraicClosure ℚ) = algebraMap F Ω (σ.symm k) := by
        rw [τ.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]
      have : (⟨τ.symm k, (hmem _).2 (by rw [RingEquiv.apply_symm_apply]; exact (algebraMap K.1 (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') k).2)⟩ :
          maxUnramifiedOutside F Ω S) = algebraMap F (maxUnramifiedOutside F Ω S) (σ.symm k) :=
        Subtype.ext hk
      rw [this, h.commutes]
      show τ (algebraMap F Ω (σ.symm k)) = _
      rw [hτ, RingEquiv.apply_symm_apply])
  invFun h' := AlgEquiv.ofRingEquiv (f := (tauE τ S S' hmem).trans (h'.toRingEquiv.trans (tauE τ S S' hmem).symm))
    fun x => Subtype.ext (by
      show τ.symm ((h' ⟨τ (algebraMap F Ω x), _⟩ : maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
        AlgebraicClosure ℚ) = algebraMap F Ω x
      have : (⟨τ (algebraMap F Ω x), (hmem _).1 (algebraMap F (maxUnramifiedOutside F Ω S) x).2⟩ :
          maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') =
          algebraMap K.1 (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') (σ x) :=
        Subtype.ext (hτ x)
      rw [this, h'.commutes, τ.symm_apply_eq, hτ]
      rfl)
  left_inv h := by ext x; simp [tauE]
  right_inv h' := by ext y; simp [tauE]
  map_mul' a b := by ext y; simp [tauE]

theorem continuous_galTransport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    Continuous (galTransport K τ σ hτ S S' hmem) ∧ Continuous (galTransport K τ σ hτ S S' hmem).symm := by
  have hc : Continuous (galTransport K τ σ hτ S S' hmem) := by
    let f : galUnramifiedOutside F Ω S →* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' :=
      (galTransport K τ σ hτ S S' hmem).toMonoidHom
    change Continuous f
    refine continuous_of_continuousAt_one f ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨K0, hK0, hK0s⟩ := (krullTopology_mem_nhds_one_iff K.1 _ s).1 hs
    classical
    let b := Module.finBasis K.1 K0
    let L0 : IntermediateField F (maxUnramifiedOutside F Ω S) :=
      IntermediateField.adjoin F (Set.range fun i => (tauE τ S S' hmem).symm (b i : _))
    have hL0 : FiniteDimensional F L0 :=
      IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
    rw [Filter.mem_map]
    refine Filter.mem_of_superset
      ((krullTopology_mem_nhds_one_iff F _ _).2 ⟨L0, hL0, le_rfl⟩) fun h hh => hK0s ?_
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
    have hb : ∀ i, f h (b i : _) = b i := fun i => by
      change (tauE τ S S' hmem) (h ((tauE τ S S' hmem).symm (b i : _))) = _
      rw [hh _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩), RingEquiv.apply_symm_apply]
    intro y hy
    have key := b.ext (f₁ := (f h).toLinearMap ∘ₗ K0.val.toLinearMap) (f₂ := K0.val.toLinearMap)
      fun i => hb i
    exact LinearMap.congr_fun key ⟨y, hy⟩
  exact ⟨hc, Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (galTransport K τ σ hτ S S' hmem).toEquiv) hc⟩

theorem galEquiv_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (hmem : ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω S ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') :
    ∃ θ : galUnramifiedOutside F Ω S ≃ₜ* galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S',
      ∀ (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)), (∀ x : Ω, g' (τ x) = τ (g x)) →
        θ (resS (Ω := Ω) S g) = resS (Ω := AlgebraicClosure ℚ) S' g' := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  obtain ⟨h1, h2⟩ := continuous_galTransport K τ σ hτ S S' hmem
  refine ⟨{ galTransport K τ σ hτ S S' hmem with continuous_toFun := h1, continuous_invFun := h2 },
    fun g g' hg => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  show τ ((g.restrictNormal (maxUnramifiedOutside F Ω S) ((tauE τ S S' hmem).symm y) : Ω)) =
    ((g'.restrictNormal (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') y :
      maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') : AlgebraicClosure ℚ)
  have e1 := AlgEquiv.restrictNormal_commutes g (maxUnramifiedOutside F Ω S) ((tauE τ S S' hmem).symm y)
  have e2 := AlgEquiv.restrictNormal_commutes g' (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S') y
  simp only [IntermediateField.algebraMap_apply] at e1 e2
  rw [e1, e2, ← hg]
  show g' (τ (τ.symm (y : AlgebraicClosure ℚ))) = _
  rw [RingEquiv.apply_symm_apply]

theorem gsTransport_compat (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite)
      (θ : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)), (∀ x : Ω, g' (τ x) = τ (g x)) →
        θ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) g) =
          resS (Ω := AlgebraicClosure ℚ) S' g' := by
  obtain ⟨S', hS', hn, hmem⟩ := places_transport K τ σ hτ S
  obtain ⟨θ, hθ⟩ := galEquiv_transport K τ σ hτ _ S' hmem
  exact ⟨S', hS', θ, hn, hθ⟩

theorem exists_transport_elem (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (g' : G K.1 (AlgebraicClosure ℚ)) : ∃ g : G F Ω, ∀ x : Ω, g' (τ x) = τ (g x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := τ.trans (g'.toRingEquiv.trans τ.symm)) fun x => ?_, fun x => ?_⟩
  · show τ.symm (g' (τ (algebraMap F Ω x))) = algebraMap F Ω x
    rw [hτ, τ.symm_apply_eq, hτ]
    exact g'.commutes (σ x)
  · show g' (τ x) = τ (τ.symm (g' (τ x)))
    rw [RingEquiv.apply_symm_apply]

theorem realPlaces_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ)) :
    ∃ e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal},
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (w : {w : InfinitePlace F // w.IsReal}) (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)),
        (∀ x : Ω, g' (τ x) = τ (g x)) → IsCCAt (e w).1 g' → IsCCAt w.1 g := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.realPlaces_transport K τ σ hτ

theorem real_H0_card_eq_fixed (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ cc : G K.1 (AlgebraicClosure ℚ), IsCCAt v.1 cc ∧
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'))
        [IsDiscreteRep B], gsRealH0Card S' B ιr v =
          Nat.card {b : B // B.ρ (resS (Ω := AlgebraicClosure ℚ) S' cc) b = b} := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.real_H0_card_eq_fixed K S' ιr v

open scoped Classical in

theorem transport_data {l : ℕ} [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ContainsAbove S l) :
    ∃ (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite)
      (θ : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
        galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S')
      (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
      (c' : InfinitePlace F → G F Ω)
      (e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal}),
      (∀ v : HeightOneSpectrum (𝓞 K.1), ((l : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S') ∧
      (∀ w, w.IsReal → IsCCAt w (c' w)) ∧
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
        [IsDiscreteRep A] (w : {w : InfinitePlace F // w.IsReal}),
        haveI := IsDiscreteRep.res (φ := θ.symm.toMulEquiv.toMonoidHom) θ.symm.continuous A
        gsRealH0Card S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr (e w) =
          Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1)) a = a} := by
  obtain ⟨K, τ, σ, hτ⟩ := exists_fieldTransport (F := F) (Ω := Ω)
  obtain ⟨S', hS', θ, hn, hθ⟩ := gsTransport_compat K τ σ hτ S
  obtain ⟨e, hcard, hcc⟩ := realPlaces_transport K τ σ hτ
  let ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
      AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion := fun v => IsAlgClosed.lift
  choose cc hccv hfixv using fun v => real_H0_card_eq_fixed K S' ιr v
  choose g hg using fun v => exists_transport_elem K τ σ hτ (cc v)
  refine ⟨K, S', hS', θ, ιr, fun w => if hw : w.IsReal then g (e ⟨w, hw⟩) else 1, e,
    hn l hS, fun w hw => ?_, hcard, fun A _ w => ?_⟩
  · simp only [dif_pos hw]
    exact hcc ⟨w, hw⟩ _ _ (hg _) (hccv _)
  · rw [hfixv (e w)]
    simp only [dif_pos w.2, Subtype.coe_eta]
    rw [← hθ _ _ (hg (e w))]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    show A.ρ (θ.symm (θ _)) a = a ↔ _
    rw [ContinuousMulEquiv.symm_apply_apply]

open scoped Classical in

theorem ratio_F_exists {l : ℕ} [Fact l.Prime] (h : RatioOne l (fun _ => True))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l) :
    ∃ c' : InfinitePlace F → G F Ω, (∀ w, w.IsReal → IsCCAt w (c' w)) ∧
      ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
        [IsDiscreteRep A] [Finite A] (r : ℕ), (∀ a : A, (l ^ r) • a = 0) →
        eulerChar A * (Nat.card A : ℚ) ^ Fintype.card (InfinitePlace F) =
          ∏ w : {w : InfinitePlace F // w.IsReal},
            (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1)) a = a} : ℚ) := by
  obtain ⟨K, S', hS', θ, ιr, c', e, hl, hc', hcard, hfix⟩ := transport_data (Ω := Ω) S hS
  refine ⟨c', hc', fun A _ _ r hA => ?_⟩
  haveI := IsDiscreteRep.res (φ := θ.symm.toMulEquiv.toMonoidHom) θ.symm.continuous A
  haveI hBf : Finite (Rep.res θ.symm.toMulEquiv.toMonoidHom A) := inferInstanceAs (Finite A)
  have h1 := h K S' hS' hl trivial ιr (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ⟨r, hA⟩
  have hχ := eulerChar_res_continuousMulEquiv θ.symm A
  unfold gsEulerRatio at h1
  have hP : (∏ v : {v : InfinitePlace K.1 // v.IsReal},
      (gsRealH0Card S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr v : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by
      exact_mod_cast (gsRealH0Card_pos S' (Rep.res θ.symm.toMulEquiv.toMonoidHom A) ιr v).ne'
  rw [div_eq_one_iff_eq hP, hχ] at h1
  have hn : Nat.card (Rep.res θ.symm.toMulEquiv.toMonoidHom A) = Nat.card A := rfl
  rw [hn] at h1
  rw [hcard, h1]
  exact (Fintype.prod_equiv e _ _ (fun w => by rw [hfix A w])).symm

open scoped Classical in

theorem ratio_F {l : ℕ} [Fact l.Prime] (h : RatioOne l (fun _ => True))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ContainsAbove S l)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
    [IsDiscreteRep A] [Finite A] (r : ℕ) (hA : ∀ a : A, (l ^ r) • a = 0)
    (c : InfinitePlace F → G F Ω) (hc : ∀ w, w.IsReal → IsCCAt w (c w)) :
    eulerChar A * (Nat.card A : ℚ) ^ Fintype.card (InfinitePlace F) =
      ∏ w : {w : InfinitePlace F // w.IsReal},
        (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c w.1)) a = a} : ℚ) := by
  obtain ⟨c', hc', hrat⟩ := ratio_F_exists (Ω := Ω) h S hS
  rw [hrat A r hA]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain ⟨g, hg⟩ := isCCAt_conj w.2 (hc' w.1 w.2) (hc w.1 w.2)
  have e := card_fix_conj A (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) g)
    (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c' w.1))
  rw [← map_inv, ← map_mul, ← map_mul, ← hg] at e
  rw [e]

theorem dict_A {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hc : ContAction rhoS) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
      (_ : IsDiscreteRep A), Finite A ∧ (∀ a : A, (l ^ r) • a = 0) ∧ Nat.card A = Nat.card M ∧
      Nat.card (cohomology A 0) = Nat.card (H0 rhoS) ∧ Nat.card (cohomology A 1) = Nat.card (H1 rhoS) ∧
      Nat.card (cohomology A 2) = Nat.card (H2 rhoS) ∧
      ∀ g : G F Ω, Nat.card {a : A // A.ρ (resS (S : Set (HeightOneSpectrum (𝓞 F))) g) a = a} =
        Nat.card {m : M // rhoS (toGS Ω _ g) m = m} := by
  exact PositivityTheory.Lit1.GEN.W_dictfwd_b.dict_A S rhoS hc

open scoped Classical in
theorem globalEulerCharAt_of_ratioOne {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (h : RatioOne l (fun _ => True)) : GlobalEulerCharAt S rhoS := by
  intro _ hS hc c hcc
  obtain ⟨A, hAd, hAf, hAt, hcard, h0, h1, h2, hfix⟩ := dict_A S rhoS hc
  have key := ratio_F h S hS A r hAt c hcc
  simp only [eulerChar, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    zpow_one, zpow_neg, neg_one_sq, Int.reduceNeg, hcard, h0, h1, h2] at key
  have hP : ∏ w : {w : InfinitePlace F // w.IsReal},
      (Nat.card {a : A // A.ρ (resS (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (c w.1)) a = a} : ℚ) =
      ((∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m} : ℕ) : ℚ) := by
    rw [Nat.cast_prod, Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal)
      (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)) (fun w => by simp)]
    exact Finset.prod_congr rfl fun w _ => by rw [hfix]
  rw [hP] at key
  have hR := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
  have hI : Fintype.card (InfinitePlace F) =
      InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F :=
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  unfold archH0Card
  rw [← hR]
  rw [hI] at key
  have hpos : 0 < ∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
      Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m} :=
    Finset.prod_pos fun w _ => Nat.card_pos_iff.2 ⟨⟨⟨0, map_zero _⟩⟩, inferInstance⟩
  by_cases hh1 : Nat.card (H1 rhoS) = 0
  · rw [hh1] at key
    simp at key
    exact absurd key.symm (by exact_mod_cast hpos.ne')
  · have hq : ((Nat.card (H0 rhoS) * Nat.card (H2 rhoS) * Nat.card M ^
        (InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F) : ℕ) : ℚ) =
        ((Nat.card (H1 rhoS) * ((∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
          Nat.card {m : M // rhoS (toGS Ω _ (c w)) m = m}) *
          Nat.card M ^ InfinitePlace.nrComplexPlaces F) : ℕ) : ℚ) := by
      push_cast
      rw [← Nat.cast_prod, ← key]
      have : (Nat.card (H1 rhoS) : ℚ) ≠ 0 := by exact_mod_cast hh1
      field_simp
      ring
    exact_mod_cast hq

end

end PositivityTheory.Lit1.GEN.W_dictfwd_a
