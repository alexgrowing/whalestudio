import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.DefsForms
import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.RatioOneKilled
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Transport

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_dictfwd_b

theorem eulerChar_eq_div {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] :
    eulerChar A = (Nat.card (cohomology A 0) : ℚ) * Nat.card (cohomology A 2) /
      Nat.card (cohomology A 1) := by
  unfold eulerChar
  simp [Finset.prod_range_succ, div_eq_mul_inv]
  ring

open scoped Classical in

theorem natEq_of_gsEulerRatio_eq_one {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
      AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)) [IsDiscreteRep A]
    [Finite A] (h : gsEulerRatio S A ιr = 1) :
    Nat.card (cohomology A 0) * Nat.card (cohomology A 2) * Nat.card A ^ Module.finrank ℚ K.1 =
      Nat.card (cohomology A 1) *
        ((∏ v : {v : InfinitePlace K.1 // v.IsReal}, gsRealH0Card S A ιr v) *
          Nat.card A ^ InfinitePlace.nrComplexPlaces K.1) := by
  have hP : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S A ιr v : ℚ)) ≠ 0 :=
    (Finset.prod_pos fun v _ => by exact_mod_cast gsRealH0Card_pos S A ιr v).ne'
  have hn : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  unfold gsEulerRatio at h
  rw [eulerChar_eq_div] at h
  have hcard : Fintype.card (InfinitePlace K.1) =
      InfinitePlace.nrRealPlaces K.1 + InfinitePlace.nrComplexPlaces K.1 :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K.1
  have hrank : Module.finrank ℚ K.1 =
      InfinitePlace.nrRealPlaces K.1 + 2 * InfinitePlace.nrComplexPlaces K.1 :=
    (InfinitePlace.card_add_two_mul_card_eq_rank K.1).symm
  rw [hcard] at h
  rw [hrank]
  set a : ℚ := ((Nat.card (cohomology A 0) : ℕ) : ℚ)
  set b : ℚ := ((Nat.card (cohomology A 1) : ℕ) : ℚ)
  set c : ℚ := ((Nat.card (cohomology A 2) : ℕ) : ℚ)
  set n : ℚ := ((Nat.card A : ℕ) : ℚ)
  set P : ℚ := ∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S A ιr v : ℚ)
  have hb : b ≠ 0 := by
    intro hb0
    rw [hb0, div_zero, zero_mul, zero_div] at h
    exact zero_ne_one h
  have key : a * c * n ^ (InfinitePlace.nrRealPlaces K.1 + InfinitePlace.nrComplexPlaces K.1) = b * P := by
    field_simp at h
    linarith [h]
  have : (a * c * n ^ (InfinitePlace.nrRealPlaces K.1 + 2 * InfinitePlace.nrComplexPlaces K.1) : ℚ) =
      b * (P * n ^ InfinitePlace.nrComplexPlaces K.1) := by
    rw [show InfinitePlace.nrRealPlaces K.1 + 2 * InfinitePlace.nrComplexPlaces K.1 =
      (InfinitePlace.nrRealPlaces K.1 + InfinitePlace.nrComplexPlaces K.1) +
        InfinitePlace.nrComplexPlaces K.1 by ring, pow_add, ← mul_assoc, key]
    ring
  apply Nat.cast_injective (R := ℚ)
  push_cast
  exact this

theorem mem_Zn_zero_iff {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (rho : Representation R G M) (f : (Fin 0 → G) → M) :
    f ∈ ReciprocityTheory.Gal.Zn rho 0 ↔ ∀ g, rho g (f Fin.elim0) = f Fin.elim0 := by
  have hc : Continuous f := continuous_of_discreteTopology
  have e : ∀ (j : Fin 1) (g' : Fin 1 → G), Fin.contractNth j (· * ·) g' = Fin.elim0 :=
    fun _ _ => Subsingleton.elim _ _
  have key : ∀ g' : Fin 1 → G, ReciprocityTheory.Gal.dn rho 0 f g' = rho (g' 0) (f Fin.elim0) - f Fin.elim0 := by
    intro g'
    rw [ReciprocityTheory.Gal.dn_apply]
    have e1 : (fun i : Fin 0 => g' i.succ) = Fin.elim0 := Subsingleton.elim _ _
    simp only [e1, e, Fin.sum_univ_one]
    simp [sub_eq_add_neg]
  constructor
  · rintro ⟨_, hk⟩ g
    have h1 := congrFun (LinearMap.mem_ker.1 hk) (fun _ => g)
    rw [key] at h1
    exact sub_eq_zero.1 h1
  · intro h
    refine ⟨hc, LinearMap.mem_ker.2 (funext fun g => ?_)⟩
    rw [key, h (g 0), sub_self]
    rfl

theorem card_H0_eq_card_Hn_zero_alt {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] (rho : Representation R G M) :
    Nat.card (ReciprocityTheory.Gal.H0 rho) = Nat.card (ReciprocityTheory.Gal.Hn rho 0) := by
  have hbot : (ReciprocityTheory.Gal.Bn rho 0).comap (ReciprocityTheory.Gal.Zn rho 0).subtype = ⊥ := by
    show (⊥ : Submodule R _).comap _ = ⊥
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  have e1 : ReciprocityTheory.Gal.Hn rho 0 ≃ ReciprocityTheory.Gal.Zn rho 0 :=
    (Submodule.quotEquivOfEqBot _ hbot).toEquiv
  rw [Nat.card_congr e1]
  refine Nat.card_congr
    { toFun := fun m => ⟨fun _ => m.1, (mem_Zn_zero_iff rho _).2 fun g => m.2 g⟩
      invFun := fun f => ⟨f.1 Fin.elim0, fun g => ((mem_Zn_zero_iff rho f.1).1 f.2) g⟩
      left_inv := fun m => rfl
      right_inv := fun f => Subtype.ext (funext fun x => by
        simp only
        rw [Subsingleton.elim x Fin.elim0]) }

section DictA

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

noncomputable def resS (S : Set (HeightOneSpectrum (𝓞 F))) : G F Ω →* galUnramifiedOutside F Ω S :=
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside F Ω S)

noncomputable def gsIso (S : Set (HeightOneSpectrum (𝓞 F))) :
    GS Ω S ≃ₜ* galUnramifiedOutside F Ω S := by
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
  exact { q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }

theorem gsIso_toGS (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω) :
    gsIso (Ω := Ω) S (toGS Ω S g) = resS S g := by
  rfl

theorem gsIso_symm_resS (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω) :
    (gsIso (Ω := Ω) S).symm (resS S g) = toGS Ω S g := by
  rw [← gsIso_toGS, ContinuousMulEquiv.symm_apply_apply]

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
  let e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) := (gsIso (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F)))).symm
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
  obtain ⟨e0, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  have hH0 : H0 rho' = H0 rhoS := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      obtain ⟨g', rfl⟩ := e.surjective g
      exact h g'
    · intro h g
      exact h (e g)
  refine ⟨A, hA, hAf, hn, (Nat.card_congr eA.toEquiv).symm, ?_, ?_, ?_, fun g => ?_⟩
  · rw [← Nat.card_congr e0.toEquiv, hH0]
  · exact (Nat.card_congr (t1.toAddEquiv.trans e1).toEquiv).symm
  · exact (Nat.card_congr (t2.toAddEquiv.trans e2).toEquiv).symm
  · have hg : e (resS (S : Set (HeightOneSpectrum (𝓞 F))) g) = toGS Ω _ g :=
      gsIso_symm_resS _ g
    refine (Nat.card_congr (Equiv.subtypeEquiv eA.toEquiv fun m => ?_)).symm
    change rhoS (toGS Ω _ g) m = m ↔ A.ρ (resS _ g) (eA m) = eA m
    rw [← he, eA.apply_eq_iff_eq]
    change rhoS (toGS Ω _ g) m = m ↔ rhoS (e (resS _ g)) m = m
    rw [hg]

theorem isCCAt_conj {w : InfinitePlace F} (hw : w.IsReal) {c c' : G F Ω} (hc : IsCCAt w c)
    (hc' : IsCCAt w c') : ∃ g : G F Ω, c' = g * c * g⁻¹ := by
  obtain ⟨j, hj, hjw⟩ := hc
  obtain ⟨j', hj', hj'w⟩ := hc'
  have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap F Ω)) := by
    rw [← InfinitePlace.isReal_mk_iff, hjw]
    exact hw
  have hres : j'.comp (algebraMap F Ω) = j.comp (algebraMap F Ω) := by
    rcases InfinitePlace.mk_eq_iff.1 (hj'w.trans hjw.symm) with h | h
    · exact h
    · calc j'.comp (algebraMap F Ω)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (j'.comp (algebraMap F Ω))) :=
            by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
        _ = ComplexEmbedding.conjugate (j.comp (algebraMap F Ω)) := by rw [h]
        _ = j.comp (algebraMap F Ω) := ComplexEmbedding.isReal_iff.1 hreal
  let _ : Algebra Ω ℂ := j.toAlgebra
  let _ : Algebra F ℂ := (j.comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Normal F Ω := IsAlgClosure.normal F Ω
  let J' : Ω →ₐ[F] ℂ := { j' with commutes' := fun x => RingHom.congr_fun hres x }
  let σ : Gal(Ω/F) := Normal.algHomEquivAut F ℂ Ω J'
  have hσ : ∀ x, j (σ x) = j' x := fun x =>
    congrArg (fun f : Ω →ₐ[F] ℂ => f x) ((Normal.algHomEquivAut F ℂ Ω).symm_apply_apply J')
  have key : σ * c' = c * σ := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    show j (σ (c' x)) = j (c (σ x))
    rw [hσ, hj', hj, hσ]
  refine ⟨σ⁻¹, ?_⟩
  calc c' = σ⁻¹ * (σ * c') := by group
    _ = σ⁻¹ * (c * σ) := by rw [key]
    _ = σ⁻¹ * c * σ⁻¹⁻¹ := by group

theorem comap_comap' {k L N : Type*} [Field k] [Field L] [Field N] (w : InfinitePlace N)
    (f : L →+* N) (g : k →+* L) : (w.comap f).comap g = w.comap (f.comp g) := by
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.comap_mk,
    InfinitePlace.comap_mk]
  rfl

theorem realPlaces_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ)) :
    ∃ e : {w : InfinitePlace F // w.IsReal} ≃ {v : InfinitePlace K.1 // v.IsReal},
      Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace K.1) ∧
      ∀ (w : {w : InfinitePlace F // w.IsReal}) (g : G F Ω) (g' : G K.1 (AlgebraicClosure ℚ)),
        (∀ x : Ω, g' (τ x) = τ (g x)) → IsCCAt (e w).1 g' → IsCCAt w.1 g := by
  have h1 : ∀ w : InfinitePlace F, (w.comap (σ.symm : K.1 →+* F)).comap (σ : F →+* K.1) = w := by
    intro w
    rw [comap_comap']
    have : (σ.symm : K.1 →+* F).comp (σ : F →+* K.1) = RingHom.id F := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]
  have h2 : ∀ v : InfinitePlace K.1, (v.comap (σ : F →+* K.1)).comap (σ.symm : K.1 →+* F) = v := by
    intro v
    rw [comap_comap']
    have : (σ : F →+* K.1).comp (σ.symm : K.1 →+* F) = RingHom.id K.1 := by
      ext x
      simp
    rw [this, InfinitePlace.comap_id]
  let eP : InfinitePlace F ≃ InfinitePlace K.1 :=
    ⟨fun w => w.comap (σ.symm : K.1 →+* F), fun v => v.comap (σ : F →+* K.1), h1, h2⟩
  refine ⟨eP.subtypeEquiv fun w => (InfinitePlace.isReal_comap_iff σ.symm).symm,
    Fintype.card_congr eP, ?_⟩
  rintro w g g' hgg' ⟨j, hj, hjw⟩
  refine ⟨j.comp τ.toRingHom, fun x => ?_, ?_⟩
  · show j (τ (g x)) = starRingEnd ℂ (j (τ x))
    rw [← hgg', hj]
  · have : (j.comp τ.toRingHom).comp (algebraMap F Ω) =
        (j.comp (algebraMap K.1 (AlgebraicClosure ℚ))).comp (σ : F →+* K.1) := by
      ext x
      show j (τ (algebraMap F Ω x)) = j (algebraMap K.1 (AlgebraicClosure ℚ) (σ x))
      rw [hτ]
      rfl
    rw [this, ← InfinitePlace.comap_mk, hjw]
    exact h1 w.1

theorem places_transport (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (S' : Set (HeightOneSpectrum (𝓞 K.1))) (_ : S'.Finite),
      (∀ n : ℕ, (∀ v : HeightOneSpectrum (𝓞 F), (n : 𝓞 F) ∈ v.asIdeal → v ∈ S) →
        ∀ v' : HeightOneSpectrum (𝓞 K.1), (n : 𝓞 K.1) ∈ v'.asIdeal → v' ∈ S') ∧
      ∀ x : Ω, x ∈ maxUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ↔
        τ x ∈ maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S' := by
  haveI : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  classical
  have he : ∀ x : F, τ (algebraMap F Ω x) = algebraMap K.1 (AlgebraicClosure ℚ) (σ x) :=
    fun x => (hτ x).trans rfl
  let T : Finset (HeightOneSpectrum (𝓞 K.1)) :=
    S.map (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv σ)).toEmbedding
  have hC : GlobalTheory.CompanionTheory.GSCd.Transport.Corr σ (S : Set (HeightOneSpectrum (𝓞 F)))
      (T : Set (HeightOneSpectrum (𝓞 K.1))) := by
    intro v
    simp [T]
  refine ⟨(T : Set (HeightOneSpectrum (𝓞 K.1))), T.finite_toSet, fun n hn w hw => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · have hv : (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv (RingOfIntegers.mapRingEquiv σ)).symm w ∈ S := by
      apply hn
      change RingOfIntegers.mapRingEquiv σ (n : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hw
    exact Finset.mem_coe.2 (Finset.mem_map.2 ⟨_, hv, (GlobalTheory.CompanionTheory.GSCd.Transport.placeEquiv _).apply_symm_apply w⟩)
  · exact GlobalTheory.CompanionTheory.GSCd.Transport.mem_max σ τ he hC hx
  · have := GlobalTheory.CompanionTheory.GSCd.Transport.mem_max σ.symm τ.symm (GlobalTheory.CompanionTheory.GSCd.Transport.symm_compat σ τ he)
      hC.symm hx
    rwa [RingEquiv.symm_apply_apply] at this

theorem exists_transport_elem (K : FiniteSubfield) (τ : Ω ≃+* AlgebraicClosure ℚ) (σ : F ≃+* K.1)
    (hτ : ∀ x : F, τ (algebraMap F Ω x) = ((σ x : K.1) : AlgebraicClosure ℚ))
    (g' : G K.1 (AlgebraicClosure ℚ)) : ∃ g : G F Ω, ∀ x : Ω, g' (τ x) = τ (g x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (τ.trans g'.toRingEquiv).trans τ.symm) fun r => ?_, fun x => ?_⟩
  · show τ.symm (g' (τ (algebraMap F Ω r))) = algebraMap F Ω r
    rw [hτ]
    have h1 : g' ((σ r : K.1) : AlgebraicClosure ℚ) = ((σ r : K.1) : AlgebraicClosure ℚ) :=
      g'.commutes (σ r)
    rw [h1, ← hτ, RingEquiv.symm_apply_apply]
  · show g' (τ x) = τ (τ.symm (g' (τ x)))
    rw [RingEquiv.apply_symm_apply]

end DictA

section Arch

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

theorem real_H0_card_eq_fixed_of_gen (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal})
    (s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (hs : ∀ g, g = 1 ∨ g = s)
    (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S')) [IsDiscreteRep B] :
    gsRealH0Card S' B ιr v = Nat.card {b : B // B.ρ (gsRealFamily S' ιr v s) b = b} := by
  unfold gsRealH0Card
  rw [Nat.card_congr (H0Iso _).toLinearEquiv.toEquiv]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  change (∀ g, B.ρ (gsRealFamily S' ιr v g) b = b) ↔ B.ρ (gsRealFamily S' ιr v s) b = b
  refine ⟨fun h => h s, fun h g => ?_⟩
  rcases hs g with hg | hg
  · rw [hg, map_one, map_one]
    rfl
  · rw [hg]
    exact h

set_option maxHeartbeats 1600000 in

theorem exists_cc_gen (K : FiniteSubfield) (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ (κ : AlgebraicClosure v.1.Completion →+* ℂ) (s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)),
      (∀ y, κ (s y) = starRingEnd ℂ (κ y)) ∧ (∀ g, g = 1 ∨ g = s) ∧
      ∀ x : K.1, κ (algebraMap K.1 (AlgebraicClosure v.1.Completion) x) = v.1.embedding x := by
  have hv : v.1.IsReal := v.2
  let ρ := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let φ : v.1.Completion →+* ℂ := Complex.ofRealHom.comp ρ.toRingHom
  let _ : Algebra v.1.Completion ℂ := φ.toAlgebra
  let κA : AlgebraicClosure v.1.Completion →ₐ[v.1.Completion] ℂ := IsAlgClosed.lift
  have hκr : ∀ r : v.1.Completion, κA (algebraMap v.1.Completion _ r) = (ρ r : ℂ) := fun r =>
    κA.commutes r

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    ((Polynomial.X ^ 2 + 1 : Polynomial (AlgebraicClosure v.1.Completion)))
    (by rw [← Polynomial.C_1, Polynomial.degree_X_pow_add_C (by norm_num : 0 < 2)]; norm_num)
  have hy2 : κA y ^ 2 = -1 := by
    have h := congrArg κA (show y ^ 2 + 1 = 0 by simpa using hy)
    rw [map_add, map_pow, map_one, map_zero] at h
    linear_combination h
  have hsurj : Function.Surjective κA := by
    intro z
    have hI : ∃ t, κA t = Complex.I := by
      have : (κA y - Complex.I) * (κA y + Complex.I) = 0 := by
        calc (κA y - Complex.I) * (κA y + Complex.I) = κA y ^ 2 - Complex.I ^ 2 := by ring
          _ = 0 := by rw [hy2, Complex.I_sq]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact ⟨y, sub_eq_zero.1 h⟩
      · exact ⟨-y, by rw [map_neg]; linear_combination -h⟩
    obtain ⟨t, ht⟩ := hI
    refine ⟨algebraMap v.1.Completion _ (ρ.symm z.re) + algebraMap v.1.Completion _ (ρ.symm z.im) * t, ?_⟩
    rw [map_add, map_mul, hκr, hκr, ht, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact Complex.re_add_im z
  let e : AlgebraicClosure v.1.Completion ≃+* ℂ :=
    RingEquiv.ofBijective κA.toRingHom ⟨κA.toRingHom.injective, hsurj⟩
  have he : ∀ t, e t = κA t := fun _ => rfl
  have hreal : ∀ r : v.1.Completion, e.symm (ρ r : ℂ) = algebraMap v.1.Completion _ r := by
    intro r
    rw [e.symm_apply_eq, he, hκr]
  let s : Gal(AlgebraicClosure v.1.Completion / v.1.Completion) :=
    { toRingEquiv := (e.trans (starRingAut : ℂ ≃+* ℂ)).trans e.symm
      commutes' := fun r => by
        show e.symm (starRingEnd ℂ (e (algebraMap v.1.Completion _ r))) = algebraMap v.1.Completion _ r
        rw [he, hκr, Complex.conj_ofReal, hreal] }
  have hs : ∀ t, κA (s t) = starRingEnd ℂ (κA t) := by
    intro t
    show e (e.symm ((starRingAut : ℂ ≃+* ℂ) (e t))) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  refine ⟨κA.toRingHom, s, hs, fun g => ?_, fun x => ?_⟩
  · let f : ℂ →ₐ[ℝ] ℂ :=
      { toRingHom := (e.symm.trans (g.toRingEquiv.trans e)).toRingHom
        commutes' := fun a => by
          show e (g (e.symm (Complex.ofReal a))) = Complex.ofReal a
          have : (Complex.ofReal a) = (ρ (ρ.symm a) : ℂ) := by rw [RingEquiv.apply_symm_apply]
          rw [this, hreal, AlgEquiv.commutes, he, hκr] }
    rcases Complex.real_algHom_eq_id_or_conj f with hf | hf
    · left
      ext t
      apply e.injective
      have := congrArg (fun F : ℂ →ₐ[ℝ] ℂ => F (e t)) hf
      simpa [f] using this
    · right
      ext t
      apply e.injective
      have := congrArg (fun F : ℂ →ₐ[ℝ] ℂ => F (e t)) hf
      simp only [f] at this
      rw [he (s t), hs]
      simp at this
      exact this
  · have hsc : algebraMap K.1 (AlgebraicClosure v.1.Completion) x =
        algebraMap v.1.Completion (AlgebraicClosure v.1.Completion) (algebraMap K.1 v.1.Completion x) :=
      IsScalarTower.algebraMap_apply _ _ _ x
    show κA (algebraMap K.1 (AlgebraicClosure v.1.Completion) x) = _
    rw [hsc, hκr, InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← InfinitePlace.embedding_of_isReal_apply hv]
    congr 1
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv _

theorem real_H0_card_eq_fixed (K : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
        AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) :
    ∃ cc : G K.1 (AlgebraicClosure ℚ), IsCCAt v.1 cc ∧
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S'))
        [IsDiscreteRep B], gsRealH0Card S' B ιr v =
          Nat.card {b : B // B.ρ (resS (Ω := AlgebraicClosure ℚ) S' cc) b = b} := by
  obtain ⟨κ, s, hκs, hs, hκK⟩ := exists_cc_gen K v
  refine ⟨decompHom v.1.Completion (ιr v) s, ⟨κ.comp (ιr v).toRingHom, fun x => ?_, ?_⟩, fun B _ => ?_⟩
  · show κ (ιr v (decompHom v.1.Completion (ιr v) s x)) = starRingEnd ℂ (κ (ιr v x))
    rw [decompHom_apply, hκs]
  · have : (κ.comp (ιr v).toRingHom).comp (algebraMap K.1 (AlgebraicClosure ℚ)) = v.1.embedding := by
      ext x
      show κ (ιr v (algebraMap K.1 (AlgebraicClosure ℚ) x)) = v.1.embedding x
      rw [AlgHom.commutes, hκK]
    rw [this, InfinitePlace.mk_embedding]
  · rw [real_H0_card_eq_fixed_of_gen K S' ιr v s hs B]
    have hfam : gsRealFamily S' ιr v s = resS (Ω := AlgebraicClosure ℚ) S' (decompHom v.1.Completion (ιr v) s) := by
      show decompHomS v.1.Completion S' (ιr v) s = _
      rw [decompHomS_eq]
      rfl
    simp only [hfam]

end Arch

end PositivityTheory.Lit1.GEN.W_dictfwd_b
