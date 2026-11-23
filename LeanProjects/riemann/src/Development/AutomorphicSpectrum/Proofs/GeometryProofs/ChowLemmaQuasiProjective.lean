import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverIsIsoMorphismRestrict
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_lift_of_isDominant {D Y V A : Scheme.{0}} [IsReduced Y] (σ : D ⟶ Y) [IsDominant σ]
    (r : Y ⟶ V) (k : A ⟶ V) [IsClosedImmersion k] (a : D ⟶ A) (h : σ ≫ r = a ≫ k) :
    ∃ φ : Y ⟶ A, φ ≫ k = r := by
  have hl : pullback.lift σ a h ≫ pullback.fst r k = σ := pullback.lift_fst _ _ _
  have : IsDominant (pullback.lift σ a h ≫ pullback.fst r k) := by rw [hl]; infer_instance
  have : IsDominant (pullback.fst r k) := IsDominant.of_comp (pullback.lift σ a h) _
  have : Surjective (pullback.fst r k) :=
    surjective_of_isDominant_of_isClosed_range _ (pullback.fst r k).isClosedEmbedding.isClosed_range
  have : IsIso (pullback.fst r k) := isIso_of_isClosedImmersion_of_surjective _
  exact ⟨inv (pullback.fst r k) ≫ pullback.snd r k, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem isClosedImmersion_morphismRestrict {S X B X' T D : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    (u : B ⟶ S) [IsReduced X'] (π : X' ⟶ X) (b : X' ⟶ B) (hπb : π ≫ f = b ≫ u)
    [IsClosedImmersion (pullback.lift π b hπb)] (A : X.Opens) (O : B.Opens) (τ : T ⟶ S)
    (ρ : O.toScheme ⟶ T) (hρ : ρ ≫ τ = O.ι ≫ u) (k : A.toScheme ⟶ T) [IsClosedImmersion k]
    (hk : k ≫ τ = A.ι ≫ f) (σ : D ⟶ (b ⁻¹ᵁ O).toScheme) [IsDominant σ] (a : D ⟶ A.toScheme)
    (h₁ : σ ≫ b ∣_ O ≫ ρ = a ≫ k) (h₂ : a ≫ A.ι = σ ≫ (b ⁻¹ᵁ O).ι ≫ π) :
    IsClosedImmersion (b ∣_ O) := by
  obtain ⟨φ, hφ⟩ := exists_lift_of_isDominant σ (b ∣_ O ≫ ρ) k a h₁
  have hσφ : σ ≫ φ = a := by
    rw [← cancel_mono k, Category.assoc, hφ, h₁]
  have hφι : φ ≫ A.ι = (b ⁻¹ᵁ O).ι ≫ π := by
    refine ext_of_isDominant_of_isSeparated f ?_ σ ?_
    · rw [Category.assoc, Category.assoc, ← hk, reassoc_of% hφ, hρ, morphismRestrict_ι_assoc,
        hπb]
    · rw [reassoc_of% hσφ, h₂]
  have hc : (pullback.snd ρ k ≫ A.ι) ≫ f = (pullback.fst ρ k ≫ O.ι) ≫ u := by
    rw [Category.assoc, Category.assoc, ← hk, ← hρ, pullback.condition_assoc]
  let c : pullback ρ k ⟶ pullback f u := pullback.lift _ _ hc
  have c₁ : c ≫ pullback.fst f u = pullback.snd ρ k ≫ A.ι := pullback.lift_fst _ _ _
  have c₂ : c ≫ pullback.snd f u = pullback.fst ρ k ≫ O.ι := pullback.lift_snd _ _ _
  have : Mono c := by
    have : Mono (c ≫ pullback.snd f u) := by rw [c₂]; infer_instance
    exact mono_of_mono c (pullback.snd f u)
  let m : (b ⁻¹ᵁ O).toScheme ⟶ pullback ρ k := pullback.lift (b ∣_ O) φ hφ.symm
  have m₁ : m ≫ pullback.fst ρ k = b ∣_ O := pullback.lift_fst _ _ _
  have m₂ : m ≫ pullback.snd ρ k = φ := pullback.lift_snd _ _ _
  have hw : (b ⁻¹ᵁ O).ι ≫ pullback.lift π b hπb = m ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, c₁, reassoc_of% m₂, hφι]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, c₂, reassoc_of% m₁,
        morphismRestrict_ι]
  have sq : IsPullback (b ⁻¹ᵁ O).ι m (pullback.lift π b hπb) c := by
    have hr : ∀ {Z : Scheme.{0}} (x : Z ⟶ X') (y : Z ⟶ pullback ρ k),
        x ≫ pullback.lift π b hπb = y ≫ c → Set.range x ⊆ Set.range (b ⁻¹ᵁ O).ι := by
      intro Z x y e
      have e' : x ≫ b = (y ≫ pullback.fst ρ k) ≫ O.ι := by
        have := congr($e ≫ pullback.snd f u)
        simpa only [Category.assoc, pullback.lift_snd, c₂] using this
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (x ≫ b) z ∈ O
      rw [e']
      exact ((y ≫ pullback.fst ρ k) z).2
    refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
      (fun s ↦ IsOpenImmersion.lift (b ⁻¹ᵁ O).ι s.fst (hr _ _ s.condition)) (fun s ↦ ?_)
      (fun s ↦ ?_) (fun s n h₃ _ ↦ ?_)⟩⟩
    · exact IsOpenImmersion.lift_fac _ _ _
    · rw [← cancel_mono c, Category.assoc, ← hw, IsOpenImmersion.lift_fac_assoc, s.condition]
    · rw [← cancel_mono (b ⁻¹ᵁ O).ι, IsOpenImmersion.lift_fac, h₃]
  have : IsClosedImmersion m := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq ‹_›
  rw [← m₁]
  infer_instance

theorem exists_isProper_surjective_isQProjOver : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (X' : Scheme.{0}) (π : X' ⟶ X), IsProper π ∧ Surjective π ∧ IsQProjOver (π ≫ p) := by
  intro R _ _ X _ f _ _ _
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA : ∀ y : X, ∃ A : X.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set X))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → X.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : X, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    (isAmpleLB_of_isAffine (LB.isLB_triv (A i).toScheme)).isQProjOver ((A i).ι ≫ f))
  choose N j hj _ hjt using hP
  let U : X.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint X ∈ U := by
    have : ∀ i, genericPoint X ∈ A i := fun i ↦
      ((genericPoint_spec X).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : X.Opens ↦ genericPoint X ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have hps : ∀ n, IsProjOver (PSpace.str R n) := fun n ↦ ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨P, s, p, hP, hp, hu⟩ := ProjFinProd.exists_isProjOver_finite_prod R T (Sp R) (𝟙 _)
    (fun i ↦ PSpace R (N i)) (fun i ↦ PSpace.str R (N i))
    ((isAmpleLB_of_isAffine (LB.isLB_triv (Sp R))).isProjOver (𝟙 _)) (fun i ↦ hps _)
  rw [Category.comp_id] at hP hp
  obtain ⟨h, ⟨hs, hh⟩, -⟩ := hu U.toScheme (U.ι ≫ f) (fun i ↦ X.homOfLE (hUA i) ≫ j i)
    (fun i ↦ by rw [Category.assoc, hjt, X.homOfLE_ι_assoc, Category.comp_id])
  have : IsProper s := ((isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hP).1
  let g : U.toScheme ⟶ pullback f s := pullback.lift U.ι h hs.symm
  have g₁ : g ≫ pullback.fst f s = U.ι := pullback.lift_fst _ _ _
  have g₂ : g ≫ pullback.snd f s = h := pullback.lift_snd _ _ _
  have : IsImmersion (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : IsImmersion g := IsImmersion.of_comp g (pullback.fst f s)
  have : QuasiCompact (g ≫ pullback.fst f s) := by rw [g₁]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g (pullback.fst f s)
  have := isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  let π : g.image ⟶ X := g.imageι ≫ pullback.fst f s
  let q : g.image ⟶ P := g.imageι ≫ pullback.snd f s
  have hπ : g.toImage ≫ π = U.ι := by rw [g.toImage_imageι_assoc, g₁]
  have hq : g.toImage ≫ q = h := by rw [g.toImage_imageι_assoc, g₂]
  have hπq : π ≫ f = q ≫ s := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ i, (π ⁻¹ᵁ A i).ι ≫ q ≫ p i = π ∣_ A i ≫ j i := by
    intro i
    obtain ⟨σ, _, e₁, e₂⟩ := GlobalTheory.ChowLemma.exists_dominant_lift π (hUA i) g.toImage hπ
    have := isProper_str R (N i)
    refine ext_of_isDominant_of_isSeparated (PSpace.str R (N i)) ?_ σ ?_
    · rw [Category.assoc, Category.assoc, hp, ← hπq, Category.assoc (π ∣_ A i), hjt,
        morphismRestrict_ι_assoc]
    · rw [reassoc_of% e₁, reassoc_of% hq, hh, reassoc_of% e₂]
  have : ∀ i, IsImmersion (j i) := hj
  let V : ∀ i, (PSpace R (N i)).Opens := fun i ↦ (j i).coborderRange
  have hV : ∀ i (x : g.image), π x ∈ A i → (q ≫ p i) x ∈ V i := by
    intro i x hx
    have e : ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ = (π ∣_ A i ≫ j i) ⟨x, hx⟩ := by rw [key i]
    change ((π ⁻¹ᵁ A i).ι ≫ q ≫ p i) ⟨x, hx⟩ ∈ V i
    rw [e]
    exact subset_coborder ⟨_, rfl⟩
  let W : P.Opens := ⨆ i, p i ⁻¹ᵁ V i
  have hW : Set.range q ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨i, hi⟩ := hcov (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hV i x hi⟩
  let q' : g.image ⟶ W.toScheme := IsOpenImmersion.lift W.ι q hW
  have hq' : q' ≫ W.ι = q := IsOpenImmersion.lift_fac _ _ _
  have hπq' : π ≫ f = q' ≫ W.ι ≫ s := by rw [reassoc_of% hq', hπq]
  have hcl : IsClosedImmersion (pullback.lift π q' hπq') := by
    let e : pullback f (W.ι ≫ s) ⟶ pullback f s :=
      pullback.lift (pullback.fst f (W.ι ≫ s)) (pullback.snd f (W.ι ≫ s) ≫ W.ι)
        (by rw [pullback.condition, Category.assoc])
    have e₁ : e ≫ pullback.fst f s = pullback.fst f (W.ι ≫ s) := pullback.lift_fst _ _ _
    have e₂ : e ≫ pullback.snd f s = pullback.snd f (W.ι ≫ s) ≫ W.ι := pullback.lift_snd _ _ _
    have : Mono e := by
      refine ⟨fun a b hab ↦ pullback.hom_ext ?_ ?_⟩
      · simpa only [Category.assoc, e₁] using congr($hab ≫ pullback.fst f s)
      · rw [← cancel_mono W.ι]
        simpa only [Category.assoc, e₂] using congr($hab ≫ pullback.snd f s)
    have he : pullback.lift π q' hπq' ≫ e = g.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, pullback.lift_fst]
      · rw [Category.assoc, e₂, pullback.lift_snd_assoc, hq']
    have : IsClosedImmersion (pullback.lift π q' hπq' ≫ e) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ e
  let O : T → W.toScheme.Opens := fun i ↦ (W.ι ≫ p i) ⁻¹ᵁ V i
  have hO : iSup O = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  have hloc : ∀ i, IsClosedImmersion (q' ∣_ O i) := by
    intro i
    have hr : Set.range g.toImage ⊆ Set.range (q' ⁻¹ᵁ O i).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : (g.toImage ≫ π) x ∈ A i := by
        rw [hπ]
        exact hUA i x.2
      change (q' ≫ W.ι ≫ p i) (g.toImage x) ∈ V i
      rw [reassoc_of% hq']
      exact hV i _ hx
    have hσ := IsOpenImmersion.lift_fac (q' ⁻¹ᵁ O i).ι g.toImage hr
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr ≫ (q' ⁻¹ᵁ O i).ι) := by
      rw [hσ]; infer_instance
    have : IsDominant (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) :=
      IsDominant.of_comp_of_isOpenImmersion _ (q' ⁻¹ᵁ O i).ι
    refine isClosedImmersion_morphismRestrict f (W.ι ≫ s) π q' hπq' (A i) (O i)
      ((V i).ι ≫ PSpace.str R (N i)) ((W.ι ≫ p i) ∣_ V i) ?_ (j i).liftCoborder ?_
      (IsOpenImmersion.lift (q' ⁻¹ᵁ O i).ι g.toImage hr) (X.homOfLE (hUA i)) ?_ ?_
    · rw [morphismRestrict_ι_assoc, Category.assoc, hp]
    · rw [Scheme.Hom.liftCoborder_ι_assoc, hjt]
    · rw [← cancel_mono (V i).ι, Category.assoc, Category.assoc, Category.assoc,
        morphismRestrict_ι, Scheme.Hom.liftCoborder_ι, morphismRestrict_ι_assoc, reassoc_of% hσ,
        reassoc_of% hq', reassoc_of% hq, hh]
    · rw [X.homOfLE_ι, reassoc_of% hσ, hπ]
  have : IsClosedImmersion q' :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) O hO hloc
  have : IsImmersion q := by rw [← hq']; infer_instance
  have : IsProper π := by infer_instance
  have : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U.isOpen.dense ⟨_, hU⟩⟩
  have : IsDominant (g.toImage ≫ π) := by rw [hπ]; infer_instance
  have : IsDominant π := IsDominant.of_comp g.toImage π
  have : QuasiCompact (q ≫ s) := by rw [← hπq]; infer_instance
  have : QuasiCompact q := QuasiCompact.of_comp q s
  obtain ⟨n, i₀, hi₀, e₀⟩ := hP
  exact ⟨g.image, π, inferInstance,
    surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range, n, q ≫ i₀,
    inferInstance, inferInstance, by rw [Category.assoc, e₀, hπq]⟩

end GlobalTheory.CompanionTheory.Ar.Approx
