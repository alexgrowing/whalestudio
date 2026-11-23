import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

private theorem fEt_surj {Y X : Scheme.{0}} {f : Y ⟶ X} {d : ℕ} (hf : FEt f d) (hd : 0 < d) (x : X) :
    ∃ y : Y, f y = x := by
  let K := AlgebraicClosure (X.residueField x)
  let b : Spec (CommRingCat.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  let a : Spec (CommRingCat.of K) ⟶ X := b ≫ X.fromSpecResidueField x
  have hc := hf.2.2 K a
  have hne : Nonempty {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ f = a} := by
    by_contra hem
    rw [not_nonempty_iff] at hem
    rw [Nat.card_of_isEmpty] at hc
    omega
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨y pt, ?_⟩
  have h1 : a pt ∈ Set.range (X.fromSpecResidueField x) := ⟨b pt, by simp [a]⟩
  rw [X.range_fromSpecResidueField] at h1
  rw [← Scheme.Hom.comp_apply, hy]
  exact h1

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} {f : Y ⟶ X} (e : X ⟶ X') [IsIso e] {d : ℕ}
    (hf : FEt f d) : FEt (f ≫ e) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv e)]
  refine Nat.card_congr ⟨fun y => ⟨y.1, ?_⟩, fun y => ⟨y.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rw [← cancel_mono e]; simp [y.2]
  · rw [← Category.assoc, y.2]; simp

theorem UpperTheory.Gal.Int.Geo.Cut.liesCut :
    UpperTheory.Gal.Int.Geo.Cut.LiesCut := by
  intro k L O _ _ _ _ H θ C C' j hj hπ g T s t m hL
  obtain ⟨hm, κ, h, ht, hF⟩ := hL
  have first : ∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π := by
    rintro x ⟨z, hz⟩
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    obtain ⟨y, rfl⟩ := fEt_surj hF hm w
    refine ⟨H.t g y, ?_⟩
    have hx : κ y = x := by
      rw [← hw2, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ht]
  refine ⟨first, ?_⟩
  intro T' i s' t' hR
  have : IsOpenImmersion i := hR.op
  have : IsOpenImmersion j := hj.op
  have hrj : ∀ z, C.π z ∈ Set.range j := fun z =>
    ⟨C'.π z, by rw [← hπ, Scheme.Hom.comp_apply]⟩
  have hκ : Set.range κ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
      exact hrj _
    · show t (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
      exact hrj _
  let κ' : H.Y g ⟶ T' := IsOpenImmersion.lift i κ hκ
  have hκ' : κ' ≫ i = κ := IsOpenImmersion.lift_fac i κ hκ
  have hs' : H.s g ≫ C'.π = κ' ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hκ', h]
  have ht' : κ' ≫ t' = H.t g ≫ C'.π := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.et, ← Category.assoc, hκ', ht]
  refine ⟨hm, κ', hs', ht', ?_⟩
  have hσ : Set.range (pullback.snd C.π s) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hs1 : s (pullback.snd C.π s w) = C.π (pullback.fst C.π s w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hmem : s (pullback.snd C.π s w) ∈ Set.range C.π := ⟨_, hs1.symm⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (pullback.snd C.π s w) ∈ Set.range j
      rw [hs1]; exact hrj _
    · show t (pullback.snd C.π s w) ∈ Set.range j
      obtain ⟨z, hz⟩ := first _ hmem
      rw [← hz]; exact hrj _
  let σ : pullback C.π s ⟶ T' := IsOpenImmersion.lift i (pullback.snd C.π s) hσ
  have hσ' : σ ≫ i = pullback.snd C.π s := IsOpenImmersion.lift_fac i _ hσ
  have hc : pullback.fst C.π s ≫ C'.π = σ ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hσ',
      pullback.condition]
  let ψ : pullback C.π s ⟶ pullback C'.π s' := pullback.lift (pullback.fst C.π s) σ hc
  have hc' : pullback.fst C'.π s' ≫ C.π = (pullback.snd C'.π s' ≫ i) ≫ s := by
    rw [← hπ, Category.assoc, ← hR.es, ← Category.assoc, ← Category.assoc, pullback.condition]
  let φ : pullback C'.π s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst C'.π s') (pullback.snd C'.π s' ≫ i) hc'
  have ψ1 : ψ ≫ pullback.fst C'.π s' = pullback.fst C.π s := pullback.lift_fst _ _ _
  have ψ2 : ψ ≫ pullback.snd C'.π s' = σ := pullback.lift_snd _ _ _
  have φ1 : φ ≫ pullback.fst C.π s = pullback.fst C'.π s' := pullback.lift_fst _ _ _
  have φ2 : φ ≫ pullback.snd C.π s = pullback.snd C'.π s' ≫ i := pullback.lift_snd _ _ _
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, φ1, ψ1, Category.id_comp]
    · rw [Category.assoc, φ2, ← Category.assoc, ψ2, hσ', Category.id_comp]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ψ1, φ1, Category.id_comp]
    · rw [Category.assoc, ψ2, Category.id_comp, ← cancel_mono i, Category.assoc, hσ', φ2]
  have : IsIso ψ := ⟨φ, hψφ, hφψ⟩
  have hfac : pullback.lift (H.s g) κ' hs' = pullback.lift (H.s g) κ h ≫ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ψ1, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, ψ2, ← cancel_mono i, hκ', Category.assoc, hσ',
        pullback.lift_snd]
  rw [hfac]
  exact fEt_comp_iso ψ hF
