import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open NumberField IsDedekindDomain UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
universe u v

private theorem ext2 {X B k K T : Scheme.{0}} {p : X ⟶ B} {g₁ : k ⟶ B} {g₂ : K ⟶ k}
    (a b : T ⟶ pullback (pullback.snd p g₁) g₂)
    (h1 : a ≫ pullback.snd _ _ = b ≫ pullback.snd _ _)
    (h2 : a ≫ pullback.fst _ _ ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ ≫ pullback.fst _ _) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using h2
    · simp only [Category.assoc, pullback.condition]
      rw [reassoc_of% h1]
  · exact h1

private theorem bcComp {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'}
    (f₁ : Z ⟶ Y) (f₂ : Y ⟶ X) (h₁ : f₁ ≫ q = r) (h₂ : f₂ ≫ p = q) (h : (f₁ ≫ f₂) ≫ p = r) :
    bcMap g (f₁ ≫ f₂) h = bcMap g f₁ h₁ ≫ bcMap g f₂ h₂ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, bcMap_fst]
    rw [← Category.assoc (bcMap g f₁ h₁), bcMap_fst, Category.assoc]
  · simp only [Category.assoc, bcMap_snd]

private theorem bcCongr {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {f f' : Y ⟶ X}
    (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : bcMap g f h = bcMap g f' h' := by
  subst e; rfl

private theorem square {B B' k K X Y : Scheme.{0}} (gφ : B' ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (gO : K ⟶ B')
    {p : X ⟶ B} {q : Y ⟶ B} (u : Y ⟶ X) (h : u ≫ p = q)
    (eX : pullback (pullback.snd p gφ) gO ⟶ pullback (pullback.snd p g₁) g₂)
    (eY : pullback (pullback.snd q gφ) gO ⟶ pullback (pullback.snd q g₁) g₂)
    (hX1 : eX ≫ pullback.snd _ _ = pullback.snd _ _)
    (hX2 : eX ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _)
    (hY1 : eY ≫ pullback.snd _ _ = pullback.snd _ _)
    (hY2 : eY ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _) :
    bcMap gO (bcMap gφ u h) (bcMap_snd _ _ _) ≫ eX = eY ≫ bcMap g₂ (bcMap g₁ u h) (bcMap_snd _ _ _) := by
  apply ext2
  · simp only [Category.assoc, hX1, hY1, bcMap_snd]
  · simp only [Category.assoc, hX2, reassoc_of% hY2, bcMap_fst, reassoc_of% bcMap_fst]

private theorem modP (hM : ModBc) (l : ℕ) [Fact l.Prime] (K : FinExt l) {O : Type} [CommRing O] [IsNoetherianRing O]
    (φ : O →+* ↥(CrystallineSemistableComparison.OK l K.1)) {Y : Scheme.{0}} (p : Y ⟶ sp O) (d : ℕ)
    (hs : SmoothOfRelativeDimension d p) (hp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p) :
    (⟨_, pullback.snd p (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd p (Spec.map (CommRingCat.ofHom φ))) := by
  have h : (⟨_, pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))⟩ : CrystallineSemistableComparison.Model l K.1).Sm ∧
      SmoothOfRelativeDimension d (pullback.snd (𝟙 Y ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    hM l K φ p d hs hp (𝟙 Y)
  rw [Category.id_comp] at h
  exact h

private theorem galPart (hSp : BcSplits) (hGal : BcGal) {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k)
    (s : T ⟶ Y) [IsFinite s] [Etale s] (c₀ : W₀ ⟶ Y) (G : Type) [Group G] [Finite G] (a₀ : G → (W₀ ⟶ W₀)) (n : ℕ)
    (σ₀ : Fin n → (W₀ ⟶ T)) (hG : IsGalois c₀ G a₀) (hS : Splits s c₀ σ₀) :
    ∃ (ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p) (hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p)
      (hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁),
      IsGalois (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _)) G
        (fun x => bcMap g₂ (bcMap g₁ (a₀ x) (ha x)) (bcMap_snd _ _ _)) ∧
      Splits (bcMap g₂ (bcMap g₁ s rfl) rfl) (bcMap g₂ (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _))
        (fun j => bcMap g₂ (bcMap g₁ (σ₀ j) (hσ j)) (hσ₁ j)) := by
  have hac := hG.2.2.2.2.2.1
  have hsc := hS.1
  have ha : ∀ x, a₀ x ≫ c₀ ≫ p = c₀ ≫ p := fun x => by rw [← Category.assoc, hac x]
  have hσ : ∀ j, σ₀ j ≫ s ≫ p = c₀ ≫ p := fun j => by rw [← Category.assoc, hsc j]
  have hσ₁ : ∀ j, bcMap g₁ (σ₀ j) (hσ j) ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ =
      pullback.snd (c₀ ≫ p) g₁ := fun j => by simp only [bcMap_snd]
  refine ⟨ha, hσ, hσ₁, ?_, ?_⟩
  · have hG1 := hGal g₁ p (c₀ ≫ p) c₀ rfl G a₀ ha hG
    exact hGal g₂ (pullback.snd p g₁) (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ c₀ rfl) (bcMap_snd _ _ _) G _
      (fun x => bcMap_snd _ _ _) hG1
  · obtain ⟨hF, hE, hsp⟩ := hSp g₁ p (s ≫ p) (c₀ ≫ p) s rfl c₀ rfl (Fin n) σ₀ hσ
    haveI := hF
    haveI := hE
    exact (hSp g₂ (pullback.snd p g₁) _ (pullback.snd (c₀ ≫ p) g₁) (bcMap g₁ s rfl) rfl (bcMap g₁ c₀ rfl)
      (bcMap_snd _ _ _) (Fin n) _ hσ₁).2.2 (hsp hS)

private theorem compPart {B k K Y T W₀ : Scheme.{0}} (p : Y ⟶ B) (g₁ : k ⟶ B) (g₂ : K ⟶ k) (s t : T ⟶ Y)
    (ht : t ≫ p = s ≫ p) (c₀ : W₀ ⟶ Y) (σ : W₀ ⟶ T) (hσ : σ ≫ s ≫ p = c₀ ≫ p) (hu : (σ ≫ t) ≫ p = c₀ ≫ p)
    (hσ₁ : bcMap g₁ σ hσ ≫ bcMap g₁ s rfl ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁)
    (ht' : bcMap g₁ t ht ≫ pullback.snd p g₁ = bcMap g₁ s rfl ≫ pullback.snd p g₁) :
    bcMap g₂ (bcMap g₁ (σ ≫ t) hu) (bcMap_snd _ _ _) = bcMap g₂ (bcMap g₁ σ hσ) hσ₁ ≫ bcMap g₂ (bcMap g₁ t ht) ht' := by
  have h' : (bcMap g₁ σ hσ ≫ bcMap g₁ t ht) ≫ pullback.snd p g₁ = pullback.snd (c₀ ≫ p) g₁ := by
    simp only [Category.assoc, ht', hσ₁]
  exact (bcCongr g₂ (bcComp g₁ σ t hσ ht hu) _ h').trans (bcComp g₂ _ _ hσ₁ ht' h')

set_option maxHeartbeats 4000000 in
theorem UpperTheory.Gal.G3.jLowCov :
    GalClosD → BcSplits → BcGal → GenIso → ModBc → LowCov := by
  intro hGC hSp hGal hGI hM E _ _ l _ H θ w C D K τK hτ
  let φ : Ow w →+* CrystallineSemistableComparison.OK l K.1 :=
    RingHom.codRestrict (τK.comp (HeightOneSpectrum.valuation E w).valuationSubring.subtype) _
      (fun x => GroundTheory.PAdicHodge.mem_normInteger.mpr (hτ x))
  have hφ : ∀ x : Ow w, algebraMap (CrystallineSemistableComparison.OK l K.1) K.1 (φ x) = τK (algebraMap (Ow w) E x) := fun x => rfl
  obtain ⟨d₀, hd₀⟩ := C.dim
  obtain ⟨eZ, hZ1, hZ2⟩ := hGI φ τK hφ C.p
  have hMZ := modP hM l K φ C.p d₀ hd₀ C.proj
  refine ⟨⟨_, pullback.snd C.p (Spec.map (CommRingCat.ofHom φ))⟩, eZ,
    ⟨hMZ.1, ⟨d₀, hMZ.2⟩, eZ, hZ1⟩, hZ1, fun g => ?_⟩
  have hfet := D.fet g
  haveI := hfet.1
  haveI := hfet.2.1
  obtain ⟨W₀, c₀, G, _, _, a₀, σ₀, hG, hS⟩ := hGC (D.s g) (D.d g) (D.fet g)
  obtain ⟨ha, hσ, hσ₁, hGal', hSpl⟩ := galPart hSp hGal C.p (gen (Ow w) E)
    (Spec.map (CommRingCat.ofHom τK)) (D.s g) c₀ G a₀ (D.d g) σ₀ hG hS
  haveI := hG.1
  haveI := hG.2.1
  have hMW := hM l K φ C.p d₀ hd₀ C.proj c₀
  obtain ⟨eW, hW1, hW2⟩ := hGI φ τK hφ (c₀ ≫ C.p)
  have hu : ∀ i, (σ₀ i ≫ D.t g) ≫ C.p = c₀ ≫ C.p := fun i => by
    rw [Category.assoc, D.comm g, ← Category.assoc, hS.1 i]
  have ht' : bcMap (gen (Ow w) E) (D.t g) (D.comm g) ≫ pullback.snd C.p (gen (Ow w) E) =
      bcMap (gen (Ow w) E) (D.s g) rfl ≫ pullback.snd C.p (gen (Ow w) E) := by
    simp only [bcMap_snd]
  refine ⟨_, bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) c₀ rfl) (bcMap_snd _ _ _),
    G, inferInstance, inferInstance, _, Fin (D.d g), inferInstance,
    fun i => bcMap (Spec.map (CommRingCat.ofHom τK)) (bcMap (gen (Ow w) E) (σ₀ i) (hσ i)) (hσ₁ i), hGal', ?_,
    ⟨_, pullback.snd (c₀ ≫ C.p) (Spec.map (CommRingCat.ofHom φ))⟩, eW,
    ⟨hMW.1, ⟨d₀, hMW.2⟩, eW, ?_⟩,
    ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) c₀ rfl, bcMap_snd _ _ _, ?_⟩,
    fun i => ⟨bcMap (Spec.map (CommRingCat.ofHom φ)) (σ₀ i ≫ D.t g) (hu i), bcMap_snd _ _ _, ?_⟩⟩
  · exact hSpl
  · exact (congrArg (eW.hom ≫ ·) (bcMap_snd _ _ _)).trans hW1
  · exact square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) c₀ rfl eZ.hom eW.hom hZ1 hZ2 hW1 hW2
  · have hcp := compPart C.p (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK)) (D.s g) (D.t g) (D.comm g)
      c₀ (σ₀ i) (hσ i) (hu i) (hσ₁ i) ht'
    have hsq := square (Spec.map (CommRingCat.ofHom φ)) (gen (Ow w) E) (Spec.map (CommRingCat.ofHom τK))
      (gen (CrystallineSemistableComparison.OK l K.1) K.1) (σ₀ i ≫ D.t g) (hu i) eZ.hom eW.hom hZ1 hZ2 hW1 hW2
    exact hsq.trans (congrArg (eW.hom ≫ ·) hcp)
