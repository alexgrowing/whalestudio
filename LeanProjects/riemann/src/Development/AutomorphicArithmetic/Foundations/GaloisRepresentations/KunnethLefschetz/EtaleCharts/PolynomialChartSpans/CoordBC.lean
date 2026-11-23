import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_pushout {K K' B B' : Type} [CommRing K] [CommRing K'] [CommRing B] [CommRing B']
    (φ : K →+* K') (s : K →+* B) (s' : K' →+* B') (t : B →+* B')
    (po : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom s) (CommRingCat.ofHom s') (CommRingCat.ofHom t))
    (σ : Type) (x : σ → B) (hE : (MvPolynomial.eval₂Hom s x).Etale) :
    (MvPolynomial.eval₂Hom s' fun i => t (x i)).Etale := by
  have hl : IsPushout (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (MvPolynomial.map φ : MvPolynomial σ K →+* MvPolynomial σ K'))
      (CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K')) := by
    letI := φ.toAlgebra
    letI : Algebra (MvPolynomial σ K) (MvPolynomial σ K') := MvPolynomial.algebraMvPolynomial
    exact ((CommRingCat.isPushout_iff_isPushout (R := K) (S := MvPolynomial σ K) (R' := K')
      (S' := MvPolynomial σ K')).mpr inferInstance).flip
  have e1 : CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s x) = CommRingCat.ofHom s := by
    ext a
    simp
  have e2 : CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K') ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i)) = CommRingCat.ofHom s' := by
    ext a
    simp
  have big : IsPushout (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial σ K) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom s x)) (CommRingCat.ofHom φ) (CommRingCat.ofHom t)
      (CommRingCat.ofHom (MvPolynomial.C : K' →+* MvPolynomial σ K') ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i))) := by
    rw [e1, e2]
    exact po.flip
  have hw : ∀ a, t (s a) = s' (φ a) := fun a => by
    have := congrArg (fun f => f.hom a) po.w
    simpa using this.symm
  have p : CommRingCat.ofHom (MvPolynomial.eval₂Hom s x) ≫ CommRingCat.ofHom t =
      CommRingCat.ofHom (MvPolynomial.map φ : MvPolynomial σ K →+* MvPolynomial σ K') ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom s' fun i => t (x i)) := by
    ext1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hw]
    · intro i
      simp
  have r := big.of_left p hl
  have hP : (RingHom.toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) =>
      f.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P := RingHom.toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) => f.Etale)
    r.flip hE

theorem coordBC : UpperTheory.Gal.KunnethLefschetz.G.CoordBC := by
  intro K K' _ _ φ Z Z' q q' a hpb V hV σ x hE
  haveI : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  have hU : IsAffineOpen (a ⁻¹ᵁ V) := hV.preimage a
  refine ⟨hU, ?_⟩
  have hUY : a ⁻¹ᵁ V = a ⁻¹ᵁ V ⊓ q' ⁻¹ᵁ ⊤ := by simp
  have h1 : (⊤ : (Spec (CommRingCat.of K')).Opens) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ ⊤ := le_top
  have h2 : V ≤ q ⁻¹ᵁ ⊤ := le_top
  have hI := isIso_pushoutSection_of_isAffineOpen hpb h1 h2 hUY (isAffineOpen_top _) (isAffineOpen_top _) hV
  have sq := ((isIso_pushoutSection_iff hpb h1 h2 hUY).mp hI).flip
  have sq' : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Pb.strV q V))
      (CommRingCat.ofHom (Pb.strV q' (a ⁻¹ᵁ V))) (CommRingCat.ofHom (Scheme.Hom.app a V).hom) := by
    refine sq.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Scheme.ΓSpecIso_naturality]
      simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Pb.strV]
    · simp [Pb.strV]
    · simp [Scheme.Hom.app_eq_appLE]
  exact etale_pushout φ (Pb.strV q V) (Pb.strV q' (a ⁻¹ᵁ V)) (Scheme.Hom.app a V).hom sq' σ x hE

end UpperTheory.Gal.KunnethLefschetz.G
