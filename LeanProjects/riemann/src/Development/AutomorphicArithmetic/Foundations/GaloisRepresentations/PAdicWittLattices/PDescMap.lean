import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pDescMap :
    GenSm → EtDesc → PtEq → PtOrbit → WitCart → DescMap := by
  intro hSm hEt hEq hOrb hCart p _ D G L R _ _ gb M N' N XM X' X h hI hA' hA1 c Φc π₁ Φ₁ hWc hFin hEtc hSurj hW1
  have hAd : AdmK L (↑M) (↑N) h := by
    intro v hv
    have h1 := hA1 v hv
    have h2 : v ∈ L.KN ↑N' := by simpa using h1
    exact hA' v h2
  haveI hred : IsReduced XM.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field R XM.X XM.s
      (hSm p D R gb M XM).1).1
  haveI hsep : IsSeparated X.s := (hSm p D R gb N X).2.1
  haveI := hFin
  haveI := hEtc
  haveI := hSurj
  have hsq : π₁ ≫ X.s = c ≫ X'.s := hW1.1.trans hWc.1.symm
  obtain ⟨hepi, π, hπ⟩ := hEt c X'.s X.s π₁ hsq (by
    intro Ω _ _ x y hxy
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, _⟩ := hOrb p D G L R gb M N' XM X' c Φc hWc Ω x y hxy
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    exact (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω (x ≫ XM.s) x y rfl hys ox oy mx my θ hθ).1)
  have hπs : π ≫ X.s = X'.s := by
    rw [← cancel_epi c, ← Category.assoc, hπ, hW1.1, hWc.1]
  have wsq : ∀ {NN NN' : ℕ} (Y' : GenModel gb NN') (Y : GenModel gb NN) (g : G.GAf) (ρ : Y'.X ⟶ Y.X)
      (Ψ : Y'.univ.A.left ⟶ Y.univ.A.left), Wit L g Y' Y ρ Ψ → Ψ ≫ Y.univ.A.hom = Y'.univ.A.hom ≫ ρ := by
    rintro _ _ Y' Y g ρ Ψ ⟨_, o, ψ, φ, _, rfl⟩
    rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w ψ]
  have hC : IsPullback Φc XM.univ.A.hom X'.univ.A.hom c :=
    hCart p D G L R gb (↑M) (↑N') XM X' 1 (one_mem _) c Φc hWc
  haveI : IsReduced XM.univ.A.left := by
    haveI := XM.univ.ab.smooth
    exact GlobalTheory.isReduced_of_smooth_of_isReduced XM.univ.A.hom
  haveI : IsSeparated X.univ.A.hom := by
    haveI := X.univ.ab.proper
    infer_instance
  haveI : IsFinite Φc := MorphismProperty.of_isPullback (P := @IsFinite) hC.flip hFin
  haveI : Etale Φc := MorphismProperty.of_isPullback (P := @Etale) hC.flip hEtc
  haveI : Surjective Φc := MorphismProperty.of_isPullback (P := @Surjective) hC.flip hSurj
  have hsq2 : Φ₁ ≫ X.univ.A.hom = Φc ≫ X'.univ.A.hom ≫ π := by
    rw [wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  obtain ⟨hepi2, Φ, hΦ⟩ := hEt Φc (X'.univ.A.hom ≫ π) X.univ.A.hom Φ₁ hsq2 (by
    intro Ω _ _ x y hxy
    have hab : (x ≫ XM.univ.A.hom) ≫ c = (y ≫ XM.univ.A.hom) ≫ c := by
      have e := congrArg (· ≫ X'.univ.A.hom) hxy
      simpa [hC.w] using e
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθeq⟩ :=
      hOrb p D G L R gb M N' XM X' c Φc hWc Ω _ _ hab
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    have key := (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω ((x ≫ XM.univ.A.hom) ≫ XM.s) _ _ rfl hys ox oy mx my θ hθ).2
    obtain ⟨x', hx1, hx2⟩ : ∃ x' : sp Ω ⟶ ox.A.left, x' ≫ mx.φ = x ∧ x' ≫ ox.A.hom = 𝟙 _ :=
      ⟨mx.cart.1.lift x (𝟙 _) (by simp), mx.cart.1.lift_fst _ _ _, mx.cart.1.lift_snd _ _ _⟩
    obtain ⟨y', hy1, hy2⟩ : ∃ y' : sp Ω ⟶ oy.A.left, y' ≫ my.φ = y ∧ y' ≫ oy.A.hom = 𝟙 _ :=
      ⟨my.cart.1.lift y (𝟙 _) (by simp), my.cart.1.lift_fst _ _ _, my.cart.1.lift_snd _ _ _⟩
    have hP := my.cart.1.paste_horiz hC
    have hxy' : x' ≫ θ.left = y' := by
      apply hP.hom_ext
      · rw [Category.assoc, hθeq, ← Category.assoc, hx1, hxy, ← Category.assoc, hy1]
      · rw [Category.assoc, Over.w θ, hx2, hy2]
    calc x ≫ Φ₁ = x' ≫ mx.φ ≫ Φ₁ := by rw [← Category.assoc, hx1]
      _ = x' ≫ θ.left ≫ my.φ ≫ Φ₁ := by rw [key]
      _ = y' ≫ my.φ ≫ Φ₁ := by rw [← Category.assoc x', hxy']
      _ = y ≫ Φ₁ := by rw [← Category.assoc, hy1])
  have hΦs : Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
    rw [← cancel_epi Φc, ← Category.assoc, hΦ, wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  exact ⟨π, Φ, hπ, hΦ, hπs, hΦs⟩
