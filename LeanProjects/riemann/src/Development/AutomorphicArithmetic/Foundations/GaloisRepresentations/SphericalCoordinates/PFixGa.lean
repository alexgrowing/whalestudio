import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem isCoordA_of_dvd {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.fixGa_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.IntMult → UpperTheory.Gal.W2.FixGa := by
  intro hHC hLI hFL hAY hIM p _ D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD D' t hcls P j a hco x e hU y hsee
  obtain ⟨hpl, hca, hloc, Q₀, hQ₀, hQ₀j, hrel⟩ := hco
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hP, he, hinc, hj, hpl'', hco'', hloc''⟩ :=
    hHC p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₂ hX hL hX' hL' ρ hfine D' t P x e hU B j a.1.1
      (PD.lat a.1.2) hpl hca hloc
  obtain ⟨hfix, hS, hK⟩ := hsee
  have hN : 0 < N := by omega
  have hS' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS
  obtain ⟨w, hw, hwj⟩ := (hLI p D G L B PD N hN hcp D' t D'' t'' j j'' a.1 (a.1.1 * h⁻¹, a.1.2) N' N t t''
    hcls hcls'' hpl hpl'' (isCoordA_of_dvd L hd hca) hco'' hloc hloc'' y⁻¹).1 (by
      constructor
      · have := (L.KN N).inv_mem hS'
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this
      · have := (KHT p G.m G.n 1 G.Fw).inv_mem hK
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this)
  have hfix' := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y).2 hfix
  obtain ⟨H, hH⟩ := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y⁻¹).1.1 hfix'
  have hga : ∀ u, j (w (inc u)) = actY L y⁻¹ (j u) := fun u => by rw [hwj, hj]
  have hQQ : ∀ Q : VQ D →+ Fin D.g → ℂ, (∀ u, Q (j u) = P u) → ∀ w₀, Q w₀ = Q₀ w₀ := by
    intro Q hQj w₀
    obtain ⟨m, u, hm, hmu⟩ := hpl.2.2.1 w₀
    apply smul_right_injective (Fin D.g → ℂ) hm
    simp only
    rw [← map_nsmul Q, ← map_nsmul Q₀, hmu, hQj, hQ₀j]
  obtain ⟨s, hs, hEF⟩ := hpl.2.2.2
  have hpos : (0 : ℚ) < ((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 := (y⁻¹).2.2
  have hmul : ∀ u u' : D'.La, (((D'.EF ((w.toLinearMap ∘ₗ inc) u)) ((w.toLinearMap ∘ₗ inc) u') : ℤ) : ℚ) =
      (((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 : ℚ) * ((D'.EF u u' : ℤ) : ℚ) := by
    intro u u'
    show (((D'.EF (w (inc u))) (w (inc u')) : ℤ) : ℚ) = _
    rw [hEF, hEF, hga, hga, (hAY p D G L B.β y⁻¹).1]
    ring
  obtain ⟨m, hm, hm'⟩ := hIM D.O D.inv D' (w.toLinearMap ∘ₗ inc) _ hpos hmul
  refine ⟨w.toLinearMap ∘ₗ inc, H, fun u => hga u, ⟨⟨m, hm, hm'⟩, fun u => ?_⟩, fun w' Q hQj hQ => ?_⟩
  · show P (w (inc u)) = H *ᵥ P u
    rw [← hQ₀j, ← hQ₀j, hga, hH]
  · rw [hQQ Q hQj, hQQ Q hQj, hH]
