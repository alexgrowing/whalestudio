import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometryStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem congOne_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') {g : G.GAf} (h : L.CongOne N' g) : L.CongOne N g := by
  obtain ⟨k, rfl⟩ := hd
  intro v hv
  obtain ⟨w, hw, hv'⟩ := h v hv
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [hv', smul_smul]⟩

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.oneAt_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.OneAt := by
  intro hk li p _ D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hF B PD D' t hcls j a hpl hco hloc P x e hU
  obtain ⟨h3, hcop, h3', hcop', hdvd, -⟩ := hlev
  have lev1 : LevOk L N N' 1 := ⟨h3, hcop, h3', hcop', hdvd, fun u hu => by
    have hm : u ∈ L.KN N := ⟨congOne_of_dvd L hdvd hu.1, congOne_of_dvd L hdvd hu.2⟩
    simpa using hm⟩
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hPinc, he'', -, hj'', hpl'', hco'', hloc''⟩ :=
    hk p D G L gb N N' 1 lev1 X X' c₁ hX hL hX' hL' ρ hF D' t P x e hU B j a.1 (PD.lat a.2) hpl hco hloc
  have hco₁ : IsCoordA L (trivX B) N D'' t'' j'' a.1 := by simpa using hco''
  have hpos : 0 < N := by omega
  obtain ⟨w, hmk, hw⟩ := (li p D G L B PD N hpos hcop D' t D'' t'' j j'' a a N' N t t'' hcls hcls'' hpl hpl''
    (coordA_of_dvd L hdvd hco) hco₁ hloc hloc'' 1).1 ⟨by simp, by simp⟩
  have hw1 : ∀ u, j (w u) = j'' u := fun u => by
    rw [hw u]
    simp [actY]
  have hinc : ∀ u, w (inc u) = u := fun u => hpl.1 (by rw [hw1, hj''])
  have hP : ∀ u'', P (w u'') = P'' u'' := fun u'' => by
    have e1 : inc (w u'') = u'' := w.injective (hinc _)
    rw [← hPinc, e1]
  refine ⟨_, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D' t'' t P'' P
    (x ≫ c₁.q) e'' w (LinearEquiv.refl ℂ _) hpos hU'' hmk (fun u => hP u) hU.2.1, fun z => ?_⟩
  simpa using he'' z
