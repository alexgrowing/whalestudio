import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (hc : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  refine ⟨hc.1, fun a => ?_⟩
  obtain ⟨w, hw, hw'⟩ := hc.2 a
  obtain ⟨k, rfl⟩ := hd
  refine ⟨k • w, AddSubgroup.nsmul_mem _ hw k, ?_⟩
  rw [hw', smul_smul]

private theorem eq_of_nsmul_eq_of_ne_zero {g m : ℕ} (hm : m ≠ 0) {a b : Fin g → ℂ} (h : m • a = m • b) : a = b := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [← Nat.cast_smul_eq_nsmul ℂ m a, ← Nat.cast_smul_eq_nsmul ℂ m b] at h
  exact smul_right_injective _ hm' h

private theorem fix_line_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (y : GlobalTheory.LKCx.grp G β) {D' : PLat D.O D.inv} {j : D'.La →+ VQ D}
    (hdiv : ∀ w, ∃ (m : ℕ) (u : D'.La), m ≠ 0 ∧ m • w = j u)
    (Q : VQ D →+ (Fin D.g → ℂ)) (hh : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ))
    (hl : ∀ u, Q (actY L y (j u)) = hh (Q (j u))) :
    ∃ H : Matrix (Fin D.g) (Fin D.g) ℂ, ∀ w, Q (actY L y w) = H *ᵥ Q w := by
  refine ⟨LinearMap.toMatrix' (hh : (Fin D.g → ℂ) →ₗ[ℂ] (Fin D.g → ℂ)), fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  show Q (actY L y w) = hh (Q w)
  obtain ⟨m, u, hm, hmu⟩ := hdiv w
  apply eq_of_nsmul_eq_of_ne_zero hm
  have e1 : m • Q (actY L y w) = Q (actY L y (j u)) := by
    rw [← hmu, map_nsmul, map_nsmul]
  have e2 : m • hh (Q w) = hh (Q (j u)) := by
    rw [← hmu, map_nsmul, map_nsmul]
  rw [e1, e2, hl]

theorem UpperTheory.Gal.W2.fixFwd_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixFwd := by
  intro hHecke hOne hForm hIso hFix _hAct p _ D G L gb N N' h hLev X X' c₁ c₂ hX hL hX' hL' ρ hFine v t₀ B PD RD D' t hCls' P j a hC x e hU hx
  have hN : 0 < N := by
    have := hLev.1
    omega
  obtain ⟨hPl, hCA', hLoc, Q, hPerQ, hQP, hrel⟩ := hC
  obtain ⟨e₁, hU₁, -⟩ := hOne p D G L gb N N' h hLev X X' c₁ hX hL hX' hL' ρ hFine B PD D' t hCls' j a.1 hPl hCA' hLoc P x e hU
  obtain ⟨D'', t'', P'', e'', inc, j'', hCls'', hU'', hPinc, -, hdivinc, hjinc, hPl'', hCA'', hLoc''⟩ :=
    hHecke p D G L gb N N' h hLev X X' c₂ hX hL hX' hL' ρ hFine D' t P x e hU B j a.1.1 (PD.lat a.1.2) hPl hCA' hLoc
  have hx' : (x ≫ c₁.q : Sp ℂ ⟶ (gfam X.univ hX hL).X) = x ≫ c₂.q := hx
  revert e₁
  rw [hx']
  intro e₁ hU₁
  obtain ⟨w, hh, hmk, hPw, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry D.O D.inv D.g ρ _ _ _ _ N D' D'' t t'' P P'' _ _ _ hN hU₁ hU''
  obtain ⟨y, s, hs, hys, hyj⟩ := hForm p D G L B.β B.β D'' D' j'' j hPl'' hPl
    (w : D'.La →ₗ[D.O] D''.La) 1 one_pos (fun u u' => by
      rw [_root_.one_mul]
      exact hmk.1 u u')
  let Y : GlobalTheory.LKCx.grp G B.β := ⟨(y, s), hys, hs⟩
  have hQ'' : ∀ u'', Q (j'' u'') = P'' u'' := by
    intro u''
    obtain ⟨d, u, hd0, hdu⟩ := hdivinc u''
    have e1 : d • Q (j'' u'') = Q (j u) := by
      rw [← map_nsmul, ← map_nsmul, ← hdu, hjinc]
    have e2 : d • P'' u'' = P u := by
      rw [← map_nsmul, ← hdu, hPinc]
    apply eq_of_nsmul_eq_of_ne_zero hd0
    rw [e1, e2, hQP]
  have hl : ∀ u, Q (actY L Y (j u)) = hh (Q (j u)) := by
    intro u
    rw [hQP, ← hPw, ← hQ'']
    congr 1
    exact (hyj u).symm
  obtain ⟨H, hH⟩ := fix_line_ext L Y hPl.2.2.1 Q hh hl
  have hfixL := ((hFix p D G L v t₀ ρ B.β RD Q a.2 hPerQ hrel Y).1).2 ⟨H, hH⟩
  have hmem := (hIso p D G L B PD N hN hLev.2.1 D'' t'' D' t j'' j (a.1.1 * h⁻¹, a.1.2) a.1 N N' t'' t
    hCls'' hCls' hPl'' hPl hCA'' (coordA_of_dvd L hLev.2.2.2.2.1 hCA') hLoc'' hLoc Y).2 ⟨w, hmk, fun u => hyj u⟩
  refine ⟨Y, hfixL, ?_, by simpa using hmem.2⟩
  have h1 := hmem.1
  simp only [Set.mem_setOf_eq]
  simpa [mul_inv_rev, _root_.mul_assoc] using h1
