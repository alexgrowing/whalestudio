import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.mat_gstar :
    ∀ {G R : Type} [Group G] [CommRing R] {m : ℕ} (r : G →* GG m R) (c g : G), (r c).mat = 1 → (r c).right = -1 → (r g).right = 1 →
    (r (gstar c g)).mat = Jmat R m * (r g).matᵀ * Jmat R m ∧ (r (gstar c g)).right = 1 := by
  intro G R _ _ m r c g h1 h2 h3
  have hc : r c = SemidirectProduct.mk 1 (-1) := by
    apply SemidirectProduct.ext
    · exact Units.ext (by simpa [GG.mat] using h1)
    · exact h2
  have hg : r g = SemidirectProduct.mk (r g).left 1 := SemidirectProduct.ext rfl h3
  have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by
    simp only [gstar, map_mul, map_inv]
  rw [hs, hc, hg]
  simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, inv_one, map_one, mul_one, one_mul, MulAut.one_apply, map_inv,
    sgnAct_neg_one, theta_inv_val]
  refine ⟨?_, ?_⟩
  · simp [map_one, theta_inv_val]
  · norm_num
