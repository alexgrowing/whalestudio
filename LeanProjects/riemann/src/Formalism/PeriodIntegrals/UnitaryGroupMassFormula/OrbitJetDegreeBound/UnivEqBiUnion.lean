import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.ProdMonomialOne

noncomputable section

open Classical

namespace PI.OrbJet.AU

open Formalism.BasicNotions Formalism.MainNotions.G PI.OrbJet PI.OrbJet.OrbW PI.OrbShared PI.OrbJet.OJ

variable (D : D7) (p : ℕ) [Fact p.Prime]

theorem univ_eq_biUnion {R : Finset (Pl D)} (hR : IsReps D p R) :
    (Finset.univ : Finset (Pl D)) = R.biUnion (fun r => Finset.univ.image (orbMap D p r)) := by
  ext z
  simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_image, true_iff]
  obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
  refine ⟨r, hr, ?_⟩
  unfold orbMap
  refine ⟨(e : ZMod (nP D p)), trivial, ?_⟩
  rw [ZMod.val_natCast, ← he]
  have key : ∀ (x : HH D) (n e : ℕ), n • x = 0 → (e % n) • x = e • x := by
    intro x n e h
    conv_rhs => rw [← Nat.mod_add_div e n]
    rw [add_nsmul, mul_comm, ← smul_smul, h, smul_zero, add_zero]
  have hpe : partner D p r.2 (e % nP D p) = partner D p r.2 e := by
    unfold partner nP
    by_cases hs : IsSg D p
    · have h2 : (2 * addOrderOf (2 • hP D p)) • hP D p = 0 := by
        rw [mul_comm, ← smul_smul, addOrderOf_nsmul_eq_zero]
      simp only [if_pos hs]
      rw [key _ _ _ h2]
      simp only [Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 _)]
    · simp only [if_neg hs]
      rw [key _ _ _ (addOrderOf_nsmul_eq_zero _)]
      simp [hs]
  unfold posPl
  rw [hpe]

private theorem orbMap_injective (r : Pl D) : Function.Injective (orbMap D p r) := by
  intro s t hst
  unfold orbMap posPl partner at hst
  simp only [Prod.mk.injEq, add_right_inj] at hst
  obtain ⟨h1, h2⟩ := hst
  have hn : nP D p = if IsSg D p then 2 * addOrderOf (2 • hP D p) else addOrderOf (hP D p) := by
    unfold nP
    rfl
  have hs_lt := lt_of_lt_of_eq (ZMod.val_lt s) hn
  have ht_lt := lt_of_lt_of_eq (ZMod.val_lt t) hn
  apply ZMod.val_injective
  by_cases hsg : IsSg D p
  · rw [if_pos hsg] at hs_lt ht_lt
    have hpar : s.val % 2 = t.val % 2 := by
      have h1' : (s.val % 2 = 1 ↔ t.val % 2 = 1) := by
        have hd : decide (IsSg D p) = true := decide_eq_true hsg
        simpa [hd, Nat.odd_iff] using h1
      rcases Nat.mod_two_eq_zero_or_one s.val with h | h <;>
        rcases Nat.mod_two_eq_zero_or_one t.val with h' | h'
      · rw [h, h']
      · exact absurd (h1'.mpr h') (by omega)
      · exact absurd (h1'.mp h) (by omega)
      · rw [h, h']
    have h3 : (s.val % 2) • hP D p + (2 * (s.val / 2)) • hP D p
        = (t.val % 2) • hP D p + (2 * (t.val / 2)) • hP D p := by
      rw [← add_nsmul, ← add_nsmul, Nat.mod_add_div, Nat.mod_add_div]
      exact h2
    rw [hpar] at h3
    have h4 := add_left_cancel h3
    have hk : (s.val / 2) • (2 • hP D p) = (t.val / 2) • (2 • hP D p) := by
      rw [smul_smul, smul_smul, mul_comm (s.val / 2), mul_comm (t.val / 2)]
      exact h4
    have h5 := nsmul_inj_mod.mp hk
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h5
    omega
  · rw [if_neg hsg] at hs_lt ht_lt
    have h5 := nsmul_inj_mod.mp h2
    rwa [Nat.mod_eq_of_lt hs_lt, Nat.mod_eq_of_lt ht_lt] at h5

theorem prod_orbits {M : Type*} [CommMonoid M] {R : Finset (Pl D)} (hR : IsReps D p R) (g : Pl D → M) :
    ∏ z, g z = ∏ r ∈ R, ∏ s : ZMod (nP D p), g (orbMap D p r s) := by
  rw [univ_eq_biUnion D p hR, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [Finset.prod_image (fun s _ t _ h => orbMap_injective D p r h)]
  · intro r hr r' hr' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz hz'
    obtain ⟨s, rfl⟩ := hz
    obtain ⟨s', hs'⟩ := hz'
    apply hne
    obtain ⟨r0, -, huniq⟩ := hR (orbMap D p r s)
    have a := huniq r ⟨hr, s.val, rfl⟩
    have b := huniq r' ⟨hr', s'.val, hs'⟩
    rw [a, b]

theorem Gxz_eq {R : Finset (Pl D)} (hR : IsReps D p R) {N0 N1 : ℕ} (nu : Pl D → YoungDiagram)
    (I : ColChoice N1 nu) :
    Gxz N0 N1 nu I = ∏ r ∈ R, MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r))
      (Gxz N0 N1 (fun s => nu (orbMap D p r s)) (fun s => I (orbMap D p r s))) := by
  unfold Gxz
  rw [prod_orbits D p hR]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  unfold minorXZ
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp [AlgHom.mapMatrix_apply, Matrix.map_apply, map_sum, MvPolynomial.rename_X, xzMap, orbE, pEmb,
    Function.Embedding.coeFn_mk]
  all_goals rfl

theorem Gxz_supported {N0 N1 : ℕ} (r : Pl D) (nu : ZMod (nP D p) → YoungDiagram) (I : ColChoice N1 nu) :
    MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r)) (Gxz N0 N1 nu I) ∈
      MvPolynomial.supported ℤ (xzLetter ⁻¹' Set.range (orbMap D p r)) := by
  rw [MvPolynomial.mem_supported]
  intro v hv
  have hv' := MvPolynomial.vars_rename _ _ (Finset.mem_coe.mp hv)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv'
  rcases w with ⟨s, _⟩ | ⟨s, _⟩ <;>
    exact Set.mem_preimage.mpr (Set.mem_range.mpr ⟨s, by simp [xzLetter, xzMap, orbE, pEmb, orbMap]⟩)

theorem kval_prod {R : Finset (Pl D)} (hR : IsReps D p R) {N0 N1 : ℕ} (nu : Pl D → YoungDiagram)
    (F : Pl D → MvPowerSeries (ZMod (nP D p) × Fin N0 × Fin N1) ℂ_[p]) (β : Pl D → ℝ)
    (hF : ∀ r ∈ R, KvalGe N0 N1 p (fun s => nu (orbMap D p r s)) (F r) (β r)) :
    KvalGe N0 N1 p nu (∏ r ∈ R, MvPowerSeries.rename (pE D p r (Fin N0 × Fin N1)) (F r)) (∑ r ∈ R, β r) := by
  intro I m
  have hdisj : (R : Set (Pl D)).PairwiseDisjoint (fun r => Set.range (orbMap D p r)) := by
    intro r hr r' hr' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨s, rfl⟩ ⟨s', hs'⟩
    exact hne (mem_orbit_unique D p hR hr hr' s s' hs'.symm)
  have key := applyAt0_prod p R (fun r => Set.range (orbMap D p r)) hdisj
    (fun r => MvPowerSeries.rename (pE D p r (Fin N0 × Fin N1)) (F r))
    (fun r => MvPolynomial.rename (xzMap (N0 := N0) (N1 := N1) (orbE D p r))
      (Gxz N0 N1 (fun s => nu (orbMap D p r s)) (fun s => I (orbMap D p r s))))
    (fun r _ => serIn_rename (orbE D p r) (F r)) (fun r _ => Gxz_supported D p r _ _)
  beta_reduce at key
  rw [Gxz_eq D p hR, key]
  have hpos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsum : (p : ℝ) ^ (-∑ r ∈ R, β r) = ∏ r ∈ R, (p : ℝ) ^ (-β r) := by
    rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hpos]
  rw [hsum]
  refine norm_coeff_prod_le R (fun r _ => Real.rpow_nonneg hpos.le _) (fun r hr m' => ?_) m
  rw [applyAt0_rename]
  exact norm_coeff_rename_le _ _ (Real.rpow_nonneg hpos.le _) (fun m'' => hF r hr _ m'') m'

end PI.OrbJet.AU

end
