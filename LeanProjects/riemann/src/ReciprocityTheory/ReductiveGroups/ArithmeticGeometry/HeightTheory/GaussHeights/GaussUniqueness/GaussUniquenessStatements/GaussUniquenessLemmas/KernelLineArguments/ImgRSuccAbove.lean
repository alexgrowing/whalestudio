import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussUniqueness.GaussUniquenessStatements.GaussUniquenessLemmas.KernelLineArguments.ExistsSmulOfLine

namespace GaussValuationUniqueness

open ReciprocityTheory.ChartRestriction.G.T0

noncomputable def imgR {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (p : TVar D N) : MvPolynomial (SVar D N) R :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) R) j0
    (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (ρ k))
    (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2

theorem imgR_same {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) : imgR (D := D) j0 ρ (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (ρ k) := by
  unfold imgR
  exact sac_same j0 _ _

theorem imgR_succAbove {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) (k : Fin N) :
    imgR (D := D) j0 ρ (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
  unfold imgR
  exact sac_succAbove j0 _ _ k

theorem imgR_map {R R' : Type*} [CommRing R] [CommRing R'] {D N : ℕ} (φ : R →+* R')
    (j0 : Fin (N + 1)) (ρ : Fin N → R) (t : TVar D N) :
    MvPolynomial.map φ (imgR j0 ρ t) = imgR j0 (fun k => φ (ρ k)) t := by
  obtain ⟨i, j⟩ := t
  rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
  · rw [imgR_same, imgR_same]
    split_ifs
    · exact MvPolynomial.map_X φ _
    · simp only [map_neg, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  · rw [imgR_succAbove, imgR_succAbove, MvPolynomial.map_X]

section Ker

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem alg_mem (hv : IsTrivOn K v) (x : K) : algebraMap K Ω x ∈ vRing v := by
  rw [mem_vRing_iff]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [hv x hx]

noncomputable def kap (hv : IsTrivOn K v) : K →+* vRing v :=
  (algebraMap K Ω).codRestrict (vRing v) (alg_mem v hv)

noncomputable def psiT (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (vRing v) :=
  MvPolynomial.eval₂Hom ((MvPolynomial.C : vRing v →+* MvPolynomial (SVar D N) (vRing v)).comp
    (kap v hv)) (imgR j0 ρ)

noncomputable def psiR (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (ρ : Fin N → vRing v) :
    MvPolynomial (TVar D N) K →+* MvPolynomial (SVar D N) (IsLocalRing.ResidueField (vRing v)) :=
  (MvPolynomial.map (IsLocalRing.residue (vRing v))).comp (psiT (D := D) v hv j0 ρ)

theorem pos_of_ker {w : AddValuation (OmS Ω D N) (WithTop ℤ)}
    (hw : ∀ a : Ω, w (algebraMap Ω (OmS Ω D N) a) = v a)
    (e : SVar D N → OmS Ω D N) (he : ∀ s, 0 ≤ w (e s))
    (q : MvPolynomial (SVar D N) (vRing v))
    (hq : MvPolynomial.map (IsLocalRing.residue (vRing v)) q = 0) :
    0 < w (MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) e q) := by
  rw [MvPolynomial.eval₂_eq]
  refine Finset.sum_induction _ (fun x => 0 < w x)
    (fun a b ha hb => lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add w a b)) (by simp) ?_
  intro d _
  have hprod : 0 ≤ w (∏ s ∈ d.support, e s ^ d s) :=
    Finset.prod_induction _ (fun x => 0 ≤ w x)
      (fun a b ha hb => by rw [AddValuation.map_mul]; exact add_nonneg ha hb)
      (le_of_eq (AddValuation.map_one w).symm)
      (fun s _ => by rw [AddValuation.map_pow]; exact nsmul_nonneg (he s) _)
  have hnu : ¬ IsUnit (q.coeff d) := by
    have h0 := congrArg (MvPolynomial.coeff d) hq
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h0
    exact (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hc : 0 < w (((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) (q.coeff d)) := by
    rw [RingHom.comp_apply, hw]
    exact pos_of_not_isUnit v _ hnu
  rw [AddValuation.map_mul]
  exact lt_of_lt_of_le hc (le_add_of_nonneg_right hprod)

end Ker

end GaussValuationUniqueness
