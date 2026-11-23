import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CpZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ContGr

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreCp :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Near a 0 D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∃ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) ∧ (∀ n, AdicCont (maximalIdeal (W.gr 0)) fun g => (cp g).coeff n) ∧ ∀ g, (cp g).map (res Λ (W.gr 0) : W.gr 0 →+* ResidueField Λ) = ∏ i, (X - C (residue Λ (a (Φ.χ i g)))) := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hN hG D' hD
  have hr : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := fun g => by
    rw [← hD]; rfl
  have hent : ∀ g i j, D'.r g i j ∈ W.gr (wt i j) := fun g i j => by
    have := hG.ent g i j
    rw [hr] at this
    exact this
  have hc : ∀ g n, (D'.r g).charpoly.coeff n ∈ W.gr 0 := fun g => sxCpZero W.gr (D'.r g) (hent g)
  have hl : ∀ g, ∃ p : (W.gr 0)[X], p.map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly := fun g => by
    have : (D'.r g).charpoly ∈ Polynomial.lifts (algebraMap (W.gr 0) W.A) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hc g n⟩, rfl⟩
    exact (Polynomial.mem_lifts _).1 this
  choose cp hcp using hl
  have hco : ∀ g n, (((cp g).coeff n : W.A) : R) = (D.r g).charpoly.coeff n := fun g n => by
    rw [hr, Matrix.charpoly_map, coeff_map, ← hcp, coeff_map]
    rfl
  refine ⟨cp, hcp, fun n => ?_, fun g => ?_⟩
  · refine (sxContGr W hG.max).2 _ ?_
    simp only [hco]
    exact (sxAdicMat (maximalIdeal R) (fun g => D.r g) hN.cont).1 n
  · let f : W.gr 0 →ₐ[Λ] R :=
      { (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A) with
        commutes' := fun _ => rfl }
    have hd : (D.r g).map (res Λ R : R →+* ResidueField Λ) =
        Matrix.diagonal fun i => residue Λ (a (Φ.χ i g)) := by
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.diagonal_apply_eq]
        exact hN.diag g i
      · rw [Matrix.diagonal_apply_ne _ h]
        exact (res_eq_zero_iff Λ R _).2 (hN.off g i j h le_rfl)
    rw [← Matrix.charpoly_diagonal, ← hd, Matrix.charpoly_map]
    ext n
    rw [coeff_map, coeff_map, ← hco]
    exact (res_map f _).symm
