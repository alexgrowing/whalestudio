import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.MonoZero

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eqMono_unit {Λ S : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing S] [Algebra Λ S] [IsCO Λ S] {x : S}
    (h : IsUnit (res Λ S x)) : IsUnit x := by
  by_contra hn
  exact h.ne_zero ((res_eq_zero_iff Λ S x).2 hn)

private theorem eqMono_root {S : Type} [CommRing S] (x : S) (c : Fin 4 → S) (i : Fin 4)
    (h : ∏ j, (x - c j) = 0) (hu : ∀ j, j ≠ i → IsUnit (x - c j)) : x = c i := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)] at h
  have h2 : IsUnit (∏ j ∈ Finset.univ.erase i, (x - c j)) :=
    IsUnit.prod_iff.2 fun j hj => hu j (Finset.ne_of_mem_erase hj)
  exact sub_eq_zero.1 (h2.mul_left_eq_zero.1 h)

theorem UpperTheory.V.Ws.sxEqMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} [IsCO Λ (W.gr 0)], Φ.Ok ((residue Λ).comp a) → Φ.Near a 0 D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ cp : Γ → (W.gr 0)[X], (∀ g, (cp g).map (algebraMap (W.gr 0) W.A) = (D'.r g).charpoly) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ g n, f ((cp g).coeff n) = f' ((cp g).coeff n)) → ∀ x ∈ mono D.r 0, ∃ b : W.gr 0, ((b : W.A) : R) = x ∧ f b = f' b := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W _ hOk hNear hGr D' hD' cp hcp R' _ _ _ f f' hff' x hx
  classical
  let φA : W.gr 0 →ₐ[Λ] R :=
    { toRingHom := (W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A)
      commutes' := fun c => rfl }
  have hAinj : Function.Injective (algebraMap (W.gr 0) W.A) := fun b c h => Subtype.ext h
  let E : Subring R := (AlgHom.equalizer f f').toSubring.map (φA : W.gr 0 →+* R)
  have hmem : ∀ b : W.gr 0, f b = f' b → φA b ∈ E := fun b hb => Subring.mem_map.mpr ⟨b, hb, rfl⟩
  have hrep := hNear.rep
  have hdex : ∀ i : Fin 4, ∃ d : W.gr 0, φA d = D.r Φ.g0 i i := by
    intro i
    have h := hGr.ent Φ.g0 i i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact ⟨⟨⟨_, W.part_le_A h⟩, h⟩, rfl⟩
  choose d hd using hdex
  have hresd : ∀ i, res Λ (W.gr 0) (d i) = residue Λ (a ↑((Φ.χ i) Φ.g0)) := by
    intro i
    rw [← res_map φA, hd]
    exact hNear.diag Φ.g0 i
  have hdist : ∀ i j, i ≠ j → IsUnit (res Λ (W.gr 0) (d i - d j)) := by
    intro i j hij
    have h := hOk.dist i j hij
    simp only [RingHom.comp_apply] at h
    rw [map_sub, hresd, hresd, ← map_sub]
    exact h
  have hD'r : ∀ g, D.r g = (D'.r g).map (W.A.val : W.A →+* R) := by
    intro g
    rw [← hD']
    rfl
  have hD'g0 : D'.r Φ.g0 = Matrix.diagonal (fun i => algebraMap (W.gr 0) W.A (d i)) := by
    ext i j
    change (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = (W.A.val : W.A →+* R) _
    have h1 : (W.A.val : W.A →+* R) (D'.r Φ.g0 i j) = D.r Φ.g0 i j := by
      rw [hD'r]
      rfl
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, h1, ← hd i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero, h1]
      exact hrep.nrm hij
  have hcp0 : cp Φ.g0 = ∏ j, (X - C (d j)) := by
    apply Polynomial.map_injective _ hAinj
    rw [hcp, hD'g0, Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp
  have hmapeq : (cp Φ.g0).map (f : W.gr 0 →+* R') = (cp Φ.g0).map (f' : W.gr 0 →+* R') := by
    ext n
    simpa using hff' Φ.g0 n
  have hfix : ∀ i, f (d i) = f' (d i) := by
    intro i
    have hroot : ∏ j, (f' (d i) - f (d j)) = 0 := by
      have h1 : ((cp Φ.g0).map (f' : W.gr 0 →+* R')).eval (f' (d i)) = 0 := by
        rw [hcp0, Polynomial.map_prod, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp
      rw [← hmapeq, hcp0, Polynomial.map_prod, Polynomial.eval_prod] at h1
      simpa using h1
    have hu : ∀ j, j ≠ i → IsUnit (f' (d i) - f (d j)) := by
      intro j hji
      apply eqMono_unit (Λ := Λ)
      rw [map_sub, res_map, res_map, ← map_sub]
      exact hdist i j (Ne.symm hji)
    exact (eqMono_root (f' (d i)) (fun j => f (d j)) i hroot hu).symm
  have hν : ∀ g, ∃ ν ∈ E, IsGSp ν (D.r g) := fun g =>
    ⟨_, hmem (algebraMap Λ (W.gr 0) (a ↑(Φ.ν g))) (by rw [f.commutes, f'.commutes]), hrep.mult g⟩
  have htr : ∀ g, Matrix.trace (D.r g) ∈ E := by
    intro g
    have h2 : Matrix.trace (D'.r g) = algebraMap (W.gr 0) W.A (-(cp g).coeff 3) := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hcp, Polynomial.coeff_map, map_neg]
    have h3 : Matrix.trace (D.r g) = (W.A.val : W.A →+* R) (Matrix.trace (D'.r g)) := by
      rw [hD'r g]
      simp [Matrix.trace, map_sum]
    have h1 : Matrix.trace (D.r g) = φA (-(cp g).coeff 3) := by
      rw [h3, h2]
      rfl
    rw [h1]
    exact hmem _ (by rw [map_neg, map_neg, hff' g 3])
  have hEdiag : ∀ i, D.r Φ.g0 i i ∈ E := fun i => by
    rw [← hd i]
    exact hmem _ (hfix i)
  have hsep : ∀ i j, i ≠ j → ∃ u ∈ E, u * (D.r Φ.g0 i i - D.r Φ.g0 j j) = 1 := by
    intro i j hij
    obtain ⟨U, hU⟩ := eqMono_unit (Λ := Λ) (S := W.gr 0) (hdist i j hij)
    have hfe : f (d i - d j) = f' (d i - d j) := by rw [map_sub, map_sub, hfix, hfix]
    have e1 : f ↑U⁻¹ * f (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have e2 : f' ↑U⁻¹ * f' (d i - d j) = 1 := by rw [← hU, ← map_mul, Units.inv_mul, map_one]
    have hinv : f (↑U⁻¹ : W.gr 0) = f' ↑U⁻¹ := by
      calc f ↑U⁻¹ = f ↑U⁻¹ * (f' (d i - d j) * f' ↑U⁻¹) := by rw [mul_comm (f' _), e2, mul_one]
        _ = (f ↑U⁻¹ * f (d i - d j)) * f' ↑U⁻¹ := by rw [hfe]; ring
        _ = f' ↑U⁻¹ := by rw [e1, one_mul]
    refine ⟨φA ↑U⁻¹, hmem _ hinv, ?_⟩
    rw [← hd i, ← hd j, ← map_sub, ← map_mul, ← hU, Units.inv_mul, map_one]
  have hsub := sxMonoZero E D.r Φ.g0 hν htr hrep.nrm hEdiag hsep
  obtain ⟨b, hb, hbx⟩ := Subring.mem_map.mp (hsub hx)
  exact ⟨b, hbx, hb⟩
