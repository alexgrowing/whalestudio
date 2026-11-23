import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem tor_conj_apply {R : Type} [CommRing R] (t : Rˣ) (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    ((tor R t).val * X * (tor R t⁻¹).val) a b = ((t ^ wt a b : Rˣ) : R) * X a b := by
  rw [tor_val, tor_val, Matrix.mul_diagonal,
    Matrix.diagonal_mul, wt, _root_.zpow_sub, Units.val_mul, _root_.inv_zpow]
  ring

private theorem unit_diff {O : Type} [CommRing O] (p : Oˣ) (hp : IsUnit ((p : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((p ^ wt1 a : Oˣ) : O) - ((p ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((p : O) - 1) :=
    isUnit_of_mul_isUnit_left (y := (p : O) + 1) (by convert hp using 1; ring)
  have e : (p : O) * ((p⁻¹ : Oˣ) : O) = 1 := p.mul_inv
  have h2 : IsUnit ((1 : O) - ((p⁻¹ : Oˣ) : O)) := by
    convert h1.mul (p⁻¹).isUnit using 1
    linear_combination (-1 : O) * e
  have h3 : IsUnit ((p : O) - ((p⁻¹ : Oˣ) : O)) := by
    convert hp.mul (p⁻¹).isUnit using 1
    linear_combination (-(p : O)) * e
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  have k : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases k a with rfl | rfl | rfl <;> rcases k b with rfl | rfl | rfl <;>
    simp only [w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg_one, Units.val_one] <;>
    first
    | exact absurd rfl hab
    | assumption
    | (rw [← neg_sub, IsUnit.neg_iff]; assumption)

private theorem red_diag {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [Group D] {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG 3 R} (hr : Red η Ψ r) {x : D}
    (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) :
    (∀ a b, a ≠ b → IsUnit ((r x).mat a a - (r x).mat b b)) ∧
      ∀ a b, a ≠ b → (r x).mat a b ∈ maximalIdeal R := by
  have hd : ∀ a, (r x).mat a a - algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O) ∈ maximalIdeal R := fun a => by
    have := hr.red x a a
    rwa [Matrix.sub_apply, Matrix.map_apply, GG.mat, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_eq] at this
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · by_contra hn
    have h1 : (r x).mat a a - (r x).mat b b ∈ maximalIdeal R := hn
    have h2 := (unit_diff (Ψ x) hx a b hab).map (algebraMap O R)
    have h3 := Ideal.add_mem _ (Ideal.sub_mem _ h1 (hd a)) (hd b)
    refine h3 ?_
    convert h2 using 1
    rw [map_sub]; ring
  · have := hr.red x a b
    rwa [Matrix.sub_apply, Matrix.map_apply, GG.mat, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.diagonal_apply_ne _ hab,
      map_zero, sub_zero] at this

private theorem local_of_co {O R R' : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') : IsLocalHom (f : R →+* R') := by
  refine ⟨fun y hy => ?_⟩
  by_contra hn
  have h1 : y ∈ maximalIdeal R := hn
  rw [← res_eq_zero_iff O, ← res_map f, res_eq_zero_iff] at h1
  exact h1 hy

private theorem canon_wpart {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [Group Γ] (u : Γ →* GG 3 R) (x : Γ) (hu : ∀ a b, a ≠ b → IsUnit ((u x).mat a a - (u x).mat b b))
    (h : GL (Fin 3) R) (hc : Canon (u x).mat h) :
    GrMat (wpart O u) h.val ∧ GrMat (wpart O u) (h⁻¹).val := by
  have key : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : R'ˣ),
      push f' u = conjBy (tor R' t) (push f u) →
      GeneralLinearGroup.map (f' : R →+* R') h =
        tor R' t * GeneralLinearGroup.map (f : R →+* R') h * tor R' t⁻¹ := by
    intro R' _ _ _ f f' t e
    haveI := local_of_co f
    haveI := local_of_co f'
    have c1 := canon_map.1 (f' : R →+* R') _ h hc
    have c2 := canon_map.2 _ _ t (canon_map.1 (f : R →+* R') _ h hc)
    have e1 : (tor R' t).val * ((u x).mat.map (f : R →+* R')) * (tor R' t⁻¹).val
        = (u x).mat.map (f' : R →+* R') := by
      ext a b
      rw [tor_conj_apply]
      exact (entry_mem u x a b R' f f' t e).symm
    rw [e1] at c2
    refine canon_unique _ _ _ (fun a b hab => ?_) c1 c2
    have := (hu a b hab).map (f' : R →+* R')
    rwa [map_sub] at this
  refine ⟨fun a b R' _ _ _ f f' t e => ?_, fun a b R' _ _ _ f f' t e => ?_⟩
  · have k := congrArg (fun g : GL (Fin 3) R' => g.val a b) (key R' f f' t e)
    simp only [Units.val_mul, tor_conj_apply] at k
    exact k
  · have k0 : GeneralLinearGroup.map (f' : R →+* R') h⁻¹ =
        tor R' t * GeneralLinearGroup.map (f : R →+* R') h⁻¹ * tor R' t⁻¹ := by
      rw [map_inv, key R' f f' t e, map_inv, map_inv]
      group
    have k := congrArg (fun g : GL (Fin 3) R' => g.val a b) k0
    simp only [Units.val_mul, tor_conj_apply] at k
    exact k

theorem UpperTheory.V.UnitaryThreeInertia.exists_graded_basis :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ v ∈ F.Tb, ∃ h : GL (Fin 3) R, InHat h ∧ GrMat (wpart O u) h.val ∧ GrMat (wpart O u) (h⁻¹).val ∧
      (v = F.vl → TriIn (F.ηv v) (F.Ψv v) (F.Iv v) (u.comp (F.loc v)) h) ∧ (v ∈ F.Sb → DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) (u.comp (F.loc v)) h) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ _ R _ _ _ u hu v hv
  obtain ⟨x, hη, hx⟩ := hF.x v hv
  have hred : Red (F.ηv v) (F.Ψv v) (u.comp (F.loc v)) :=
    ⟨fun g => hu.pt.mult (F.loc v g), fun g => hu.pt.red (F.loc v g)⟩
  obtain ⟨h1, h2⟩ := red_diag hred hx
  obtain ⟨h, hc⟩ := exists_canon _ h1 h2
  have hg := canon_wpart (O := O) u (F.loc v x) h1 h hc
  have hi := cond_iff_canon (F.ηv v) (F.Ψv v) (F.Iv v) _ x h hred hη hx hc
  exact ⟨h, hc.hat, hg.1, hg.2, fun e => hi.1.1 ((hu.pt.loc v).1 e), fun e => hi.2.1 ((hu.pt.loc v).2.1 e)⟩
