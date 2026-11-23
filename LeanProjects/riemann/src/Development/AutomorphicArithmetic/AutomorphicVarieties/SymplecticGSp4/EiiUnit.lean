import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem eii_step {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (y0 y1 y2 y3 : R) (hY : (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) ∈ A)
    (hu : IsUnit (y0 * y3 - y1 * y2)) : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
  have key : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) =
      (y0 + y3) • (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) -
        (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) *
          (!![y0, 0, y1, 0; 0, 0, 0, 0; y2, 0, y3, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hm : (y0 * y3 - y1 * y2) • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    rw [key]
    exact A.sub_mem (A.smul_mem _ hY) (hmul _ hY _ hY)
  obtain ⟨u, hu⟩ := hu
  have hs := A.smul_mem (↑u⁻¹ : R) hm
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at hs

private theorem eii_alg {R : Type} [CommRing R] (A : Submodule R (M4 R)) (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A)
    (hone : (1 : M4 R) ∈ A) (hadj : ∀ x ∈ A, adj x ∈ A) (X : M4 R) (hX : X ∈ A) (hb : IsBlock X)
    (hu : IsUnit ((X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) *
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) -
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2) * (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)))
    (H : M4 R) (hH : H ∈ A) (h02 : H 0 2 = 0) (h20 : H 2 0 = 0) (hd : IsUnit (H 0 0 - H 2 2)) (i : Fin 4) :
    Matrix.single i i (1 : R) ∈ A := by
  have z : ∀ a b, lamW a ≠ lamW b → X a b = 0 := hb
  have x01 := z 0 1 (by simp [lamW])
  have x03 := z 0 3 (by simp [lamW])
  have x10 := z 1 0 (by simp [lamW])
  have x12 := z 1 2 (by simp [lamW])
  have x21 := z 2 1 (by simp [lamW])
  have x23 := z 2 3 (by simp [lamW])
  have x30 := z 3 0 (by simp [lamW])
  have x32 := z 3 2 (by simp [lamW])
  have hYA : X * X - (X 1 1 + X 3 3) • X + (X 1 1 * X 3 3 - X 1 3 * X 3 1) • (1 : M4 R) ∈ A :=
    A.add_mem (A.sub_mem (hmul X hX X hX) (A.smul_mem _ hX)) (A.smul_mem _ hone)
  have hE : (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) ∈ A := by
    refine eii_step A hmul
      (X 0 0 * X 0 0 + X 0 2 * X 2 0 - (X 1 1 + X 3 3) * X 0 0 + (X 1 1 * X 3 3 - X 1 3 * X 3 1))
      (X 0 0 * X 0 2 + X 0 2 * X 2 2 - (X 1 1 + X 3 3) * X 0 2)
      (X 2 0 * X 0 0 + X 2 2 * X 2 0 - (X 1 1 + X 3 3) * X 2 0)
      (X 2 0 * X 0 2 + X 2 2 * X 2 2 - (X 1 1 + X 3 3) * X 2 2 + (X 1 1 * X 3 3 - X 1 3 * X 3 1)) ?_ hu
    convert hYA using 1
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, x01, x03, x10, x12, x21, x23, x30, x32] <;>
      ring
  have hZ : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) =
      (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) * H *
          (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) -
        H 2 2 • (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> simp [Matrix.single, h02, h20]
  have h0m : (H 0 0 - H 2 2) • Matrix.single 0 0 (1 : R) ∈ A := by
    rw [hZ]
    exact A.sub_mem (hmul _ (hmul _ hE _ hH) _ hE) (A.smul_mem _ hE)
  have e0 : Matrix.single 0 0 (1 : R) ∈ A := by
    obtain ⟨u, hu'⟩ := hd
    have hs := A.smul_mem (↑u⁻¹ : R) h0m
    rwa [← hu', smul_smul, Units.inv_mul, one_smul] at hs
  have e2 : Matrix.single 2 2 (1 : R) ∈ A := by
    have h : Matrix.single 2 2 (1 : R) =
        (!![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0] : M4 R) - Matrix.single 0 0 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.single]
    rw [h]
    exact A.sub_mem hE e0
  have hadjs : ∀ k : Fin 4, adj (Matrix.single k k (1 : R)) = Matrix.single k.rev k.rev 1 := by
    intro k
    ext a b
    fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [adj_apply, Matrix.single, sgn, Fin.rev]
  fin_cases i
  · exact e0
  · have h := hadj _ e2
    rwa [hadjs] at h
  · exact e2
  · have h := hadj _ e0
    rwa [hadjs] at h

private theorem eii_span {R H : Type} [CommRing R] [Group H] (r : H →* M4 R) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g)) :
    (∀ x ∈ Submodule.span R (Set.range r), ∀ y ∈ Submodule.span R (Set.range r), x * y ∈ Submodule.span R (Set.range r)) ∧
      ∀ x ∈ Submodule.span R (Set.range r), adj x ∈ Submodule.span R (Set.range r) := by
  have hadj : ∀ g, adj (r g) = ν g • r g⁻¹ := by
    intro g
    have hinv : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : adj (r g) * r g * r g⁻¹ = ν g • 1 * r g⁻¹ := by rw [hν g]
    rw [mul_assoc, hinv, mul_one, smul_mul_assoc, one_mul] at h0
    exact h0
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨a, ⟨g, rfl⟩, b, ⟨k, rfl⟩, rfl⟩
    exact ⟨g * k, map_mul r g k⟩
  · let L : M4 R →ₗ[R] M4 R :=
      { toFun := adj
        map_add' := fun x y => by
          ext i j
          simp only [adj_apply, Matrix.add_apply, smul_add]
        map_smul' := fun c x => by
          ext i j
          simp only [adj_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, zsmul_eq_mul]
          ring }
    have hle : Submodule.span R (Set.range r) ≤ (Submodule.span R (Set.range r)).comap L := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show adj (r g) ∈ Submodule.span R (Set.range r)
      rw [hadj g]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
    exact hle hx

private theorem eii_unit {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (x : R)
    (h : res O R x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((res_eq_zero_iff O R x).2 ((IsLocalRing.mem_maximalIdeal x).2 hx))

private theorem eii_abs {O R H : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Group H]
    (r : H →* M4 R) (ps : Fin 4 → H →* Oˣ) (ν : H → R) (hν : ∀ g, IsGSp (ν g) (r g))
    (hr : ∀ g i j, res O R (r g i j) = residue O (diagRep ps g i j)) (φ g : H) (hb : IsBlock (r φ))
    (hφ : ∀ i j, lamW i ≠ lamW j → residue O (ps i φ) ≠ residue O (ps j φ))
    (h0 : ps 0 g = ps 2 g * ps 1 g) (h1 : residue O (ps 1 g) ≠ 1) (h2 : residue O (ps 2 g) ≠ 1)
    (h02 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 0 2 = 0) (h20 : (r g + algebraMap O R (ps 0 g) • r g⁻¹) 2 0 = 0)
    (i : Fin 4) : Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range r) := by
  obtain ⟨hmul, hadj⟩ := eii_span r ν hν
  have hone : (1 : M4 R) ∈ Submodule.span R (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have hdiag : ∀ k i, res O R (r k i i) = residue O (ps i k : O) := by
    intro k i
    rw [hr]
    simp [diagRep]
  have hoff : ∀ k i j, i ≠ j → res O R (r k i j) = 0 := by
    intro k i j h
    rw [hr]
    simp [diagRep, Matrix.diagonal_apply_ne _ h]
  have hHm : r g + algebraMap O R (ps 0 g) • r g⁻¹ ∈ Submodule.span R (Set.range r) :=
    Submodule.add_mem _ (Submodule.subset_span ⟨g, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹, rfl⟩))
  refine eii_alg _ hmul hone hadj (r φ) (Submodule.subset_span ⟨φ, rfl⟩) hb ?_ _ hHm h02 h20 ?_ i
  · apply eii_unit (O := O)
    simp only [map_mul, map_add, map_sub, hdiag, hoff φ 0 2 (by decide), hoff φ 2 0 (by decide),
      hoff φ 1 3 (by decide), hoff φ 3 1 (by decide)]
    have n01 := sub_ne_zero.2 (hφ 0 1 (by simp [lamW]))
    have n03 := sub_ne_zero.2 (hφ 0 3 (by simp [lamW]))
    have n21 := sub_ne_zero.2 (hφ 2 1 (by simp [lamW]))
    have n23 := sub_ne_zero.2 (hφ 2 3 (by simp [lamW]))
    intro h
    apply mul_ne_zero (mul_ne_zero n01 n03) (mul_ne_zero n21 n23)
    linear_combination h
  · apply eii_unit (O := O)
    have hc : res O R (algebraMap O R (ps 0 g : O)) = residue O (ps 0 g : O) := by
      rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq]
    have hi : ∀ k, residue O (ps k g⁻¹ : O) * residue O (ps k g : O) = 1 := by
      intro k
      rw [← map_mul (residue O), ← Units.val_mul, ← map_mul (ps k), inv_mul_cancel, map_one,
        Units.val_one, map_one]
    have e0 : residue O (ps 0 g : O) = residue O (ps 2 g : O) * residue O (ps 1 g : O) := by
      rw [h0, Units.val_mul, map_mul]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_add, map_mul, hc, hdiag]
    intro h
    have hp : (residue O (ps 1 g : O) - 1) * (residue O (ps 2 g : O) - 1) = 0 := by
      linear_combination h - e0 * (1 - residue O (ps 2 g⁻¹ : O)) - hi 0 + residue O (ps 1 g : O) * hi 2
    rcases mul_eq_zero.1 hp with h' | h'
    · exact h1 (sub_eq_zero.1 h')
    · exact h2 (sub_eq_zero.1 h')

theorem UpperTheory.V.GradeZeroInterpolatingElement.eii :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), D.Mult ρ.hom → D.Nrm ρ.hom → ∀ i, Matrix.single i i (1 : R) ∈ Submodule.span R (Set.range ρ.hom) := by
  intro Ω _ _ _ l _ c D hG R _ _ _ ρ hM hN i
  obtain ⟨-, hT, -, -, -, -, -, -, -, hph, -⟩ := facts D hG
  have hrb : ∀ k j, D.rbar k j j = residue c.O (D.ps j k : c.O) := by
    intro k j
    simp [Raw.rbar, mapRep, Raw.r0, diagRep]
  refine eii_abs ρ.hom D.ps (fun g => algebraMap c.O R (D.th g : c.O)) hM ?_ D.ph D.g0 hN.1 ?_ ?_ ?_ ?_
    hN.2.1 hN.2.2 i
  · intro g a b
    rw [ρ.red]
    simp [Raw.rbar, mapRep, Raw.r0]
  · intro a b hab
    rw [← hrb, ← hrb, hph, hrb, hrb]
    exact (hT l (Finset.mem_insert_self _ _)).2.2 a b hab
  · rfl
  · exact hG.genElt_Psi
  · exact hG.genElt_alpha
