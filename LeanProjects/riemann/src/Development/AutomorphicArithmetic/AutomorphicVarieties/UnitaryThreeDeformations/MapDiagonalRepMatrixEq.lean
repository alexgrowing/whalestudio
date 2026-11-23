import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_diagonal_rep_matrix_eq {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (GG.map (algebraMap O R) (r0 η Ψ g)).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
  rw [GG.map_mat]
  show ((tor O (Ψ g)).val).map (algebraMap O R) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem conjBy_inv_one {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

private theorem diagIn_one {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R)
    (hr : ∀ g, (r g).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g)) : DiagIn η Ψ I r 1 := by
  have hne : ∀ a b : Fin 3, wt a b ≠ 0 → a ≠ b := by
    intro a b h hab
    subst hab
    simp [wt] at h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne)
  · intro s _ _ a
    rw [conjBy_inv_one, hr, Matrix.diagonal_apply_eq]
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne')

theorem UpperTheory.V.UnitaryThreeInertia.isPt_rz :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)], F.IsPt g₁ (F.rz R) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hok g₁ R _ _ _ _
  have hmat : ∀ g, (F.rz R g).mat = diagonal fun a => algebraMap O R (psi F.Ψ a g) :=
    fun g => map_diagonal_rep_matrix_eq F.η F.Ψ g
  have hinhat : InHat (1 : GL (Fin 3) R) := by
    intro a b
    simp
  have hloc : ∀ v, ∀ s, ((F.rz R).comp (F.loc v) s).mat =
      diagonal fun a => algebraMap O R (psi (F.Ψv v) a s) := fun v s => hmat _
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro g
    rfl
  · intro g a b
    have e : (F.rz R g).mat = (r0 F.η F.Ψ g).mat.map (algebraMap O R) := GG.map_mat _ _
    rw [e, sub_self, Matrix.zero_apply]
    exact zero_mem _
  · intro v
    refine ⟨fun _ => ⟨1, hinhat, (diagIn_one _ _ _ _ (hloc v)).toTriIn⟩,
      fun _ => ⟨1, hinhat, diagIn_one _ _ _ _ (hloc v)⟩, fun hv s hs => ?_⟩
    have h1 : F.Ψ (F.loc v s) = 1 := hok.teich v hv s hs
    have h2 : F.η (F.loc v s) = 1 := hs.1.2
    show GG.map (algebraMap O R) (r0 F.η F.Ψ (F.loc v s)) = 1
    have e : r0 F.η F.Ψ (F.loc v s) = 1 := by
      apply SemidirectProduct.ext
      · rw [unitaryThreeReflection_left, h1, map_one]
        rfl
      · exact h2
    rw [e, map_one]
  · have hc : ∀ a, psi F.Ψ a F.c = 1 := by
      intro a
      simp [psi, hok.Ψc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmat]
      simp [hc, Matrix.diagonal_one]
    · simp [zmat, hmat]
    · simp [zmat, hmat]
  · intro n
    have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit (algebraMap O R) x hx)) n
    have key : ∀ g g', Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g : O) =
        Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g' : O) → ∀ a,
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g)) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g')) := by
      intro g g' h a
      let q : O →* O ⧸ maximalIdeal O ^ n := (Ideal.Quotient.mk (maximalIdeal O ^ n) : O →* O ⧸ maximalIdeal O ^ n)
      have hu : Units.map q (F.Ψ g) = Units.map q (F.Ψ g') := Units.ext h
      have h2 : ((Units.map q (F.Ψ g ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) =
          ((Units.map q (F.Ψ g' ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) := by
        rw [map_zpow (Units.map q) (F.Ψ g) (wt1 a), map_zpow (Units.map q) (F.Ψ g') (wt1 a), hu]
      have h3 : Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g) =
          Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g') := h2
      rw [Ideal.Quotient.eq] at h3 ⊢
      rw [← map_sub]
      exact hle (Ideal.mem_map_of_mem _ h3)
    have hf := hok.Ψ_cont n
    rw [IsLocallyConstant.iff_exists_open] at hf ⊢
    intro x
    obtain ⟨U, hU, hxU, hUx⟩ := hf x
    refine ⟨U, hU, hxU, fun x' hx' => ?_⟩
    simp only [hmat]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact key x' x (hUx x' hx') a
