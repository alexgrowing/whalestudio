import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BoxDefs

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

private theorem hh_emb {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) R)
    (h1 : hᵀ * (form6 O).JR R * h = (form6 O).JR R)
    (h2 : ∀ a b, (form6 O).blk a ≠ (form6 O).blk b → h a b = 0) :
    ∃ x : GG 3 R, x.right = 1 ∧ emb x = h := by
  have hB : h.toBlocks₁₂ = 0 := by
    ext i j
    exact h2 (Sum.inl i) (Sum.inr j) (by simp [form6])
  have hC : h.toBlocks₂₁ = 0 := by
    ext i j
    exact h2 (Sum.inr i) (Sum.inl j) (by simp [form6])
  rw [blockPairingForm_JR, ← fromBlocks_toBlocks h, hB, hC, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply] at h1
  simp only [transpose_zero, zero_mul, mul_zero, add_zero, zero_add, Matrix.fromBlocks_inj] at h1
  obtain ⟨-, hk, -, -⟩ := h1
  have hJJ : Jmat R 3 * Jmat R 3 = 1 := Jmat_mul_Jmat 3
  have hr : h.toBlocks₁₁ᵀ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3) = 1 := by
    calc h.toBlocks₁₁ᵀ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)
        = (h.toBlocks₁₁ᵀ * Jmat R 3 * h.toBlocks₂₂) * Jmat R 3 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, hJJ]
  have hl : (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ * h.toBlocks₁₁ = 1 := by
    have ht := congrArg transpose hr
    rwa [transpose_mul, transpose_transpose, transpose_one] at ht
  have hr' : h.toBlocks₁₁ * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ = 1 := mul_eq_one_comm.mp hl
  let u : GL (Fin 3) R := ⟨h.toBlocks₁₁, (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ, hr', hl⟩
  refine ⟨⟨u, 1⟩, rfl, ?_⟩
  rw [emb_apply, if_pos rfl]
  conv_rhs => rw [← fromBlocks_toBlocks h, hB, hC]
  refine Matrix.fromBlocks_inj.mpr ⟨rfl, rfl, rfl, ?_⟩
  rw [theta_val]
  have hu : ((u⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3)ᵀ := rfl
  rw [hu, transpose_transpose]
  calc Jmat R 3 * (Jmat R 3 * h.toBlocks₂₂ * Jmat R 3) * Jmat R 3
      = (Jmat R 3 * Jmat R 3) * h.toBlocks₂₂ * (Jmat R 3 * Jmat R 3) := by
        simp only [Matrix.mul_assoc]
    _ = h.toBlocks₂₂ := by rw [hJJ, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.gLift_toLift_inH_and_surjective :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (hη : IsLocallyConstant η)
          {R : Type} [CommRing R] [Algebra O R] [IsCO O R],
          (∀ r : GLift O η Ψ R, (form6 O).InH (emb.comp (r0 η Ψ)) R (r.toLift hη)) ∧
          ∀ r' : Lift O (emb.comp (rbar O η Ψ)) R, (form6 O).InH (emb.comp (r0 η Ψ)) R r' → ∃ r : GLift O η Ψ R, r.toLift hη = r' := by
  intro O _ _ Γ _ _ η Ψ hη R _ _ _
  have hra : (res O R : R →+* ResidueField O).comp (algebraMap O R) = residue O := by
    ext a
    simp [IsLocalRing.ResidueField.algebraMap_eq]
  refine ⟨fun r s => ?_, fun r' hr => ?_⟩
  · have hrt : ∀ g, (r.hom g).right = η g := r.hasMult
    show (form6 O).HH (emb (r.hom s) * (emb (r0 η Ψ s⁻¹)).map (algebraMap O R))
    rw [← emb_map', ← map_mul emb]
    set x := r.hom s * GG.map (algebraMap O R) (r0 η Ψ s⁻¹) with hxdef
    have hx : x.right = 1 := by
      rw [hxdef, SemidirectProduct.mul_right, GG.map_right, unitaryThreeReflection_right, hrt, ← map_mul, mul_inv_cancel,
        map_one]
    refine ⟨emb_form O x, fun a b hab => ?_, ?_⟩
    · by_contra hne
      have hb := emb_blk x a b hne
      rw [if_pos hx] at hb
      exact hab hb
    · rw [show (emb x).map ⇑(res O R) = emb (GG.map (res O R : R →+* ResidueField O) x) from
        (emb_map' _ x).symm]
      rw [hxdef, map_mul, r.red, GG.map_map, hra, baseLift_map_residue, ← map_mul, mul_inv_cancel, map_one, map_one]
  · have hr2 : ∀ s, (form6 O).HH (r'.hom s * (emb (r0 η Ψ s⁻¹)).map (algebraMap O R)) := fun s => hr s
    choose x hx1 hx2 using fun s => hh_emb (O := O) _ (hr2 s).1 (hr2 s).2.1
    have hF : ∀ s, emb (x s * GG.map (algebraMap O R) (r0 η Ψ s)) = r'.hom s := by
      intro s
      rw [map_mul emb, hx2 s, ← emb_map', Matrix.mul_assoc, ← map_mul emb, ← map_mul, ← map_mul,
        inv_mul_cancel, map_one, map_one, map_one, Matrix.mul_one]
    have hR : ∀ s, (x s * GG.map (algebraMap O R) (r0 η Ψ s)).right = η s := by
      intro s
      rw [SemidirectProduct.mul_right, hx1, GG.map_right, unitaryThreeReflection_right, one_mul]
    let hom : Γ →* GG 3 R :=
      { toFun := fun s => x s * GG.map (algebraMap O R) (r0 η Ψ s)
        map_one' := by
          beta_reduce
          refine eq_of_emb ?_ ?_
          · rw [hR, map_one, SemidirectProduct.one_right]
          · rw [hF, map_one, map_one]
        map_mul' := fun s t => by
          beta_reduce
          refine eq_of_emb ?_ ?_
          · rw [hR, SemidirectProduct.mul_right, hR, hR, map_mul]
          · rw [hF, map_mul emb, hF, hF, map_mul] }
    refine ⟨⟨hom, fun a b => ?_, fun g => ?_⟩, ?_⟩
    · have he : (fun g => (hom g).mat a b) =
          fun g => r'.hom g (Sum.inl a) (Sum.inl b) + r'.hom g (Sum.inl a) (Sum.inr b) := by
        funext g
        rw [mat_eq_emb']
        show emb (x g * _) _ _ + emb (x g * _) _ _ = _
        rw [hF]
      rw [he]
      intro N
      have h1 := r'.cont (Sum.inl a) (Sum.inl b) N
      have h2 := r'.cont (Sum.inl a) (Sum.inr b) N
      convert h1.add h2 using 1
      funext g
      simp only [Pi.add_apply, map_add]
    · refine eq_of_emb ?_ ?_
      · rw [GG.map_right, ← baseLift_map_residue, GG.map_right, unitaryThreeReflection_right]
        exact hR g
      · rw [emb_map']
        ext a b
        rw [Matrix.map_apply]
        show (res O R) (emb (x g * _) a b) = _
        rw [hF]
        exact r'.red g a b
    · exact Lift.ext (MonoidHom.ext fun g => hF g)
