import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ConstOfAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NotIrrOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit

open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Pr

private theorem charpoly_dvd_expand {A : Type} [CommRing A] {m : ℕ} (M : Matrix (Fin m) (Fin m) A) (n : ℕ) :
    M.charpoly ∣ expand A n (M ^ n).charpoly := by
  have hc : Commute (scalar (Fin m) (X : A[X])) ((C : A →+* A[X]).mapMatrix M) :=
    scalar_commute _ (fun _ => Commute.all _ _) _
  have key : (expand A n : A[X] →+* A[X]).mapMatrix (charmatrix (M ^ n)) =
      charmatrix M * ∑ i ∈ Finset.range n,
        (scalar (Fin m) (X : A[X])) ^ i * ((C : A →+* A[X]).mapMatrix M) ^ (n - 1 - i) := by
    rw [show charmatrix M = scalar (Fin m) (X : A[X]) - (C : A →+* A[X]).mapMatrix M from rfl,
      hc.mul_geom_sum₂, ← map_pow, ← map_pow]
    ext i j
    by_cases h : i = j <;> simp [charmatrix_apply, h]
  unfold Matrix.charpoly
  have := RingHom.map_det (expand A n : A[X] →+* A[X]) (charmatrix (M ^ n))
  rw [RingHom.coe_coe] at this
  rw [this, key, det_mul]
  exact dvd_mul_right _ _

set_option linter.overlappingInstances false in
private theorem charpoly_const {k A : Type} [Field k] [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A]
    {m : ℕ} (M : Matrix (Fin m) (Fin m) A) (M₀ N₀ : Matrix (Fin m) (Fin m) k) (n : ℕ) (hn : 0 < n)
    (h : EntIn (maximalIdeal A) (M - M₀.map (algebraMap k A)))
    (hp : (M ^ n).charpoly = (N₀.map (algebraMap k A)).charpoly) :
    M.charpoly = M₀.charpoly.map (algebraMap k A) := by
  classical
  have hmon : (expand k n N₀.charpoly).Monic := (charpoly_monic N₀).expand hn
  have hdvd : M.charpoly ∣ (expand k n N₀.charpoly).map (algebraMap k A) := by
    rw [map_expand, ← charpoly_map, ← hp]
    exact charpoly_dvd_expand M n
  have hint := isIntegral_coeff_of_dvd _ _ hmon (charpoly_monic M) hdvd
  have hres : M.map (IsLocalRing.residue A) = (M₀.map (algebraMap k A)).map (IsLocalRing.residue A) := by
    ext a b
    simp only [Matrix.map_apply]
    apply Ideal.Quotient.eq.mpr
    simpa using h a b
  have hcp := congrArg Matrix.charpoly hres
  simp only [charpoly_map] at hcp
  ext i
  rw [Polynomial.coeff_map]
  apply UpperTheory.V.Pr.constOfAlg k A _ _ (hint i).isAlgebraic
  have hi := congrArg (fun p => p.coeff i) hcp
  simp only [Polynomial.coeff_map] at hi
  exact Ideal.Quotient.eq.mp hi

set_option linter.overlappingInstances false in
private theorem diag_const {k A : Type} [Field k] [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A]
    {m : ℕ} (M : Matrix (Fin m) (Fin m) A) (M₀ : Matrix (Fin m) (Fin m) k)
    (h : EntIn (maximalIdeal A) (M - M₀.map (algebraMap k A)))
    (hp : M.charpoly = M₀.charpoly.map (algebraMap k A)) (a : Fin m)
    (ha : (Matrix.scalar (Fin m) (M a a) - M).det = 0) : M a a = algebraMap k A (M₀ a a) := by
  classical
  apply UpperTheory.V.Pr.constOfAlg k A
  · refine ⟨M₀.charpoly, (charpoly_monic M₀).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hp, Matrix.eval_charpoly]
    exact ha
  · simpa using h a a

private theorem zmat_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (c g₁ : G)
    (r : G →* GG 3 R) (i j : Fin 3) : zmat c g₁ ((GG.map f).comp r) i j = f (zmat c g₁ r i j) := by
  simp only [zmat, Matrix.sub_apply, MonoidHom.comp_apply, GG.map_mat, Matrix.map_apply, map_sub]

private theorem normalised_map {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) {c g₁ : G}
    {r : G →* GG 3 R} (h : Normalised c g₁ r) : Normalised c g₁ ((GG.map f).comp r) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [GG.map_mat, h.atc]
  · rw [zmat_map, h.z12, map_zero]
  · rw [zmat_map, h.z21, map_zero]

private theorem charpoly_diagonal_character_rep {G k : Type} [Group G] [Field k] (η : G →* ℤˣ) (Ψ : G →* kˣ) (g : G) :
    (r0 η Ψ g).mat.charpoly = (X - C (Ψ g : k)) * (X - C 1) * (X - C ((Ψ g)⁻¹ : kˣ).1) := by
  simp [GG.mat, unitaryThreeReflection_left, tor_val, charpoly_diagonal, Fin.prod_univ_three, wt1]

private theorem corner_eq {κ : Type} [CommRing κ] (M : Matrix (Fin 3) (Fin 3) κ) :
    corner M = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem charpoly_block {κ : Type} [CommRing κ] (M : Matrix (Fin 3) (Fin 3) κ) (h1 : M 0 1 = 0)
    (h2 : M 1 0 = 0) (h3 : M 1 2 = 0) (h4 : M 2 1 = 0) :
    M.charpoly = (corner M).charpoly * (X - C (M 1 1)) := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.det_fin_two]
  simp [corner_eq, Matrix.charmatrix_apply, h1, h2, h3, h4]
  ring

private theorem corner_mul {κ : Type} [CommRing κ] (M N : Matrix (Fin 3) (Fin 3) κ) (h1 : M 0 1 = 0)
    (h4 : M 2 1 = 0) : corner (M * N) = corner M * corner N := by
  rw [corner_eq, corner_eq, corner_eq, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private theorem not_typeI {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (Φ : G →* κˣ) (r : G →* GG 3 κ)
    (hm : HasMult η r)
    (hp : ∀ g ∈ η.ker, (r g).mat.charpoly = (X - C (Φ g : κ)) * (X - C 1) * (X - C ((Φ g)⁻¹ : κˣ).1)) :
    ¬ TypeI η r := by
  intro h
  refine notIrrOfChar η.ker κ 3 (by norm_num) (glPart η r hm)
    ![Φ.comp η.ker.subtype, 1, (Φ.comp η.ker.subtype)⁻¹] (fun g => ?_) fun W hW => h W fun g hg => hW ⟨g, hg⟩ trivial
  rw [chPoly, Fin.prod_univ_three]
  exact hp g g.2

private theorem exists_corner_rep_of_block {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (r : G →* GG 3 κ)
    (hm : HasMult η r) (hB : Block η r) :
    ∃ ρ : η.ker →* GL (Fin 2) κ, ∀ g, (ρ g : Matrix (Fin 2) (Fin 2) κ) = corner (r g).mat := by
  have hmul : ∀ g h : η.ker, (r (g * h : η.ker)).mat = (r g).mat * (r h).mat := by
    intro g h
    have hr : (r g).right = 1 := by rw [hm]; exact g.2
    rw [Subgroup.coe_mul, map_mul]
    show (((r g * r h).left : GL (Fin 3) κ) : Matrix (Fin 3) (Fin 3) κ) =
      ((r g).left : Matrix (Fin 3) (Fin 3) κ) * (r h).left
    rw [SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply, Units.val_mul]
  let μ : η.ker →* Matrix (Fin 2) (Fin 2) κ :=
    { toFun := fun g => corner (r g).mat
      map_one' := by
        rw [OneMemClass.coe_one, map_one, corner_eq]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [GG.mat]
      map_mul' := fun g h => by
        show corner (r (g * h : η.ker)).mat = corner (r g).mat * corner (r h).mat
        rw [hmul g h]
        exact corner_mul _ _ (hB g g.2 0 1 ⟨0, by simp [wt, wt1]⟩) (hB g g.2 2 1 ⟨-1, by simp [wt, wt1]⟩) }
  exact ⟨μ.toHomUnits, fun g => rfl⟩

private theorem not_typeII {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (Φ : G →* κˣ) (r : G →* GG 3 κ)
    (hm : HasMult η r)
    (hp : ∀ g ∈ η.ker, (r g).mat.charpoly = (X - C (Φ g : κ)) * (X - C 1) * (X - C ((Φ g)⁻¹ : κˣ).1))
    (hB : Block η r) (h11 : ∀ g ∈ η.ker, (r g).mat 1 1 = 1) : ¬ TypeII η r := by
  rintro ⟨-, hirr⟩
  obtain ⟨ρ, hρ⟩ := exists_corner_rep_of_block η r hm hB
  let χ : Fin 2 → η.ker →* κˣ := ![Φ.comp η.ker.subtype, (Φ.comp η.ker.subtype)⁻¹]
  apply UpperTheory.V.Pr.notIrrOfChar η.ker κ 2 le_rfl ρ χ
  · intro g
    have hcp := charpoly_block (r g).mat (hB g g.2 0 1 ⟨0, by simp [wt, wt1]⟩)
      (hB g g.2 1 0 ⟨-1, by simp [wt, wt1]⟩) (hB g g.2 1 2 ⟨0, by simp [wt, wt1]⟩)
      (hB g g.2 2 1 ⟨-1, by simp [wt, wt1]⟩)
    rw [hp g g.2, h11 g g.2] at hcp
    have hc2 : (corner (r g).mat).charpoly = (X - C (Φ g : κ)) * (X - C ((Φ g)⁻¹ : κˣ).1) := by
      apply mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : κ))
      rw [← hcp]
      ring
    rw [show UpperTheory.V.Pr.gm ρ g = corner (r g).mat from hρ g, hc2]
    simp [chPoly, Fin.prod_univ_two, χ]
  · intro W hW
    exact hirr W (fun g hg v hv => by simpa [hρ] using hW ⟨g, hg⟩ trivial v hv)

private theorem mat_mul_eq_of_mat_eq_one {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c g : G)
    (h : (r c).mat = 1) : (r (g * c)).mat = (r g).mat := by
  have hc : (r c).left = 1 := Units.ext h
  rw [map_mul]
  simp [GG.mat, SemidirectProduct.mul_left, hc]

private theorem mat_pow_of_mult_one {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (r : G →* GG 3 R)
    (hm : HasMult η r) (g : G) (hg : η g = 1) (n : ℕ) : (r (g ^ n)).mat = (r g).mat ^ n := by
  induction n with
  | zero => simp [GG.mat]
  | succ n ih =>
    rw [pow_succ, map_mul, pow_succ, ← ih]
    have hr : (r (g ^ n)).right = 1 := by rw [hm, map_pow, hg, one_pow]
    show (((r (g ^ n) * r g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      ((r (g ^ n)).left : Matrix (Fin 3) (Fin 3) R) * (r g).left
    rw [SemidirectProduct.mul_left, hr, map_one, MulAut.one_apply, Units.val_mul]

private theorem det_up_lemma_3 {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A)
    (hM : ∀ a b, wt a b < 0 → M a b = 0) (a : Fin 3) : (scalar (Fin 3) (M a a) - M).det = 0 := by
  have h10 := hM 1 0 (by simp [wt, wt1])
  have h20 := hM 2 0 (by simp [wt, wt1])
  have h21 := hM 2 1 (by simp [wt, wt1])
  rw [det_fin_three]
  fin_cases a <;> simp [h10, h20, h21]

private theorem det_scalar_diag_sub_triangular_eq_zero {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A)
    (hM : ∀ a b, 0 < wt a b → M a b = 0) (a : Fin 3) : (scalar (Fin 3) (M a a) - M).det = 0 := by
  have h01 := hM 0 1 (by simp [wt, wt1])
  have h02 := hM 0 2 (by simp [wt, wt1])
  have h12 := hM 1 2 (by simp [wt, wt1])
  rw [det_fin_three]
  fin_cases a <;> simp [h01, h02, h12]

theorem UpperTheory.V.Pr.constOfChar :
    UpperTheory.V.Pr.ConstOfChar := by
  intro G k A _ _ _ _ _ _ _ h2 η Ψ c g₁ hMk r hm hent hN U hU hchar
  have hcp : ∀ g, η g = 1 → (r g).mat.charpoly = ((r0 η Ψ g).mat).charpoly.map (algebraMap k A) := by
    intro g hg
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    apply charpoly_const (r g).mat (r0 η Ψ g).mat (r0 η Ψ (g ^ n)).mat n hn (hent g)
    rw [← mat_pow_of_mult_one η r hm g hg n]
    exact hchar _ hgn (by rw [map_pow, hg, one_pow])
  have hdiagK : ∀ g, η g = 1 → ∀ a, ((scalar (Fin 3) ((r g).mat a a)) - (r g).mat).det = 0 →
      (r g).mat a a = algebraMap k A ((r0 η Ψ g).mat a a) :=
    fun g hg a ha => diag_const _ _ (hent g) (hcp g hg) a ha
  have hzu : IsUnit (zeta c g₁ r) := by
    have hsub : zeta c g₁ r - algebraMap k A (zeta c g₁ (r0 η Ψ)) ∈ maximalIdeal A := by
      have e1 := hent g₁ 0 0
      have e2 := hent (gstar c g₁) 0 0
      have he : zeta c g₁ r - algebraMap k A (zeta c g₁ (r0 η Ψ)) =
          ((r g₁).mat - (r0 η Ψ g₁).mat.map (algebraMap k A)) 0 0 -
            ((r (gstar c g₁)).mat - (r0 η Ψ (gstar c g₁)).mat.map (algebraMap k A)) 0 0 := by
        simp [zeta, zmat]
        ring
      rw [he]
      exact Ideal.sub_mem _ e1 e2
    have hu : IsUnit (algebraMap k A (zeta c g₁ (r0 η Ψ))) := (zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ c g₁ hMk).2.map _
    by_contra hnu
    have hm1 := Ideal.sub_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hnu) hsub
    rw [sub_sub_cancel] at hm1
    exact (IsLocalRing.mem_maximalIdeal _).1 hm1 hu
  let f : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hf : Function.Injective f := IsFractionRing.injective A (FractionRing A)
  let r' : G →* GG 3 (FractionRing A) := (GG.map f).comp r
  have hm' : HasMult η r' := fun g => hm g
  have hN' : Normalised c g₁ r' := normalised_map f hN
  have hmat' : ∀ g, (r' g).mat = (r g).mat.map f := fun g => GG.map_mat f (r g)
  have hz' : zeta c g₁ r' ≠ 0 := by
    show zmat c g₁ r' 0 0 ≠ 0
    rw [zmat_map]
    intro h0
    exact hzu.ne_zero (hf (h0.trans (map_zero f).symm))
  have h2A : (2 : A) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap k A).injective
    rw [map_ofNat, map_zero]
    exact h0
  have h2' : (2 : FractionRing A) ≠ 0 := by
    intro h0
    apply h2A
    apply hf
    rw [map_ofNat, map_zero]
    exact h0
  let Φ : G →* (FractionRing A)ˣ := (Units.map (f.comp (algebraMap k A)).toMonoidHom).comp Ψ
  have hp' : ∀ g ∈ η.ker, (r' g).mat.charpoly =
      (X - C (Φ g : FractionRing A)) * (X - C 1) * (X - C ((Φ g)⁻¹ : (FractionRing A)ˣ).1) := by
    intro g hg
    rw [hmat', Matrix.charpoly_map, hcp g hg, charpoly_diagonal_character_rep, Polynomial.map_map]
    simp [Φ, Polynomial.map_mul, Polynomial.map_sub]
  have hUpT : Upper η r' → Upper η r := by
    intro h g hg a b hab
    apply hf
    rw [map_zero]
    have := h g hg a b hab
    rw [hmat'] at this
    exact this
  have hLoT : Lower η r' → Lower η r := by
    intro h g hg a b hab
    apply hf
    rw [map_zero]
    have := h g hg a b hab
    rw [hmat'] at this
    exact this
  have hUL : Upper η r ∨ Lower η r := by
    rcases shape_cases η r' c g₁ h2' hm' hMk.ηc hMk.ηg hN' hz' with hI | hUp' | hLo' | hII
    · exact absurd hI (not_typeI η Φ r' hm' hp')
    · exact Or.inl (hUpT hUp')
    · exact Or.inr (hLoT hLo')
    · exfalso
      apply not_typeII η Φ r' hm' hp' hII.1 _ hII
      intro g hg
      have hB : ∀ a b, Odd (wt a b) → (r g).mat a b = 0 := by
        intro a b hab
        apply hf
        rw [map_zero]
        have := hII.1 g hg a b hab
        rw [hmat'] at this
        exact this
      have hcpb := charpoly_block (r g).mat (hB 0 1 ⟨0, by simp [wt, wt1]⟩) (hB 1 0 ⟨-1, by simp [wt, wt1]⟩)
        (hB 1 2 ⟨0, by simp [wt, wt1]⟩) (hB 2 1 ⟨-1, by simp [wt, wt1]⟩)
      have hdet : (scalar (Fin 3) ((r g).mat 1 1) - (r g).mat).det = 0 := by
        rw [← Matrix.eval_charpoly, hcpb]
        simp
      rw [hmat', Matrix.map_apply, hdiagK g hg 1 hdet]
      simp [GG.mat, unitaryThreeReflection_left, tor_val, wt1]
  have hdk : ∀ g, η g = 1 → ∀ a, (r g).mat a a = algebraMap k A ((r0 η Ψ g).mat a a) := by
    intro g hg a
    apply hdiagK g hg a
    rcases hUL with hu | hl
    · exact det_up_lemma_3 _ (fun a b hab => hu g hg a b hab) a
    · exact det_scalar_diag_sub_triangular_eq_zero _ (fun a b hab => hl g hg a b hab) a
  refine ⟨hUL, fun g a => ?_⟩
  by_cases hg : η g = 1
  · exact hdk g hg a
  · have hneg : η g = -1 := (Int.units_eq_one_or (η g)).resolve_left hg
    have hgc : η (g * c) = 1 := by
      rw [map_mul, hneg, hMk.ηc]
      rfl
    have hrc : (r0 η Ψ c).mat = 1 := by
      simp [GG.mat, unitaryThreeReflection_left, hMk.Ψc]
    rw [← mat_mul_eq_of_mat_eq_one r c g hN.atc, ← mat_mul_eq_of_mat_eq_one (r0 η Ψ) c g hrc]
    exact hdk _ hgc a
