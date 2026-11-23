import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsLocPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem emb_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG 3 R)
    (a b : Fin 3 ⊕ Fin 3) : emb (GG.map f x) a b = f (emb x a b) := by
  have h : (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) =
      (theta x.left : Matrix (Fin 3) (Fin 3) R).map f :=
    (congrArg Units.val (map_theta f x.left)).symm
  show (if (GG.map f x).right = 1 then Matrix.fromBlocks (GG.map f x).mat 0 0 (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S)
    else Matrix.fromBlocks 0 (GG.map f x).mat (theta (GG.map f x).left : Matrix (Fin 3) (Fin 3) S) 0) a b =
    f ((if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) a b)
  rw [h, GG.map_mat, GG.map_right]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;> simp

private theorem mat_eq_emb {R : Type} [CommRing R] (x : GG 3 R) (a b : Fin 3) :
    x.mat a b = emb x (.inl a) (.inl b) + emb x (.inl a) (.inr b) := by
  show _ = (if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) _ _ +
    (if x.right = 1 then Matrix.fromBlocks x.mat 0 0 (theta x.left : Matrix (Fin 3) (Fin 3) R)
    else Matrix.fromBlocks 0 x.mat (theta x.left : Matrix (Fin 3) (Fin 3) R) 0) _ _
  split_ifs <;> simp

private theorem emb_tor {R : Type} [CommRing R] (t : Rˣ) :
    emb (GG.ofGL (tor R t)) = Matrix.diagonal fun i => ((t ^ wt6 i : Rˣ) : R) := by
  show (if (1 : ℤˣ) = 1 then Matrix.fromBlocks (tor R t : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R t) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R t : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R t) : Matrix (Fin 3) (Fin 3) R) 0) = _
  rw [if_pos rfl, theta_tor, tor_val, Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> rfl

private theorem emb_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) :
    emb (conjBy (tor R t) r g) a b = ((t ^ (wt6 a - wt6 b) : Rˣ) : R) * emb (r g) a b := by
  have h : conjBy (tor R t) r g = GG.ofGL (tor R t) * r g * GG.ofGL (tor R t⁻¹) := by
    rw [map_inv, map_inv]; rfl
  rw [h, map_mul, map_mul, emb_tor, emb_tor, Matrix.mul_diagonal, Matrix.diagonal_mul, _root_.zpow_sub,
    Units.val_mul, _root_.inv_zpow]
  ring

private theorem unitaryEmbedding_residualRep_eq_zero_of_weight_ne {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G)
    (a b : Fin 3 ⊕ Fin 3) (h : wt6 a ≠ wt6 b) : emb (r0 η Ψ g) a b = 0 := by
  show (if (r0 η Ψ g).right = 1 then Matrix.fromBlocks (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R) 0 0
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) else Matrix.fromBlocks 0 (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R)
    (theta (tor R (Ψ g)) : Matrix (Fin 3) (Fin 3) R) 0) a b = 0
  rw [theta_tor, tor_val]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | rfl
    | exact Matrix.diagonal_apply_ne (i := a) (j := b) (fun i => ((Ψ g ^ wt1 i : Rˣ) : R)) (by rintro rfl; exact h rfl)

private theorem map_reducible_three_dim {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] (η : G →* ℤˣ) (Ψ : G →* Oˣ)
    (g : G) : GG.map (residue O) (r0 η Ψ g) = rbar O η Ψ g := by
  refine SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (residue O) = tor _ (barChar O Ψ g)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (residue O).toMonoidHom) (Ψ g) (wt1 i))

private theorem res_zpow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) (j : ℤ) : res O R ((t ^ j : Rˣ) : R) = 1 := by
  have h1 : Units.map (res O R : R →* ResidueField O) t = 1 := Units.ext ht
  have h2 := map_zpow (Units.map (res O R : R →* ResidueField O)) t j
  rw [h1, _root_.one_zpow] at h2
  exact congrArg Units.val h2

private def torLift {O : Type} [CommRing O] [IsLocalRing O] {G : Type} [Group G] [TopologicalSpace G]
    {η : G →* ℤˣ} {Ψ : G →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R) (t : Rˣ)
    (ht : res O R t = 1) : GLift O η Ψ R where
  hom := conjBy (tor R t) r.hom
  cont a b N := by
    simp only [(conjBy_tor r.hom t).1, map_mul]
    exact (r.cont a b N).comp fun y => Ideal.Quotient.mk _ ((t ^ wt a b : Rˣ) : R) * y
  red g := by
    rw [← r.red g]
    refine SemidirectProduct.ext (Units.ext ?_) ((conjBy_tor r.hom t).2.1 g)
    ext a b
    show res O R ((conjBy (tor R t) r.hom g).mat a b) = res O R ((r.hom g).mat a b)
    rw [(conjBy_tor r.hom t).1, map_mul, res_zpow t ht, one_mul]

private theorem congOne_tor {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    (t : Rˣ) (ht : res O R t = 1) : CongOne (maximalIdeal R) (tor R t) := by
  intro a b
  rw [Matrix.sub_apply, tor_val]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← res_eq_zero_iff O, map_sub, res_zpow t ht, map_one, sub_self]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_self]
    exact zero_mem _

theorem UpperTheory.V.U3.exists_locPres :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {η : H →* ℤˣ} {Ψ : H →* Oˣ}
      (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R), IsLocallyConstant η → LocGood U I → ∃ WB : WPres O ℤ (U.R ⧸ I), IsLocPres U I WB := by
  intro O _ _ _ _ _ H _ _ _ η Ψ U I _ hL
  obtain ⟨x, τ, _, w, φ, -, hφ, -⟩ := hL.chart
  have hne : I ≠ ⊤ := hφ.ker ▸ RingHom.ker_ne_top φ
  haveI : Nontrivial (U.R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (U.R ⧸ I) :=
    co_quot O U.R (U.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hent : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : (U.R ⧸ I) →ₐ[O] R') g a b,
      f (emb (push (Ideal.Quotient.mkₐ O I) U.r.hom g) a b) =
        emb ((U.r.map (f.comp (Ideal.Quotient.mkₐ O I))).hom g) a b := fun R' _ _ _ f g a b =>
    (emb_map (f : (U.R ⧸ I) →+* R') _ a b).symm
  obtain ⟨W, u, hu, he⟩ := coord_grading O ℤ (U.R ⧸ I) (H × (Fin 3 ⊕ Fin 3) × (Fin 3 ⊕ Fin 3))
    (fun s => emb (push (Ideal.Quotient.mkₐ O I) U.r.hom s.1) s.2.1 s.2.2 -
      algebraMap O _ (emb (r0 η Ψ s.1) s.2.1 s.2.2)) (fun s => wt6 s.2.1 - wt6 s.2.2)
    (fun ⟨g, a, b⟩ => by
      have h1 := emb_map (res O (U.R ⧸ I) : (U.R ⧸ I) →+* ResidueField O)
        ((U.r.map (Ideal.Quotient.mkₐ O I)).hom g) a b
      rw [GLift.red, ← map_reducible_three_dim, emb_map] at h1
      rw [← res_eq_zero_iff O, map_sub, AlgHom.commutes, sub_eq_zero]
      exact h1.symm)
    (fun R' _ _ _ f f' h => by
      have h1 : U.r.map (f.comp (Ideal.Quotient.mkₐ O I)) = U.r.map (f'.comp (Ideal.Quotient.mkₐ O I)) := by
        refine GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl)
        ext a b
        have h2 : ∀ a b, emb ((U.r.map (f.comp (Ideal.Quotient.mkₐ O I))).hom g) a b =
            emb ((U.r.map (f'.comp (Ideal.Quotient.mkₐ O I))).hom g) a b := fun a b => by
          have := h (g, a, b)
          simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
          rw [← hent, ← hent]
          exact this
        refine (mat_eq_emb _ a b).trans (Eq.trans ?_ (mat_eq_emb _ a b).symm)
        rw [h2, h2]
      exact Ideal.Quotient.algHom_ext O (((U.rep R').2 _ trivial).unique h1 rfl))
    (fun R' _ _ _ f t ht => by
      have hk : I ≤ RingHom.ker (f.comp (Ideal.Quotient.mkₐ O I)) := fun y hy => by
        show f (Ideal.Quotient.mk I y) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.2 hy, map_zero]
      obtain ⟨f₁, hf₁, hk₁⟩ := hL.conj R' (U.r.map (f.comp (Ideal.Quotient.mkₐ O I)))
        (torLift _ (t (Multiplicative.ofAdd 1)) (ht _)) _ (congOne_tor _ (ht _)) rfl ⟨_, rfl, hk⟩
      have hc : (Ideal.Quotient.liftₐ I f₁ hk₁).comp (Ideal.Quotient.mkₐ O I) = f₁ := AlgHom.ext fun _ => rfl
      have htj : ∀ j : ℤ, t (Multiplicative.ofAdd 1) ^ j = t (Multiplicative.ofAdd j) := fun j => by
        rw [← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
      refine ⟨Ideal.Quotient.liftₐ I f₁ hk₁, fun ⟨g, a, b⟩ => ?_⟩
      dsimp only
      rw [map_sub, map_sub f, AlgHom.commutes, AlgHom.commutes, hent, hent, hc, hf₁, mul_sub, ← htj (wt6 a - wt6 b)]
      congr 1
      · exact emb_conj _ _ g a b
      · by_cases hab : wt6 a = wt6 b
        · simp [hab]
        · simp [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab])
  refine ⟨W, fun i => ⟨(u i).1, (u i).2.1, (u i).2.2, (hu i).2, (hu i).1⟩, fun g a b => ?_⟩
  have h1 := he (g, a, b)
  have h2 : algebraMap O (U.R ⧸ I) (emb (r0 η Ψ g) a b) ∈ W.part (wt6 a - wt6 b) := by
    by_cases hab : wt6 a = wt6 b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : U.R ⧸ I) ∈ W.part 0)
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b hab, map_zero]
      exact zero_mem _
  simpa only [sub_add_cancel] using add_mem h1 h2
