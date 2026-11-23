import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem UpperTheory.V.X.So.vanE_wt_rev (a b : Fin 3) : U3.wt b.rev a.rev = U3.wt a b := by
  revert a b
  decide

private theorem UpperTheory.V.X.So.vanE_char {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : UnitaryThreeInertia.Frame O G Γ ι) (j : ℤ) (s : ℕ) (g : Γ) :
    (lineChar F j s g : O) = ((F.Ψ g ^ j : Oˣ) : O) * (if F.η g = 1 then 1 else (-1) ^ s) := by
  rcases Int.units_eq_one_or (F.η g) with h | h
  · simp [lineChar, etaO, h]
  · simp [lineChar, etaO, h]

private theorem UpperTheory.V.X.So.vanE_ad {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : UnitaryThreeInertia.Frame O G Γ ι) (s : ℕ) (g : Γ) (X : Matrix (Fin 3) (Fin 3) O) (a b : Fin 3) :
    U3.adRep (U3.r0 F.η F.Ψ) g X a b - (-1) ^ s * U3.adRep (U3.r0 F.η F.Ψ) g X b.rev a.rev =
      (lineChar F (U3.wt a b) s g : O) * (X a b - (-1) ^ s * X b.rev a.rev) := by
  rw [U3.adRep_baseLift_apply, U3.adRep_baseLift_apply, So.vanE_char, So.vanE_wt_rev, Fin.rev_rev, Fin.rev_rev]
  have h : ((-1 : O) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow]; simp
  split_ifs
  · ring
  · linear_combination (((F.Ψ g ^ U3.wt a b : Oˣ) : O) * X b.rev a.rev) * h

theorem UpperTheory.V.X.So.vanEOf :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (G Γ ι : Type) [Group G] [Group Γ] [TopologicalSpace G] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G Γ ι), (∀ j : ℤ, j ≤ 0 → ∀ s : ℕ, LineVan F j (lineChar F j s)) → F.VanE := by
  intro O _ _ _ _ G Γ ι _ _ _ _ F hL j hj γ hγw hcoc hcont hN hI hD
  have hz : ∀ g a b, U3.wt a b ≠ j → γ g a b = 0 := fun g a b h => hγw g a b h
  let z : Fin 3 → Fin 3 → ℕ → Γ → O := fun a b s g => γ g a b - (-1) ^ s * γ g b.rev a.rev
  have key : ∀ (a b : Fin 3) (s : ℕ), CobOn (lineChar F (U3.wt a b) s) (z a b s) ⊤ := by
    intro a b s
    by_cases hw : U3.wt a b = j
    · have hcz : Coc (lineChar F j s) (z a b s) := by
        intro g h
        have e := UpperTheory.V.X.So.vanE_ad F s g (γ h) a b
        rw [hw] at e
        simp only [z, hcoc g h, Matrix.add_apply]
        linear_combination e
      have hcc : Alg.AdicCont (IsLocalRing.maximalIdeal O) (z a b s) := by
        intro N
        have h1 := hcont a b N
        have h2 := hcont b.rev a.rev N
        have h3 := h1.comp₂ h2 (fun x y => x - Ideal.Quotient.mk _ ((-1 : O) ^ s) * y)
        convert h3 using 1
        funext g
        simp [z, map_sub, map_mul]
      have hnz : ∀ v ∉ F.Tb, ∀ t ∈ F.Nv v, z a b s ((F.loc v) t) = 0 := by
        intro v hv t ht
        simp [z, hN v hv t ht]
      have hiz : j = 0 → ∀ v ∈ F.Tb, ∀ t ∈ F.Iv v, z a b s ((F.loc v) t) = 0 := by
        intro h0 v hv t ht
        simp [z, hI h0 v hv t ht]
      have hdz : j < 0 → ∃ y, ∀ (g : ↥(F.D F.vl)), (F.ηv F.vl) g = 1 →
          z a b s ((F.loc F.vl) g) = ↑((lineChar F j s) ((F.loc F.vl) g)) * y - y := by
        intro hneg
        obtain ⟨Y, -, hY⟩ := hD hneg
        refine ⟨-(Y a b - (-1) ^ s * Y b.rev a.rev), fun g hg => ?_⟩
        have e := UpperTheory.V.X.So.vanE_ad F s ((F.loc F.vl) g) Y a b
        rw [hw] at e
        simp only [z, hY g hg, U3.cob, Matrix.sub_apply]
        linear_combination -e
      rw [hw]
      exact hL j hj s (z a b s) hcz hcc hnz hiz hdz
    · apply cobOn_of_eq_zero
      intro g _
      have h1 := hz g a b hw
      have h2 := hz g b.rev a.rev (by rw [UpperTheory.V.X.So.vanE_wt_rev]; exact hw)
      simp [z, h1, h2]
  have key0 : ∀ a b, ∃ c : O, c ≠ 0 ∧ ∃ m : O, ∀ g ∈ (⊤ : Subgroup Γ),
      c * z a b 0 g = ↑((lineChar F (U3.wt a b) 0) g) * m - m := fun a b => key a b 0
  have key1 : ∀ a b, ∃ c : O, c ≠ 0 ∧ ∃ m : O, ∀ g ∈ (⊤ : Subgroup Γ),
      c * z a b 1 g = ↑((lineChar F (U3.wt a b) 1) g) * m - m := fun a b => key a b 1
  choose c0 hc0 m0 hm0 using key0
  choose c1 hc1 m1 hm1 using key1
  set A : O := ∏ a, ∏ b, c0 a b * c1 a b with hA
  have hd0 : ∀ a b, ∃ k, A = c0 a b * k := fun a b =>
    (dvd_mul_right _ _).trans ((Finset.dvd_prod_of_mem (fun b => c0 a b * c1 a b) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a => ∏ b, c0 a b * c1 a b) (Finset.mem_univ a)))
  have hd1 : ∀ a b, ∃ k, A = c1 a b * k := fun a b =>
    (dvd_mul_left _ _).trans ((Finset.dvd_prod_of_mem (fun b => c0 a b * c1 a b) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a => ∏ b, c0 a b * c1 a b) (Finset.mem_univ a)))
  choose k0 hk0 using hd0
  choose k1 hk1 using hd1
  have hP0 : ∀ a b g, A * z a b 0 g = ↑((lineChar F (U3.wt a b) 0) g) * (k0 a b * m0 a b) - k0 a b * m0 a b := by
    intro a b g
    linear_combination k0 a b * hm0 a b g (Subgroup.mem_top g) + z a b 0 g * hk0 a b
  have hP1 : ∀ a b g, A * z a b 1 g = ↑((lineChar F (U3.wt a b) 1) g) * (k1 a b * m1 a b) - k1 a b * m1 a b := by
    intro a b g
    linear_combination k1 a b * hm1 a b g (Subgroup.mem_top g) + z a b 1 g * hk1 a b
  have hAne : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Finset.prod_ne_zero_iff.mpr fun b _ => mul_ne_zero (hc0 a b) (hc1 a b)
  have h4 : (4 : O) ≠ 0 := by norm_num
  let X : Matrix (Fin 3) (Fin 3) O := Matrix.of fun a b =>
    -((k0 a b * m0 a b - k0 b.rev a.rev * m0 b.rev a.rev) + (k1 a b * m1 a b + k1 b.rev a.rev * m1 b.rev a.rev))
  refine ⟨4 * A, mul_ne_zero h4 hAne, X, fun g => ?_⟩
  ext a b
  have e0 := hP0 a b g
  have e0' := hP0 b.rev a.rev g
  have e1 := hP1 a b g
  have e1' := hP1 b.rev a.rev g
  rw [UpperTheory.V.X.So.vanE_wt_rev] at e0' e1'
  rw [UpperTheory.V.X.So.vanE_char] at e0 e0' e1 e1'
  simp only [z, Fin.rev_rev] at e0 e0' e1 e1'
  simp only [U3.cob, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, U3.adRep_baseLift_apply, X, Matrix.of_apply, Fin.rev_rev]
  by_cases hη : F.η g = 1
  · simp only [hη, if_true] at e0 e0' e1 e1' ⊢
    linear_combination e0 - e0' + e1 + e1'
  · simp only [hη, if_false] at e0 e0' e1 e1' ⊢
    linear_combination e0 - e0' + e1 + e1'
