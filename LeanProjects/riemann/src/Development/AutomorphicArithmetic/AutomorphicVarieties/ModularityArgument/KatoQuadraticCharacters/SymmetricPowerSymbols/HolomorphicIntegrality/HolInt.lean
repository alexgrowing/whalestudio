import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

open Polynomial GlobalTheory.KZ.JInt in
private theorem hol_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (Tw : Tower Ω ε) (f : Tw.K)
    (hf : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ Tw.an f = (φ : Mero)) : IsIntegral (Algebra.adjoin Ω {Tw.jK}) f := by
  classical
  obtain ⟨M, hM, hfix⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨φ, hφ, hφd⟩ := hf
  let orb : SL(2, ℤ) → Tw.K := fun γ => Tw.sl (ofSL γ) f
  have hfac : ∀ γ γ' : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ → orb γ' = orb γ := by
    intro γ γ' h
    have hk : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have he : γ' = (γ' * γ⁻¹) * γ := by group
    show Tw.sl (ofSL γ') f = Tw.sl (ofSL γ) f
    conv_lhs => rw [he]
    rw [map_mul, Tw.sl_mul, hfix _ hk]
  have hfin : (Set.range orb).Finite := by
    let g' : SL(2, ZMod M) → Tw.K := fun x =>
      if h : ∃ γ, Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = x then orb h.choose else 0
    refine (Set.finite_range g').subset ?_
    rintro _ ⟨γ, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ, ?_⟩
    have h : ∃ γ', Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'
        = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ := ⟨γ, rfl⟩
    simp only [g', dif_pos h]
    exact hfac γ h.choose h.choose_spec
  set S := hfin.toFinset with hSdef
  have hmemS : ∀ s, s ∈ S ↔ ∃ γ, orb γ = s := by
    intro s
    rw [hSdef, Set.Finite.mem_toFinset, Set.mem_range]
  set P : Polynomial Tw.K := ∏ s ∈ S, (X - C s) with hPdef
  have hPmon : P.Monic := monic_prod_of_monic _ _ (fun s _ => monic_X_sub_C s)
  have hroot : P.eval f = 0 := by
    rw [hPdef, eval_prod]
    refine Finset.prod_eq_zero ((hmemS f).2 ⟨1, ?_⟩) ?_
    · show Tw.sl (ofSL 1) f = f
      rw [map_one, Tw.sl_one]
    · simp
  have hinv : ∀ δ : SL(2, ℤ), ∀ n, Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hσS : S.image (Tw.sl (ofSL δ)) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        obtain ⟨γ, rfl⟩ := (hmemS s).1 hs
        refine (hmemS _).2 ⟨γ * δ, ?_⟩
        show Tw.sl (ofSL (γ * δ)) f = Tw.sl (ofSL δ) (Tw.sl (ofSL γ) f)
        rw [map_mul, Tw.sl_mul]
      · rw [Finset.card_image_of_injective _ (Tw.sl (ofSL δ)).injective]
    have hmap : P.map ((Tw.sl (ofSL δ)).toRingEquiv : Tw.K →+* Tw.K) = P := by
      rw [hPdef, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hσS]
      rw [Finset.prod_image (fun x _ y _ h => (Tw.sl (ofSL δ)).injective h)]
      rfl
    have h2 := congrArg (fun p => p.coeff n) hmap
    simp only [Polynomial.coeff_map] at h2
    exact h2
  have hS : ∀ s ∈ S, s ∈ holR Tw := by
    intro s hs
    obtain ⟨γ, rfl⟩ := (hmemS s).1 hs
    exact ⟨fun z => φ (mob (ofSL γ) z), hφ.comp (mob_diff _) (fun z hz => mob_im _ hz),
      Tw.an_sl _ _ _ hφd⟩
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    have hl : P ∈ lifts (holR Tw).subtype := by
      rw [hPdef]
      refine Subsemiring.prod_mem _ (fun s hs => ?_)
      exact ⟨X - C ⟨s, hS s hs⟩, by simp⟩
    intro n
    obtain ⟨c, hc⟩ := (lifts_iff_coeff_lifts P).1 hl n
    rw [← hc]
    exact c.2
  have hadj : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw ε.injective
      (by obtain ⟨ψ, h1, h2⟩ := Tw.j_hol; exact ⟨ψ, h2, h1⟩) _ (fun γ => hinv γ n) (hhol n)
  have hl2 : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hadj n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl2 hPmon
  refine ⟨q, hqm, ?_⟩
  rw [← eval_map, hq, hroot]

theorem UpperTheory.V.Z.Kato.Sym.KU.hol :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an f = (φ : Mero)) → ∀ W, X.OverY W → f ∈ W := by
  intro Ω _ _ _ ε X f hf W hW
  apply vs_mem_of_isIntegral
  obtain ⟨q, hqm, hq⟩ := hol_int ε X f hf
  let ι : Algebra.adjoin Ω {X.jK} →+* W :=
    { toFun := fun a => ⟨a.1, X.adjoin_le_of_overY W hW a.1 a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨q.map ι, hqm.map ι, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hq
