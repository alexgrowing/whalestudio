import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ExistsEigenform

open CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Br.minNew :
    UpperTheory.V.Br.MinNew := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hN hk χ g
    by_cases hnew : ∀ (M' : ℕ), M' ∣ N → M' ≠ N →
        ∀ (g' : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M')) ↑k)
          (χ' : DirichletCharacter ℂ M'), HasChar k χ' ⇑g' →
          (∀ᶠ (p : ℕ) in Filter.cofinite, Nat.Prime p → IsEigAt k χ' (⇑g') p (coef (⇑g.f) p)) → g' = 0
    · refine ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g.f, χ, g.char, g.one,
        fun p hp _ => g.eig p hp, hnew⟩, hN, g, rfl, Filter.Eventually.of_forall fun _ _ => rfl⟩
    · push_neg at hnew
      obtain ⟨M', hdvd, hne, g', χ', hc, hev, hg0⟩ := hnew
      have hM0 : M' ≠ 0 := by
        rintro rfl
        exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hdvd)
      haveI : NeZero M' := ⟨hM0⟩
      have hlt : M' < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hne
      obtain ⟨g'', hg''⟩ := UpperTheory.V.Br.eigEx M' k hk χ' g' hc hg0 (coef (⇑g.f))
      obtain ⟨f, hf, h, hhf, hha⟩ := ih M' hlt k hk χ' g''
      refine ⟨f, hf, h, hhf, ?_⟩
      filter_upwards [hha, hev] with p h1 h2 hp
      rw [h1 hp, hg'' p hp (h2 hp)]
      rfl
