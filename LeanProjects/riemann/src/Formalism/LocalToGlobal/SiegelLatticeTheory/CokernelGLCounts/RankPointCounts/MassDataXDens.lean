import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MassDataPosAllOf

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.Pf.MassDataX

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_sub_eta_nonneg (η : ℝ) (hη : η = 1 ∨ η = -1) (q i : ℕ) : 0 ≤ 1 - η ^ i / ((q : ℕ) : ℝ) ^ i := by
  have h1 : |η ^ i| = 1 := by
    rcases hη with rfl | rfl <;> simp [abs_pow]
  rcases Nat.eq_zero_or_pos (q ^ i) with h | h
  · have h' : ((q : ℕ) : ℝ) ^ i = 0 := by exact_mod_cast h
    rw [h', div_zero]
    norm_num
  · have h' : (1 : ℝ) ≤ ((q : ℕ) : ℝ) ^ i := by exact_mod_cast (show 1 ≤ q ^ i from h)
    have h2 : η ^ i / ((q : ℕ) : ℝ) ^ i ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (le_abs_self _).trans (h1.le.trans h')
    linarith

theorem etaP_pm {D : D7} (p : PlF D) : eta₃ p = 1 ∨ eta₃ p = -1 := by
  unfold eta₃
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem aPD_nonneg {D : D7} (p : PlF D) (T : ℕ) : 0 ≤ aPD p T := by
  unfold aPD
  apply Finset.prod_nonneg
  intro i _
  exact one_sub_eta_nonneg _ (etaP_pm p) _ _

theorem alpD_nonneg {D : D7} (u u' : D.what₂.Word) (p : PlF D) : 0 ≤ alpD u u' p := by
  unfold alpD
  split_ifs
  · exact aPD_nonneg p _
  · exact mul_nonneg (aPD_nonneg p _) (aPD_nonneg p _)

theorem densP_nonneg {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (T T' : D.host.E) (Z : MatZ D) (p : PlF D) :
    0 ≤ densP L δ ϖ T T' Z p := by
  unfold densP Formalism.MainNotions.S.Loc.HermSp.dens
  positivity

theorem densNonnegAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.DensNonnegAll := by
  intro D T u u' Lsp ϖ
  apply div_nonneg
  · unfold supDens
    apply Real.sSup_nonneg
    intro d hd
    simp only [densSet, Set.mem_setOf_eq] at hd
    obtain ⟨Z, -, rfl⟩ := hd
    exact tprod_nonneg fun p => densP_nonneg _ _ _ _ _ _ _
  · exact tprod_nonneg fun p => alpD_nonneg u u' p

end Formalism.L2.SG.Pf.MassDataX
