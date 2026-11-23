import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

namespace Formalism.G

private lemma constantCoeff_powerSeries_subst_eq_zero' {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (p : PowerSeries R)
    (hp : PowerSeries.constantCoeff p = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a p) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hp]
  · simp [ha, hd.ne']

private lemma mvPowerSeries_subst_powerSeries_subst_eq_subst_subst {R : Type*} [CommRing R] {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {b : MvPowerSeries σ R} (hb : PowerSeries.HasSubst b)
    (p : PowerSeries R) :
    MvPowerSeries.subst a (PowerSeries.subst b p) = PowerSeries.subst (MvPowerSeries.subst a b) p :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const hb) ha p

theorem homComp : HomComp := by
  unfold HomComp
  intro R _ F G H f g hf hg
  unfold IsHom at hf hg ⊢
  unfold atX atY at hf hg ⊢
  have hf1 : MvPowerSeries.constantCoeff f = 0 := hf.1
  have hfS : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf.1
  have hFS : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hGS : PowerSeries.HasSubst G.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) :=
    fun i => PowerSeries.HasSubst.X i
  have hu : ∀ (p : PowerSeries R), PowerSeries.constantCoeff p = 0 → ∀ i : Fin 2,
      MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) p) = 0 :=
    fun p hp i => constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X i) p hp
  have haS : MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · exact hu f hf.1 0
    · exact hu f hf.1 1
  have hbS : MvPowerSeries.HasSubst
      (![PowerSeries.subst (MvPowerSeries.X 0) g, PowerSeries.subst (MvPowerSeries.X 1) g] :
        Fin 2 → MvPowerSeries (Fin 2) R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i
    · exact hu g hg.1 0
    · exact hu g hg.1 1
  refine ⟨constantCoeff_powerSeries_subst_eq_zero' hf1 g hg.1, ?_⟩
  rw [PowerSeries.subst_comp_subst_apply hfS hFS, hf.2, ← mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS hGS, hg.2,
    MvPowerSeries.subst_comp_subst_apply hbS haS]
  congr 1
  funext i
  fin_cases i
  · show MvPowerSeries.subst
        (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
          Fin 2 → MvPowerSeries (Fin 2) R) (PowerSeries.subst (MvPowerSeries.X 0) g) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g)
    rw [mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS (hX 0), MvPowerSeries.subst_X haS,
      PowerSeries.subst_comp_subst_apply hfS (hX 0)] <;> rfl
  · show MvPowerSeries.subst
        (![PowerSeries.subst (MvPowerSeries.X 0) f, PowerSeries.subst (MvPowerSeries.X 1) f] :
          Fin 2 → MvPowerSeries (Fin 2) R) (PowerSeries.subst (MvPowerSeries.X 1) g) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (PowerSeries.subst f g)
    rw [mvPowerSeries_subst_powerSeries_subst_eq_subst_subst haS (hX 1), MvPowerSeries.subst_X haS,
      PowerSeries.subst_comp_subst_apply hfS (hX 1)] <;> rfl
theorem logIffHomGa : LogIffHomGa := by
  unfold LogIffHomGa
  intro R _ F f
  unfold IsLog IsHom FormalGroup.𝔾ₐ
  have key : PowerSeries.constantCoeff f = 0 →
      MvPowerSeries.subst (![atX f, atY f] : Fin 2 → MvPowerSeries (Fin 2) R)
        (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = atX f + atY f := by
    intro h0
    have haS : MvPowerSeries.HasSubst (![atX f, atY f] : Fin 2 → MvPowerSeries (Fin 2) R) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      fin_cases i
      · exact constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X (0 : Fin 2)) f h0
      · exact constantCoeff_powerSeries_subst_eq_zero' (MvPowerSeries.constantCoeff_X (1 : Fin 2)) f h0
    rw [MvPowerSeries.subst_add haS, MvPowerSeries.subst_X haS, MvPowerSeries.subst_X haS] <;> rfl
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, h2.trans (key h0).symm⟩, h1⟩
  · rintro ⟨⟨h0, h2⟩, h1⟩
    exact ⟨h0, h1, h2.trans (key h0)⟩
theorem substInjective : SubstInjective := substInjective_statement
theorem isCommOfRat : IsCommOfRat := is_comm_of_rat

end Formalism.G
