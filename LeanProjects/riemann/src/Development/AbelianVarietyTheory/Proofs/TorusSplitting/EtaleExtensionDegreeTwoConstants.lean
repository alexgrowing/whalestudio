import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstantStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogCardComponentsLeOfRowsBoundStatement
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

private lemma etexnum_one_le_rd (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ I2.PT.rd E := by
  unfold I2.PT.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h

theorem etEx_deg_two : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → 1 ≤ q → Real.log q ≤ 70 * large₂.sc.L → ETEx h (WeightFamilies.PPv D large₂ 200000 2) (EtArch h (I2.th (E := D.host.E) q R0) (200000 * zBase large₂ ^ 2)) := by
  intro D T h large₂ hrows DF q R0 hrun hq lq
  have hP : WeightFamilies.PPv D large₂ 200000 2 = 200000 * zBase large₂ ^ 2 := by
    unfold WeightFamilies.PPv
    rw [Real.rpow_two]
  rw [hP]
  refine GlobalTheory.T.exists_cuspForm_four_clauses_explicitConstant D T h DF q R0 _ _ hrun (fun j hj => ?_) (by positivity)
  rw [min_self]
  have hN := GlobalTheory.T.log_card_components_le_of_rows_bound D T h large₂ hrows j hj T.σ₀ T.good_σ₀
  obtain ⟨hL, lr, lρ, lf, -, hf⟩ := hrows
  have hm := D.R.two_le_m
  have hk := D.R.f_le_k
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmr : D.R.m ≤ D.R.r := by
    unfold Ranks.r
    unfold Ranks.n at hn
    omega
  have hz : zBase large₂ = (I2.PT.f D.host.E : ℝ) * D.R.r * large₂.sc.L := by
    rw [hostSize_f]; rfl
  rw [hz] at hN ⊢
  exact (archimedeanBoundTotalConstant_size D.host.E D.R.r q D.R.m _ large₂.sc.L hL (by rw [hostSize_f]; omega) (by omega) (by omega) hmr hq
    (etexnum_one_le_rd _) lρ (by rw [hostSize_f]; exact lf) lr lq hN).2

end GlobalTheory.EtaAn
