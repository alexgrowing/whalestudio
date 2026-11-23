import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerTopStageThetaNormFormula
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerStageNormFactorization
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfSmallRank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerNormStepOfLargeRank
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WittTowerConstantRatioEqBottom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatchingStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTower
section Units
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Units
section Descent
variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {W : G.Weil} {μ₀ : T}
end Descent
end GlobalTheory.SqTower
namespace GlobalTheory.SqTower
open GlobalTheory.SqTower
theorem tower_alt_bis : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  intro hP hK hM hL
  have H := gbig_and (_root_.GlobalTheory.T.witt_tower_top_stage_theta_norm_formula hP hK hM) (gbig_and (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) (gbig_and (_root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank hP hK hM)
    (gbig_and (_root_.GlobalTheory.T.witt_tower_norm_step_of_large_rank hP hK hM) (gbig_and (_root_.GlobalTheory.T.witt_tower_constant_ratio_eq_bottom hP hK hM) hL))))
  unfold Tower
  refine gbig_mono H ?_
  intro D T Lc sc G μ₀ C x b hμ hQ
  obtain ⟨htop, hfac, hsm, hbig, hbot, hlne⟩ := hQ
  intro W S ρ hψ hN i j t c c₀ A A' WW X c0 Λ Λ₀ hnz hc hnz₀ hc₀ hX hc0 hΛ hΛ₀
  choose Lf hLf using (hlne i j).1
  have eΛ : Λ = Lf t := hΛ.unique (hLf t).1
  have eΛ₀ : Λ₀ = Lf μ₀ := hΛ₀.unique (hLf μ₀).1
  subst eΛ eΛ₀
  have rk := ranks_exact D i j
  obtain ⟨u1, hu1⟩ := D.R.t_odd
  obtain ⟨v1, hv1⟩ := odd_sLen D
  have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
  have h3 := D.R.three_m_lt_t
  have hm : D.R.m ≤ rankV D ↑i ↑j := by
    have := D.R.m_add_three_le_k
    simp only [rankV]; unfold Ranks.r; omega
  have hpp : pp D j ≤ D.R.m := by unfold pp; omega
  have hqq : qq D j ≤ D.R.m := by unfold qq; omega
  have hpe : pp D j ≤ eTop D i j := by unfold eTop; omega
  have hqh : eTop D i j + qq D j ≤ halfRank D i j := by unfold eTop; omega
  obtain ⟨A1, A1', WW1, X1, ct, κT, hst, hct, hκT, hsq⟩ := htop W S hψ hN ρ i j
  have ec := hsq t c hnz hc
  have ec₀ := hsq μ₀ c₀ hnz₀ hc₀
  obtain ⟨lamT, hlamT⟩ := hfac W S hψ hN i j _ _ A1 A1' WW1 X1 hst
  obtain ⟨κ1, hκ1, e1⟩ := hlamT.eq_mul hct
  have hct0 : ∀ t, ct t ≠ 0 := fun t => by rw [e1 t]; exact mul_ne_zero hκ1 (hlamT.1 t)
  have hrk : A1.rank = A1'.rank + 2 * eTop D i j := by
    obtain ⟨-, -, a1, a2, -⟩ := hst
    unfold eTop; omega
  obtain ⟨B, B', W₁, Y, cY, u, κ, hY, hcY, hκ, hu, hid⟩ := descent (W := W) (μ₀ := μ₀) (hfac W S hψ hN)
    (hsm W S hψ hN) (hbig W S hψ hN) i j Lf (fun t => (hLf t).1) (qq D j) (pp D j) (eTop D i j) X1 ct hst hct hrk hpe
  obtain ⟨v, hv, hvr⟩ := hbot W S hψ hN i j A A' WW X B B' W₁ Y cY hX hY hcY
  obtain ⟨lam0, hlam0⟩ := hfac W S hψ hN i j 0 0 A A' WW X (IsBottomTri.isStageC hX)
  obtain ⟨a, ha, ea⟩ := hlam0.eq_mul hc0
  obtain ⟨b', hb', eb⟩ := hlam0.eq_mul hv
  have ec0 : ∀ t, c0 t = a / b' * (v t * cY t) := fun t => by
    rw [ea t, eb t]; field_simp
  have hLne : ∀ n : ℕ, 1 ≤ n → n ≤ halfRank D i j → Lf μ₀ (n : ℂ) ≠ 0 := fun n h1 h2 => by
    have := (hLf μ₀).2 (n : ℤ) (by omega) (by exact_mod_cast h2)
    rwa [Int.cast_natCast] at this
  have hP0 : ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ) ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => hLne _ (by omega) (by rw [mem_range] at hk; omega)
  have hP0' : ∏ k ∈ range (pp D j), Lf μ₀ ((eTop D i j + qq D j - k : ℕ) : ℂ) ≠ 0 :=
    prod_ne_zero_iff.2 fun k hk => by rw [mem_range] at hk; exact hLne _ (by omega) (by omega)
  have hU0 : ∏ k ∈ range (pp D j + qq D j), u k μ₀ ≠ 0 := prod_ne_zero_iff.2 fun k _ => (hu k μ₀).1
  have hcY0 : cY μ₀ ≠ 0 := fun h0 => by
    have := hid μ₀
    rw [h0, mul_zero, zero_mul] at this
    exact mul_ne_zero (hct0 μ₀) hP0 this
  have hκT0 := (hκT μ₀).1
  have hv0 := (hvr μ₀).1
  obtain ⟨-, ζT, hζT, eκT⟩ := hκT t
  obtain ⟨hvt, ζv, hζv, ev⟩ := hvr t
  have hζv0 : ζv ≠ 0 := fun h0 => hvt (by rw [ev, h0, map_zero, zero_mul])
  have hσv : D.what₂.embLL ζv ≠ 0 := (map_ne_zero _).2 hζv0
  refine ⟨fun k => u k t / u k μ₀, fun k => stepRatio_div (hu k t).2 (hu k μ₀).1, ζT * ζv⁻¹,
    hζT.mul (isAwayUnit_inv hζv hζv0), ?_⟩
  rw [Fin.prod_univ_eq_prod_range (fun k => u k t / u k μ₀), prod_div_distrib, prod_div_distrib, prod_div_distrib,
    map_mul, map_inv₀, ec0, ec0]
  have L1 : c / c₀ * ((∏ k ∈ range (qq D j), Lf t ((eTop D i j + k + 1 : ℕ) : ℂ)) /
      ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ)) =
      κT t / κT μ₀ * ((ct t * ∏ k ∈ range (qq D j), Lf t ((eTop D i j + k + 1 : ℕ) : ℂ)) /
        (ct μ₀ * ∏ k ∈ range (qq D j), Lf μ₀ ((eTop D i j + k + 1 : ℕ) : ℂ))) := by
    rw [ec, ec₀]
    have := hct0 μ₀
    field_simp
  rw [L1, hid t, hid μ₀, eκT, ev]
  field_simp
end GlobalTheory.SqTower
end
end

section
open GlobalTheory.SqTop
theorem _root_.GlobalTheory.T.tower_of_theta_matching_lNe : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  first | exact @_root_.GlobalTheory.SqTower.tower_alt_bis | exact _root_.GlobalTheory.SqTower.tower_alt_bis | (intros; apply _root_.GlobalTheory.SqTower.tower_alt_bis <;> assumption)
end
