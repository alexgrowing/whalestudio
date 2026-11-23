import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem mem_iff (K : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD (botExt l)).Fil a := by
  have h := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, h, SetLike.mem_coe]

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact (mem_iff K 0 _).1 h

theorem t_isUnit (P : LocPrime l) : IsUnit (P.ιB P.tB) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

def tU (P : LocPrime l) : P.R.BdRˣ := (t_isUnit P).unit

theorem tU_val : ((tU P : P.R.BdRˣ) : P.R.BdR) = P.ιB P.tB := rfl

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR g x ∈ (P.PD (botExt l)).Fil a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) :
    P.actQdR g (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ g) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ P.tB
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [← h3, h, map_smul, Algebra.smul_def]

theorem act_zpow (g : GQ l) (n : ℤ) :
    P.actQdR g ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ n : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) := by
  have h : Units.map ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →* P.R.BdR) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) (P.χQ g) * tU P :=
    Units.ext (actQdR_periodT_eq_cyclotomic_bottom g)
  have h2 := congrArg (fun u : P.R.BdRˣ => ((u ^ n : P.R.BdRˣ) : P.R.BdR)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at h2
  rw [map_zpow P.χQ] at h2
  exact h2

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem zpow_mem (n : ℤ) : ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil n := by
  have h1 : ((tU P : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have h2 : (((tU P)⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil (-1) := by
    obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t (-1) 1).1 (by simpa using (P.PD (botExt l)).one_mem)
    rw [← tU_val] at e
    rwa [Units.inv_eq_of_mul_eq_one_right e.symm]
  induction n using Int.induction_on with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, sub_eq_add_neg]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h2

theorem shift_iff (a b : ℤ) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil b ↔
      x ∈ (P.PD (botExt l)).Fil (a + b) := by
  constructor
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J a) h
    rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at this
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J (-a)) h
    rwa [neg_add_cancel_left] at this

omit J in

theorem exists_symbol : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI →
    ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ,
      (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧
      (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a,
        sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧
      (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧
      ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a,
        sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI J K
  refine ⟨fun a x => J.θ (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x), fun a => ?_⟩
  have key : ∀ x ∈ (P.PD K).Fil a,
      ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := fun x hx =>
    (shift_iff J a 0 x).2 (by rw [add_zero]; exact (mem_iff K a x).1 hx)
  refine ⟨fun x hx y hy => ?_, fun c x hx => ?_, fun x hx => ?_, fun g x hx => ?_⟩
  · beta_reduce
    rw [mul_add, J.θ_add _ (key x hx) _ (key y hy)]
  · beta_reduce
    rw [mul_left_comm, J.θ_mul _ (om_mem c) _ (key x hx), J.θ_Om]
  · beta_reduce
    rw [J.θ_ker _ (key x hx), shift_iff J, mem_iff K]
  · beta_reduce
    have e : ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l])) *
          P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
      rw [← IsScalarTower.algebraMap_apply, map_mul, act_zpow, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one, one_mul]
    rw [e, J.θ_mul _ (om_mem _) _ (act_mem g (key x hx)), J.θ_Om, J.θ_act g _ (key x hx)]
    rfl

end GlobalTheory.DeRhamSymbol
