import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.BdRTied

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tu : P.R.BdRˣ := Units.map (P.ιB : P.R.B →* P.R.BdR) (isUnit_tB P).unit

theorem tu_val : (tu P : P.R.BdR) = P.ιB P.tB := by
  simp [tu]

theorem tz_eq (a : ℤ) : tz P a = ((tu P ^ a : P.R.BdRˣ) : P.R.BdR) := by
  rw [tz, tu, ← map_zpow]
  rfl

theorem fil_anti_le {a b : ℤ} (h : a ≤ b) (x : P.R.BdR) (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  induction b, h using Int.le_induction with
  | base => exact hx
  | succ b _ ih => exact ih ((P.PD (botExt l)).Fil_anti b hx)

theorem ι_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)

theorem fil_mul (a b : ℤ) (x y : P.R.BdR) (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_act (a : ℤ) (g : GQ l) (x : P.R.BdR) (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have h := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at h

theorem actQ_tpow (g : GQ l) (a : ℤ) : P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    apply Units.ext
    simpa [Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  have hι : ∀ b : P.R.B, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun b => by
    have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
    exact h.symm
  rw [tz, hι, actQ_tpow, map_mul, AlgHom.commutes]

variable {AI : LocAinf l P}

theorem fil_step (T : LocTied l P AI) (a : ℤ) (x : P.R.BdR) : x ∈ Fil P a ↔ P.ιB P.tB * x ∈ Fil P (a + 1) := by
  have h := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) a (P.ιB P.tB * x))
  change x ∈ (P.PD (botExt l)).Fil a ↔ P.ιB P.tB * x ∈ (P.PD (botExt l)).Fil (a + 1)
  rw [h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    have hu : IsUnit (P.ιB P.tB) := tu_val P ▸ (tu P).isUnit
    rwa [hu.mul_left_cancel e]

theorem fil_tz (T : LocTied l P AI) (b : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b) := by
  induction b using Int.induction_on with
  | zero => intro a x; simp [tz_eq]
  | succ b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + b), tz_eq, tz_eq, zpow_add_one, Units.val_mul, tu_val, ← add_assoc]
    ring_nf
  | pred b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + (-(b : ℤ) - 1)), tz_eq, tz_eq, ← tu_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_one_add]
    ring_nf

theorem isField (T : LocTied l P AI) : IsField P.R.BdR := by
  obtain ⟨-, -, hF, -⟩ := GlobalTheory.MemLoc.BdRField.bdR_isField l
  exact MulEquiv.isField hF T.eD.toMulEquiv

theorem unit_of_fil (T : LocTied l P AI) (x : P.R.BdR) (h0 : x ∈ Fil P 0) (h1 : x ∉ Fil P 1) :
    ∃ y ∈ Fil P 0, x * y = 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have he : GlobalTheory.MemLoc.IsEps AI.ε := hC.ε ▸ GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have h0' : T.eD x ∈ Formalism.Per.FilD l 0 := (T.fil (botExt l) 0 x).1 h0
  obtain ⟨w, hw⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he 0 (T.eD x)).1 h0'
  rw [zpow_zero, Units.val_one, one_mul] at hw
  have hθ : Formalism.Per.θD l w ≠ 0 := by
    intro hz
    apply h1
    change x ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hw]
    have := GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 ((hker w).1 hz)
    simpa using this
  obtain ⟨w', hw'⟩ := (hunit w hθ).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) w'), ?_, T.eD.injective ?_⟩
  · change _ ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero w'
  · rw [map_mul, RingEquiv.apply_symm_apply, hw, ← map_mul, hw', map_one, map_one]

theorem exact_deg (x : P.R.BdR) (hx : x ≠ 0) : ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (P.PD (botExt l)).Fil_exh x
  have hc : ∃ c, x ∉ Fil P c := by
    by_contra h
    push_neg at h
    exact hx ((P.PD (botExt l)).Fil_sep x h)
  obtain ⟨c, hc⟩ := hc
  have hbd : ∀ z : ℤ, x ∈ Fil P z → z ≤ c := fun z hz => by
    by_contra hlt
    exact hc (fil_anti_le P (le_of_lt (not_le.1 hlt)) x hz)
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c, hbd⟩ ⟨a₀, ha₀⟩
  exact ⟨a, ha, fun h => by have := hmax _ h; omega⟩

end GlobalTheory.PMon.BdRTied

namespace GlobalTheory.PMon

theorem bdR_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    IsField P.R.BdR ∧ Function.Injective P.ιB ∧
    (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧
    (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧
    (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧
    (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧
    (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  intro l _ P AI T
  refine ⟨BdRTied.isField P T, BdRTied.ι_injective P, fun a b x => BdRTied.fil_tz P T b a x,
    fun x h0 h1 => BdRTied.unit_of_fil P T x h0 h1, BdRTied.exact_deg P, BdRTied.fil_mul P,
    BdRTied.fil_act P, fun a g => BdRTied.act_tz P g a, fun a b => ?_, ?_, ?_⟩
  · rw [BdRTied.tz_eq, BdRTied.tz_eq, BdRTied.tz_eq, zpow_add, Units.val_mul]
  · rw [BdRTied.tz_eq, zpow_zero, Units.val_one]
  · rw [BdRTied.tz_eq, zpow_one, BdRTied.tu_val]

end GlobalTheory.PMon
