import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PotentiallySemistableCyclotomicSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisExtra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalGLCommute
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
noncomputable section

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def actM (g : GQ l) : P.R.BdR →* P.R.BdR := (P.actQdR g).toRingEquiv.toRingHom.toMonoidHom

theorem actM_apply (g : GQ l) (b : P.R.BdR) : actM P g b = P.actQdR g b := rfl

variable {P}

theorem unit_zpow_mem {u : P.R.BdRˣ} (h0 : (u : P.R.BdR) ∈ Fil P 0)
    (h1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) (k : ℤ) : ((u ^ k : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one]; exact one_mem_Fil
  | succ k ih => rw [zpow_add_one, Units.val_mul]; exact Fil_mul_left ih h0
  | pred k ih => rw [zpow_sub_one, Units.val_mul]; exact Fil_mul_left ih h1

theorem unitM_scal {n : Type} [Fintype n] [DecidableEq n] {U : GL n P.R.BdR} (hU : UnitM P U) {v : P.R.BdRˣ}
    (h0 : (v : P.R.BdR) ∈ Fil P 0) (h1 : ((v⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) :
    UnitM P (scalGL n v * U) := by
  constructor
  · intro i j
    rw [scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h0 (hU.1 i j)
  · intro i j
    rw [mul_inv_rev, ← map_inv, ← (scalGL_commute n v⁻¹ U⁻¹).eq, scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h1 (hU.2 i j)

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frame_scal {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (m : ℕ) (v : n → ℤ) (d : ℤ)
    (U : GL n P.R.BdR) (hU : ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]))
    (u : P.R.BdRˣ) (hu : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (u : P.R.BdR) =
      kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-d) : ℚ_[l]ˣ) : ℚ_[l]) * u)
    (g : ↥(GK K')) :
    matD P (twist hK ρ χ a) m g *
        ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set F : P.R.BdRˣ := Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g)) with hFdef
  set Q : P.R.BdRˣ := Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l)) with hQdef
  have hF : ∀ k : ℤ, ((F ^ k : P.R.BdRˣ) : P.R.BdR) = kd P (fr l m ((χ g ^ k : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l))) := by
    intro k
    have : F ^ k = Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g ^ k)) := by
      simp only [hFdef, map_zpow]
    rw [this]; rfl
  have hQ : ∀ k : ℤ, ((Q ^ k : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro k
    have : Q ^ k = Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l) ^ k) := by
      simp only [hQdef, map_zpow]
    rw [this]; rfl
  have hu' : Units.map (actM P (g : GQ l)) u = F * Q ^ (-d) * u := by
    apply Units.ext
    rw [Units.coe_map, actM_apply, hu g, Units.val_mul, Units.val_mul, hQ]
    have := hF 1
    rw [zpow_one, zpow_one] at this
    rw [this]
  have hs : P.actQdR (g : GQ l) ((u ^ (-a) : P.R.BdRˣ) : P.R.BdR) = (((F * Q ^ (-d) * u) ^ (-a) : P.R.BdRˣ) : P.R.BdR) := by
    rw [← hu', ← map_zpow, Units.coe_map, actM_apply]
  have hmat : matD P (twist hK ρ χ a) m g =
      ((F ^ a : P.R.BdRˣ) : P.R.BdR) • matD P ρ m ⟨g, GK_le hK g.2⟩ := by
    ext i j
    simp only [matD, twist_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hF]
  have hmap : ∀ (s : P.R.BdR) (M : Matrix n n P.R.BdR),
      (s • M).map (P.actQdR (g : GQ l)) = P.actQdR (g : GQ l) s • M.map (P.actQdR (g : GQ l)) := by
    intro s M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hdiag : (Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l])) =
      ((Q ^ (d * a) : P.R.BdRˣ) : P.R.BdR) • Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [hQ, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, zpow_add, Units.val_mul, map_mul, mul_comm]
  rw [hmat, scalGL_mul_val, hmap, hs, hdiag, smul_mul_smul_comm, smul_mul_smul_comm]
  have hUg := hU ⟨g, GK_le hK g.2⟩
  rw [hUg, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_zpow, mul_zpow, ← zpow_mul, neg_mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul, mul_comm]

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

set_option maxHeartbeats 1000000 in

theorem framed_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type)
    [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ),
    IsRat r ρ → Framed P ρ w →
    (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) →
    P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) →
    Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a)
      (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  intro l _ P AI T n _ _ K K' hK r N hr ρ w χ x a hρ hf hx hx1 hx2 hev m
  obtain ⟨-, -, hshift, hunit, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hgal : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (ev P m x) = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * ev P m x := by
    intro g
    rw [← ev_act, hx g, ← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  obtain ⟨e, he0, he1, hegal⟩ : ∃ e : P.R.BdR, e ∈ Fil P 0 ∧ e ∉ Fil P 1 ∧ ∀ g : ↥(GK K'),
      P.actQdR (g : GQ l) e = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) *
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(if (m : ℕ) = 0 then 1 else 0 : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * e := by
    by_cases hm : (m : ℕ) = 0
    · have e0 : ev P (m : ℕ) x = P.ιB x := by rw [hm]; rfl
      refine ⟨tz P (-1) * ev P m x, ?_, ?_, fun g => ?_⟩
      · have h := (hshift 1 (-1) (P.ιB x)).1 hx1
        rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
        rwa [e0]
      · intro h
        rw [e0] at h
        apply hx2
        refine (hshift 2 (-1) (P.ιB x)).2 ?_
        rwa [show (2 : ℤ) + -1 = 1 by norm_num]
      · rw [if_pos hm, map_mul, GlobalTheory.PMon.Model.act_tz, hgal g]
        ring
    · have hj := hev m (Nat.pos_of_ne_zero hm) m.2
      refine ⟨ev P m x, hj.1, hj.2, fun g => ?_⟩
      rw [if_neg hm, hgal g, neg_zero, zpow_zero, Units.val_one, map_one, mul_one]
  obtain ⟨y, hy0, hey⟩ := hunit e he0 he1
  let u : P.R.BdRˣ := ⟨e, y, hey, by rw [mul_comm]; exact hey⟩
  have hu0 : (u : P.R.BdR) ∈ Fil P 0 := he0
  have hu1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := hy0
  obtain ⟨U, hUm, hU⟩ := hf ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ ((m : ℕ) % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    rw [fr_mod (hρ.rat g i j)]
  refine ⟨scalGL n (u ^ (-a)) * U, unitM_scal hUm (unit_zpow_mem hu0 hu1 _)
    (by rw [← zpow_neg]; exact unit_zpow_mem hu0 hu1 _), fun g => ?_⟩
  have key := frame_scal hK ρ χ a m (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩) (if (m : ℕ) = 0 then 1 else 0) U
    (fun g' => by rw [hper]; exact hU g') u hegal g
  have hda : (if (m : ℕ) = 0 then (1 : ℤ) else 0) * a = if (m : ℕ) = 0 then a else 0 := by
    split_ifs <;> simp
  simp only [hda] at key
  exact key

end GlobalTheory.PMon.Twist
