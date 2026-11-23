import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.AdaptedHodge

variable {l : ℕ} [Fact l.Prime]

theorem xi_unit_fil (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ u : (Per.BdR l)ˣ, (u : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ∧
      ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a →
        ∃ w : Per.BdRp l, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w := by
  have he := core_isEps l C
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have h1 : xi C.ε ∈ Ideal.span {ξ} := by rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
  have h2 : ξ ∈ Ideal.span {xi C.ε} := by rw [← C.ker_theta, ← hξ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨a0, ha0⟩ := Ideal.mem_span_singleton'.1 h1
  obtain ⟨b0, hb0⟩ := Ideal.mem_span_singleton'.1 h2
  have hX := TiedUnif.isUnit_xi he
  have key : aDp l a0 * aDp l b0 * aDp l (xi C.ε) = aDp l (xi C.ε) := by
    rw [← map_mul, ← map_mul, mul_assoc, hb0, ha0]
  have hab : aDp l a0 * aDp l b0 = 1 := by
    apply hinj
    rw [map_one]
    apply hX.mul_right_cancel
    rw [one_mul, ← map_mul, key]
  have hα : IsUnit (aDp l a0) := IsUnit.of_mul_eq_one _ hab
  have hXe : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi C.ε)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a0) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) := by
    rw [← map_mul, ← map_mul, ha0]
  have hu : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ)) :=
    isUnit_of_mul_isUnit_right (hXe ▸ hX)
  refine ⟨hu.unit, hu.unit_spec, fun a x hx => ?_⟩
  obtain ⟨w, rfl⟩ := (TiedUnif.mem_FilD_iff he a x).1 hx
  have hEq : hX.unit = hu.unit * Units.map (algebraMap (Per.BdRp l) (Per.BdR l) : Per.BdRp l →* Per.BdR l) hα.unit :=
    Units.ext (by simp [hXe, mul_comm])
  refine ⟨((hα.unit ^ a : (Per.BdRp l)ˣ) : Per.BdRp l) * w, ?_⟩
  rw [hEq, mul_zpow, ← map_zpow, Units.val_mul, map_mul, mul_assoc]
  rfl

end GlobalTheory.BKLim.AdaptedHodge

namespace GlobalTheory.BKLim

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (x : Fin d → Fin d → P.R.BdR) (h : Fin d → ℤ), (∀ j (g : ↥(GK K)), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (x j i)) = x j) → (∀ j i, x j i ∈ (P.PD K).Fil (h j)) → (∀ y : Fin d → P.R.BdR, (∀ i, y i ∈ (P.PD K).Fil 0) → ∃ c : Fin d → P.R.BdR, (∀ j, c j ∈ (P.PD K).Fil (-h j)) ∧ y = ∑ j, c j • x j) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ i, (H.p i : ℤ) - H.q = h i := by
  intro l _ K P AI T C hfit ξ hξ d ρ x h hinv hfil hspan
  obtain ⟨u, hu, hF⟩ := AdaptedHodge.xi_unit_fil C ξ hξ
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l
  have hV : ∀ j i, ∃ w : Per.BdRp l, T.eD (x j i) = ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w :=
    fun j i => hF _ _ ((T.fil K _ _).1 (hfil j i))
  choose w hw using hV
  have h0 : ∀ i (k : Fin d), (Pi.single i (1 : P.R.BdR) : Fin d → P.R.BdR) k ∈ (P.PD K).Fil 0 := by
    intro i k
    rw [T.fil]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, map_one, ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))]
      exact TiedUnif.alg_mem_FilD_zero 1
    · rw [Pi.single_eq_of_ne hk, map_zero]
      exact zero_mem _
  choose c hc hsum using fun i => hspan (Pi.single i 1) (h0 i)
  have hW : ∀ i j, ∃ w' : Per.BdRp l, T.eD (c i j) = ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w' :=
    fun i j => hF _ _ ((T.fil K _ _).1 (hc i j))
  choose w' hw' using hW
  have hq : ∀ j, 0 ≤ h j + ((∑ j, (h j).natAbs : ℕ) : ℤ) := by
    intro j
    have h1 : (h j).natAbs ≤ ∑ j, (h j).natAbs := Finset.single_le_sum (f := fun j => (h j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcan : ∀ j, ((u ^ (-h j) : (Per.BdR l)ˣ) : Per.BdR l) * ((u ^ h j : (Per.BdR l)ˣ) : Per.BdR l) = 1 := by
    intro j
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  have hVW : (Matrix.of fun i j => w j i) * (Matrix.of fun j i => w' i j) = 1 := by
    ext k i
    apply hinj
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y k)) (hsum i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at e1
    rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul]
    have e2 : ∀ j, T.eD (c i j) * T.eD (x j k) = algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j) := by
      intro j
      rw [hw, hw']
      linear_combination (algebraMap (Per.BdRp l) (Per.BdR l) (w j k) * algebraMap (Per.BdRp l) (Per.BdR l) (w' i j)) * hcan j
    simp only [e2] at e1
    rw [← e1, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  have hz : ∀ z : ℤ_[l], T.eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) =
      ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) (zOm l z) := by
    intro z
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, hfit.o]
    rfl
  refine ⟨{ V := Matrix.of fun i j => w j i
            unit := ⟨⟨_, _, hVW, _root_.mul_eq_one_comm.mp hVW⟩, rfl⟩
            p := fun j => (h j + ((∑ j, (h j).natAbs : ℕ) : ℤ)).toNat
            q := ∑ j, (h j).natAbs
            Q := Matrix.of fun i j => T.eD (x j i)
            Q_eq := ?_
            inv := ?_ }, ?_⟩
  · intro i j
    simp only [Matrix.of_apply]
    rw [hw, map_mul, map_pow, ← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_add, Int.toNat_of_nonneg (hq j), add_comm]
  · intro g _
    ext i j
    have e1 := congrArg (fun y : Fin d → P.R.BdR => T.eD (y i)) (hinv j g)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, T.actD, hz] at e1
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact e1
  · intro i
    simp only
    rw [Int.toNat_of_nonneg (hq i)]
    ring

end GlobalTheory.BKLim
