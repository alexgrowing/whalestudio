import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
import Formalism.SharpRestriction.LevelLetterCocycles.LevLetEMul
import Formalism.SharpRestriction.LevelLetterCocycles.StageStep

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def dvL (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) :
    (Fin d → LL) →ₗ[LL] T.V ⊗[Qp] B where
  toFun c := dv W T e b c
  map_add' c c' := by simp [dv, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [dv, smul_smul, Finset.smul_sum]

theorem dvL_apply (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c : Fin d → LL) :
    dvL W T e b c = dv W T e b c := rfl

theorem crystalline_filtration_antitone (T : LocLat G Qp LL O) (a : ZMod n) : Antitone fun u => FilS W T a 0 u :=
  fun _ _ hab => Submodule.map_mono (inf_le_inf_right _
    (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti (PD := PD) (ρ := T.ρ) hab))

theorem exists_lpow (hvl : v (PD.p : LL) = 1) (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (x : LL) :
    ∃ κ : ℕ, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ κ * x := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  have hne : v x ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨⌈-q⌉₊, hO2 _ ?_⟩
  rw [AddValuation.map_mul, AddValuation.map_pow, hvl, ← hq]
  have h1 : ((⌈-q⌉₊ : ℕ) • (1 : WithTop ℚ)) = (((⌈-q⌉₊ : ℕ) : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
  rw [h1, ← WithTop.coe_add, WithTop.coe_nonneg]
  have := Nat.le_ceil (-q)
  linarith

theorem exists_lpow_fin (hvl : v (PD.p : LL) = 1) (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) {ι : Type}
    [Fintype ι] (x : ι → LL) : ∃ κ : ℕ, ∀ i, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ κ * x i := by
  choose κ o ho using fun i => exists_lpow hvl hO2 (x i)
  refine ⟨∑ i, κ i, fun i => ⟨((PD.p : ℕ) : O) ^ (∑ j, κ j - κ i) * o i, ?_⟩⟩
  have hle : κ i ≤ ∑ j, κ j := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ i)
  rw [map_mul, ho, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem lamUp_eq (A : ArcP n) (c' : ZMod n) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e = ∏ s ∈ Finset.range e,
      ps W (s + 1) ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) (s + 1) := by
  unfold Formalism.MainNotions.UnusedSlot80.LevC.LamUp abelian₂
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, ← Formalism.MainNotions.UnusedSlot80.LevC.ps_succ, Formalism.MainNotions.UnusedSlot80.LevC.hs_succ]
  congr 2
  push_cast; ring

variable [IsDomain O]

theorem cc_lev_piLamUp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    constantCoeff (W.lev a ζ (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e)) ≠ 0 := by
  obtain ⟨S, -, hS⟩ := Formalism.MainNotions.UnusedSlot80.DivLevR.lev_qP_X (W := W) hR a ζ hζ
  have hq0 : constantCoeff (W.lev a ζ (Formalism.MainNotions.WachCoordinates.qP W)) = 0 := by
    rw [hS, map_mul, constantCoeff_X, zero_mul]
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have hπ : constantCoeff (W.lev a ζ W.π₀) = -(PD.p : LL) := by
    have e1 : W.π₀ = Formalism.MainNotions.WachCoordinates.qP W - ((PD.p : ℕ) : LetA O n) := by
      unfold Formalism.MainNotions.WachCoordinates.qP; ring
    rw [e1, map_sub, map_sub, hq0, map_natCast, map_natCast]; ring
  have hps : ∀ s : ℕ, constantCoeff (W.lev a ζ (ps W (s + 1))) = (PD.p : LL) := by
    intro s
    obtain ⟨x, hx⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP (W := W) hR (s + 1) (by omega)
    have e1 : ps W (s + 1) = ((PD.p : ℕ) : LetA O n) + Formalism.MainNotions.WachCoordinates.qP W * x := by
      have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) (s + 1)
      rw [hx] at this
      have e2 : ps W (s + 1) = Formalism.MainNotions.WachCoordinates.pS W (s + 1) := rfl
      rw [e2, ← this]; ring
    rw [e1, map_add, map_mul, map_add, map_mul, hq0, zero_mul, add_zero, map_natCast, map_natCast]
  rw [lamUp_eq, map_mul, map_prod, map_mul, map_prod, hπ]
  refine mul_ne_zero (neg_ne_zero.mpr hp) (Finset.prod_ne_zero_iff.mpr fun s _ => ?_)
  rw [map_pow, map_pow, hps]
  exact pow_ne_zero _ hp

theorem X_pow_dvd_of_unit {U F : PowerSeries LL} (hU : constantCoeff U ≠ 0) {k : ℕ}
    (h : ∀ j < k, coeff j (U * F) = 0) : ∀ j < k, coeff j F = 0 := by
  have h1 : (X : PowerSeries LL) ^ k ∣ U * F := X_pow_dvd_iff.mpr h
  have h2 : (X : PowerSeries LL) ^ k ∣ F := by
    obtain ⟨g, hg⟩ := h1
    refine ⟨U⁻¹ * g, ?_⟩
    calc F = U⁻¹ * (U * F) := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hU, one_mul]
      _ = X ^ k * (U⁻¹ * g) := by rw [hg]; ring
  exact X_pow_dvd_iff.mp h2

end Formalism.MainNotions.UnusedSlot80.CrD
