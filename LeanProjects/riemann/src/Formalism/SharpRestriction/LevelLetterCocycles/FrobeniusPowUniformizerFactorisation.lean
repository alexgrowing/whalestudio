import Mathlib
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.WachModuleLifts.WachModuleProofs.LemmaCLower
import Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharp
import Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharpOddUnitInvHolds
import Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharpG
import Formalism.WachModuleLifts.WachModuleProofs.LemmaCSharpOddG
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
import Formalism.GaussValuationBounds.NokLemmaCVal
import Formalism.GaussValuationBounds.GaussValueContraction.ScaledPowMemSpanCeil
import Formalism.WeaklyAdmissibleFiltrations.PhtGalois
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds

noncomputable section

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Zl

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {H : LocHW l P}

theorem zl_cancel (a : WithTop ℚ) (k : ℕ) (h : a + ((k : ℕ) : WithTop ℚ) = ((k : ℕ) : WithTop ℚ)) :
    a = 0 := by
  induction a with
  | top => simp at h
  | coe q =>
    have h' : ((q + (k : ℚ) : ℚ) : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by exact_mod_cast h
    have h'' := WithTop.coe_injective h'
    have : q = 0 := by linarith
    rw [this]; rfl

theorem zl_map_eq (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ℤ_[l] ↥LL.1 z = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) :=
  IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 z

theorem zl_inj_LL (LL : FinExt l) : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  intro a b hab
  rw [zl_map_eq, zl_map_eq] at hab
  exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective hab)

theorem zl_map_O (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℤ_[l] ↥LL.1 z := rfl

theorem zl_inj_O (LL : FinExt l) : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b hab
  apply zl_inj_LL LL
  rw [← zl_map_O, ← zl_map_O, hab]

theorem zl_O_inj (LL : FinExt l) : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) :=
  Subtype.val_injective

theorem zl_v_unit (LL : FinExt l) (w : (↥(OL LL))ˣ) :
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 := by
  have h1 : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) :=
    (P.v_O LL _).2 (w : ↥(OL LL)).2
  have h2 : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) :=
    (P.v_O LL _).2 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have h3 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
      P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
  refine le_antisymm ?_ h1
  calc P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))
      ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
        P.v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) :=
        le_add_of_nonneg_right h2
    _ = 0 := h3

theorem zl_v_pow (LL : FinExt l) (k : ℕ) :
    P.v LL (((l : ℕ) : ↥LL.1) ^ k) = ((k : ℕ) : WithTop ℚ) := by
  rw [AddValuation.map_pow, P.v_l LL]
  simp

theorem v_zl (LL : FinExt l) (z : ℤ_[l]) (hz : z ≠ 0) :
    P.v LL (algebraMap ℤ_[l] ↥LL.1 z) = ((z.valuation : ℕ) : WithTop ℚ) := by
  have hs := PadicInt.unitCoeff_spec hz
  have h1 : algebraMap ℤ_[l] ↥LL.1 z =
      algebraMap ↥(OL LL) ↥LL.1
        ((Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom (PadicInt.unitCoeff hz) : (↥(OL LL))ˣ) :
          ↥(OL LL)) * ((l : ℕ) : ↥LL.1) ^ z.valuation := by
    conv_lhs => rw [hs]
    rw [map_mul, map_pow, map_natCast]
    rfl
  rw [h1, AddValuation.map_mul, zl_v_unit, zl_v_pow, zero_add]

theorem assoc_of_v (LL : FinExt l) (x : ↥(OL LL)) (k : ℕ)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) = ((k : ℕ) : WithTop ℚ)) :
    Associated x (((l : ℕ) : ↥(OL LL)) ^ k) := by
  have hl : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h0
    have := P.v_l LL
    rw [h0, AddValuation.map_zero] at this
    exact absurd this (by simp)
  have hlk : ((l : ℕ) : ↥LL.1) ^ k ≠ 0 := pow_ne_zero _ hl
  have hx : (algebraMap ↥(OL LL) ↥LL.1 x) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at h
    exact absurd h (by simp)
  set X : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 x with hX
  have hy : P.v LL (X / ((l : ℕ) : ↥LL.1) ^ k) = 0 := by
    apply zl_cancel _ k
    rw [← zl_v_pow P LL k, ← AddValuation.map_mul, div_mul_cancel₀ _ hlk, zl_v_pow, h]
  have hy' : P.v LL (((l : ℕ) : ↥LL.1) ^ k / X) = 0 := by
    apply zl_cancel _ k
    rw [← h, ← AddValuation.map_mul, div_mul_cancel₀ _ hx, zl_v_pow, h]
  have m1 : X / ((l : ℕ) : ↥LL.1) ^ k ∈ OL LL := (P.v_O LL _).1 hy.ge
  have m2 : ((l : ℕ) : ↥LL.1) ^ k / X ∈ OL LL := (P.v_O LL _).1 hy'.ge
  refine ⟨⟨⟨_, m2⟩, ⟨_, m1⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change ((l : ℕ) : ↥LL.1) ^ k / X * (X / ((l : ℕ) : ↥LL.1) ^ k) = 1
    field_simp
  · apply Subtype.ext
    change X / ((l : ℕ) : ↥LL.1) ^ k * (((l : ℕ) : ↥LL.1) ^ k / X) = 1
    field_simp
  · apply Subtype.ext
    change X * (((l : ℕ) : ↥LL.1) ^ k / X) = _
    rw [mul_div_cancel₀ _ hx]
    simp

variable {P}

theorem zl_chi_int {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (g : (H.W K s LL h).Gam) :
    ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (((H.W K s LL h).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) := by
  obtain ⟨g', rfl⟩ := (H.W K s LL h).resΓ_onto g
  have h1 := (H.W K s LL h).χΓ_res g'
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g' : ℚ_[l]ˣ) : ℚ_[l])) := by
    rw [← h1]
    exact (((H.W K s LL h).χΓ ((H.W K s LL h).resΓ g') : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have hint' : IsIntegral ℤ_[l] (((P.PD K).χ g' : ℚ_[l]ˣ) : ℚ_[l]) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective).1 hint
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[l]) (K := ℚ_[l])).1 hint'
  refine ⟨y, ?_⟩
  apply zl_O_inj LL
  rw [h1, zl_map_O, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy]

theorem chi_zl {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (g : (H.W K s LL h).Gam) :
    ∃ z : ℤ_[l]ˣ, algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) =
      (((H.W K s LL h).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) := by
  obtain ⟨y, hy⟩ := zl_chi_int h g
  obtain ⟨y', hy'⟩ := zl_chi_int h g⁻¹
  have h1 : y * y' = 1 := by
    apply zl_inj_O LL
    rw [map_mul, hy, hy', map_inv, Units.mul_inv, map_one]
  exact ⟨⟨y, y', h1, by rw [mul_comm]; exact h1⟩, hy⟩

theorem gam_zl {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    ∃ z : ℤ_[l]ˣ, algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) =
      (((H.W K s LL h).χΓ (H.W K s LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL)) ∧
      PadicInt.valuation ((z : ℤ_[l]) - 1) = s := by
  obtain ⟨z, hz⟩ := chi_zl h (H.W K s LL h).gam
  refine ⟨z, hz, ?_⟩
  have hg := (H.W K s LL h).gam_gen
  rw [H.W_s, ← hz, zl_map_O, ← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub] at hg
  have hne : (z : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    rw [h0, map_zero, AddValuation.map_zero] at hg
    exact absurd hg (by simp)
  rw [v_zl P LL _ hne] at hg
  exact_mod_cast hg

end Zl

example {l : ℕ} [Fact l.Prime] (LL : FinExt l) : IsDomain ↥(OL LL) := inferInstance

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PartR

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P}

theorem partR_zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

theorem partR_zpow {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (z : ℤ_[l]ˣ)
    (hz : algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) =
      (((H.W K s LL h).χΓ (H.W K s LL h).gam : (↥(OL LL))ˣ) : ↥(OL LL))) (j : ℤ) :
    algebraMap ℤ_[l] ↥(OL LL) ((z ^ j : ℤ_[l]ˣ) : ℤ_[l]) =
      (((uγ (H.W K s LL h)) ^ j : (↥(OL LL))ˣ) : ↥(OL LL)) := by
  have hU : Units.map (algebraMap ℤ_[l] ↥(OL LL)).toMonoidHom z = uγ (H.W K s LL h) :=
    Units.ext hz
  rw [← hU, ← map_zpow]
  rfl

theorem lifting_product_associated {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (J : Finset ℤ)
    (hJ : (0 : ℤ) ∉ J) :
    Associated (∏ j ∈ J, (1 - (((uγ (H.W K s LL h)) ^ (-j) : (↥(OL LL))ˣ) : ↥(OL LL))))
      (((l : ℕ) : ↥(OL LL)) ^ (J.card * s + ∑ j ∈ J, padicValInt l j)) := by
  obtain ⟨z, hz, hv⟩ := gam_zl (P := P) (H := H) h
  obtain ⟨hne, hval⟩ := (Formalism.WindowSums.arc_ValProd l z s h.1 h.2.1 hv).2 J hJ
  have hprod : (∏ j ∈ J, (1 - (((uγ (H.W K s LL h)) ^ (-j) : (↥(OL LL))ˣ) : ↥(OL LL)))) =
      algebraMap ℤ_[l] ↥(OL LL) (∏ j ∈ J, (1 - ((z ^ (-j) : ℤ_[l]ˣ) : ℤ_[l]))) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_one, partR_zpow h z hz]
  rw [hprod]
  apply assoc_of_v P LL
  rw [zl_map_O, v_zl P LL _ hne, hval]

theorem product_unit_times_power_general {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (p : ℕ)
    (hp : ((p : ℕ) : LL) ≠ 0) (J : Finset ℤ) (a : ℤ → O) (k : ℕ) (c : Oˣ)
    (hc : (∏ j ∈ J, a j) * (c : O) = ((p : ℕ) : O) ^ k) :
    ∃ w : Oˣ, (∏ j ∈ J, (-(algebraMap O LL (a j) / ((p : ℕ) : LL)))) =
      algebraMap O LL (w : O) * ((p : ℕ) : LL) ^ ((k : ℤ) - (J.card : ℤ)) := by
  have hx : (∏ j ∈ J, a j) = ((p : ℕ) : O) ^ k * ((c⁻¹ : Oˣ) : O) :=
    (Units.eq_mul_inv_iff_mul_eq c).2 hc
  refine ⟨(-1) ^ J.card * c⁻¹, ?_⟩
  rw [Finset.prod_neg, Finset.prod_div_distrib, Finset.prod_const, ← map_prod, hx,
    zpow_sub₀ hp, zpow_natCast, zpow_natCast]
  simp only [map_mul, map_pow, map_natCast, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, map_neg, map_one]
  ring

theorem partR_coreLiftR {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    coreLiftR (H.W K s LL h) := by
  intro T₁ Mi hi _ _
  have hJ := partR_zero_notMem_JSet
    (jumpSet (H.W K s LL h) T₁ (Mmax _ Mi) (Mmax _ hi)) (Mmax _ Mi)
  have hA := lifting_product_associated (P := P) (H := H) h _ hJ
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [P.PD_p K]
    exact ⟨_, hA⟩
  · obtain ⟨c, hc⟩ := hA
    have hl : ((l : ℕ) : ↥LL.1) ≠ 0 := by
      intro h0
      have := P.v_l LL
      rw [h0, AddValuation.map_zero] at this
      exact absurd this (by simp)
    rw [P.PD_p K]
    obtain ⟨w, hw⟩ := product_unit_times_power_general l hl _ _ _ c hc
    exact ⟨w, _, hw⟩

def coreHval {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) : Prop :=
  ∀ r : ℕ, 1 ≤ r →
    v (algebraMap O LL (u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ)

def coreHleg (p : ℕ) : Prop :=
  ∀ r : ℕ, ((r + padicValNat p r.factorial : ℕ) : ℚ) ≤ r * p / ((p : ℚ) - 1)

theorem partR_coreHval {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (hA : CaseA (H.W K s LL h)) : coreHval (H.W K s LL h) := by
  intro r hr
  obtain ⟨_, hs1, hl2⟩ := hA
  rw [H.W_s] at hs1
  rw [P.PD_p K] at hl2 ⊢
  obtain ⟨z, hz, hv⟩ := gam_zl (P := P) (H := H) h
  have hl3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hj : (((l - 1) * r : ℕ) : ℤ) ≠ 0 := by
    have : 0 < (l - 1) * r := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this.ne'
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_ZpowVal l z s h.1 h.2.1 hv _ hj
  have hu : u₁ (H.W K s LL h) ^ r - 1 =
      algebraMap ℤ_[l] ↥(OL LL) (((z ^ (((l - 1) * r : ℕ) : ℤ) : ℤ_[l]ˣ) : ℤ_[l]) - 1) := by
    rw [map_sub, map_one, partR_zpow h z hz, zpow_natCast, Units.val_pow_eq_pow_val, pow_mul]
    unfold u₁
    rw [P.PD_p K]
  rw [hu, zl_map_O, v_zl P LL _ hne, hval, hs1, padicValInt.of_nat,
    padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega), zero_add]

theorem partR_coreHleg (p : ℕ) (hp : p.Prime) : coreHleg p := by
  haveI := Fact.mk hp
  intro r
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have key : (p - 1) * padicValNat p r.factorial ≤ r := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have key' : ((p : ℚ) - 1) * (padicValNat p r.factorial : ℚ) ≤ r := by
    have h := (Nat.cast_le (α := ℚ)).2 key
    push_cast [Nat.cast_sub hp.one_le] at h
    exact h
  rw [le_div_iff₀ (by linarith)]
  push_cast
  nlinarith

end PartR

theorem lifting_bracket_units_times_powers (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : LiftBracketR D HW F := fun l _ _ _ _ h => partR_coreLiftR (P := D.loc l) (H := HW l) h

theorem coreH_val_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (hA : CaseA ((HW l).W K s LL h)) : coreHval ((HW l).W K s LL h) :=
  partR_coreHval h hA

theorem coreH_leg_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    coreHleg ((D.loc l).PD K).p :=
  partR_coreHleg _ ((D.loc l).PD K).hp

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PartH1

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem constantCoeff_gamma (W : LocWach PD LL O v n) (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  have hC : ∀ c : O, W.γ₀ g (PowerSeries.C c) = PowerSeries.C c := by
    intro c
    have : PowerSeries.C c = algebraMap O (PowerSeries O) c := by
      simp
    rw [this, AlgHom.commutes]
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  rw [map_add, map_mul, hC, map_add, map_mul, (W.γ₀_X g).1, zero_mul, zero_add,
    PowerSeries.constantCoeff_C]

theorem gamma_X_eq (W : LocWach PD LL O v n) (g : W.Gam) :
    ∃ t : PowerSeries O, W.γ₀ g PowerSeries.X =
      PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t) := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  set f := W.γ₀ g PowerSeries.X with hf
  set f1 : PowerSeries O := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f with hf1
  have e1 : f = PowerSeries.X * f1 := by
    have := PowerSeries.eq_X_mul_shift_add_const f
    rw [h0, map_zero, add_zero] at this
    exact this
  have e2 := PowerSeries.eq_X_mul_shift_add_const f1
  have e3 : PowerSeries.constantCoeff f1 = ((W.χΓ g : Oˣ) : O) := by
    rw [← h1, hf1, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  rw [e3] at e2
  refine ⟨PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f1, ?_⟩
  rw [e1]
  conv_lhs => rw [e2]
  ring

theorem gammaA_comm (W : LocWach PD LL O v n) (g g' : W.Gam) (a : LetA O n) :
    W.γA g (W.γA g' a) = W.γA g' (W.γA g a) := by
  funext i
  have h1 : W.γ₀ g (W.γ₀ g' (a i)) = (W.γ₀ (g * g')) (a i) := by rw [map_mul]; rfl
  have h2 : W.γ₀ g' (W.γ₀ g (a i)) = (W.γ₀ (g' * g)) (a i) := by rw [map_mul]; rfl
  change W.γ₀ g (W.γ₀ g' (a i)) = W.γ₀ g' (W.γ₀ g (a i))
  rw [h1, h2, mul_comm]

theorem gammaA_letter_idempotent (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    W.γA g (letE i) = letE i := by
  funext j
  change W.γ₀ g ((letE i : LetA O n) j) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · simp [letE, hj]

theorem gammaD_semilinear (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n)
    (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem invariant_smul_mem_invariants' (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n) (ha : a ∈ W.AΔ)
    (x : W.DD T) (hx : x ∈ W.NΔ T) : a • x ∈ W.NΔ T :=
  ⟨(W.N T).smul_mem a hx.1, fun δ hδ => by rw [gammaD_semilinear, ha δ hδ, hx.2 δ hδ]⟩

theorem unit_mul_pi_pow_left_cancel (w : (LetA O n)ˣ) (k : ℕ) (a b : LetA O n)
    (h : ((w : LetA O n) * letπ ^ k) * a = ((w : LetA O n) * letπ ^ k) * b) : a = b := by
  have h' : (letπ : LetA O n) ^ k * a = letπ ^ k * b := by
    have := congrArg (fun z => ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * z) h
    simpa [mul_assoc] using this
  funext i
  have hi := congrFun h' i
  exact PowerSeries.X_pow_mul_cancel (k := k) hi

abbrev P9π₀ (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
    (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

theorem eisenstein_at_uniformizer (W : LocWach PD LL O v n) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qp]

theorem pullback_projection_frobenius (W : LocWach PD LL O v n) (h9 : P9π₀ W) :
    ∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * qp W ^ (PD.p - 1) := by
  obtain ⟨w, hw⟩ := h9.2.2.2.2.2.1
  rw [eisenstein_at_uniformizer] at hw
  exact ⟨w, hw⟩

theorem gamma_uniformizer_eq_mul_unit' (W : LocWach PD LL O v n) (h9 : P9π₀ W) :
    ∃ t ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * (algebraMap O (LetA O n) (u₁ W) + W.π₀ * t) := by
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, -, -, ⟨w', hw'⟩, -⟩ := h9
  rw [eisenstein_at_uniformizer] at hw'
  have hk : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have hreg : ∀ a b : LetA O n, W.π₀ * a = W.π₀ * b → a = b := fun a b hab => by
    rw [hw] at hab
    exact unit_mul_pi_pow_left_cancel w _ a b hab
  set c : LetA O n := 1 + (w' : LetA O n) * qp W with hc
  have hγ : W.γA W.gam W.π₀ = W.π₀ * c := by
    have : W.γA W.gam W.π₀ = W.π₀ + (w' : LetA O n) * W.π₀ * qp W := by rw [← hw']; ring
    rw [this, hc]; ring
  have hcΔ : c ∈ W.AΔ := by
    intro δ hδ
    apply hreg
    have h1 : W.γA δ (W.π₀ * c) = W.π₀ * c := by
      rw [← hγ, gammaA_comm, hπΔ δ hδ]
    rw [map_mul, hπΔ δ hδ] at h1
    exact h1
  have hcc : ∀ i, PowerSeries.constantCoeff (c i) = u₁ W := by
    intro i
    obtain ⟨t, ht⟩ := gamma_X_eq W W.gam
    have e1 : (W.γA W.gam W.π₀) i = W.γ₀ W.gam ((w : LetA O n) i) *
        (PowerSeries.X * (PowerSeries.C ((W.χΓ W.gam : Oˣ) : O) + PowerSeries.X * t)) ^ (PD.p - 1) := by
      conv_lhs => rw [hw]
      change W.γ₀ W.gam ((w : LetA O n) i * PowerSeries.X ^ (PD.p - 1)) = _
      rw [map_mul, map_pow, ht]
    have e2 : (W.π₀ * c) i = ((w : LetA O n) i * PowerSeries.X ^ (PD.p - 1)) * c i := by
      conv_lhs => rw [hw]
      rfl
    have e3 : PowerSeries.X ^ (PD.p - 1) * ((w : LetA O n) i * c i) =
        PowerSeries.X ^ (PD.p - 1) * (W.γ₀ W.gam ((w : LetA O n) i) *
          (PowerSeries.C ((W.χΓ W.gam : Oˣ) : O) + PowerSeries.X * t) ^ (PD.p - 1)) := by
      have := congrFun hγ i
      rw [e1, e2] at this
      rw [mul_pow] at this
      linear_combination -this
    have e4 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel e3)
    rw [map_mul, map_mul, constantCoeff_gamma, map_pow, map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul,
      add_zero, PowerSeries.constantCoeff_C] at e4
    have hu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) := by
      have h1 : IsUnit ((w : LetA O n) i) :=
        (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i))
      exact h1.map PowerSeries.constantCoeff
    exact hu.mul_left_cancel e4
  have hπ0 : ∀ i, PowerSeries.constantCoeff (W.π₀ i) = 0 := by
    intro i
    have : W.π₀ i = (w : LetA O n) i * PowerSeries.X ^ (PD.p - 1) := by
      conv_lhs => rw [hw]
      rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]
  set a : LetA O n := c - algebraMap O (LetA O n) (u₁ W) with ha
  have haΔ : a ∈ W.AΔ := W.AΔ.sub_mem hcΔ (W.AΔ.algebraMap_mem _)
  have ha0 : ∀ i, PowerSeries.constantCoeff (a i) = 0 := by
    intro i
    have : a i = c i - PowerSeries.C (u₁ W) := by
      rw [ha]
      simp
    rw [this, map_sub, hcc, PowerSeries.constantCoeff_C, sub_self]
  obtain ⟨f, hf, -⟩ := hsub a haΔ
  set t : LetA O n := fun i =>
    PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) with ht
  have hat : a = W.π₀ * t := by
    funext i
    have hs : PowerSeries.HasSubst (W.π₀ i) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
    have e1 := hf i
    rw [PowerSeries.eq_X_mul_shift_add_const (f i), PowerSeries.subst_add hs, PowerSeries.subst_mul hs,
      PowerSeries.subst_X hs, PowerSeries.subst_C] at e1
    have e2 : a i = W.π₀ i * t i + PowerSeries.C (PowerSeries.constantCoeff (f i)) := e1
    have e3 := congrArg PowerSeries.constantCoeff e2
    rw [ha0, map_add, map_mul, hπ0, zero_mul, zero_add, PowerSeries.constantCoeff_C] at e3
    rw [e2, ← e3, map_zero, add_zero]
    rfl
  have htΔ : t ∈ W.AΔ := by
    intro δ hδ
    apply hreg
    have h1 : W.γA δ (W.π₀ * t) = W.π₀ * t := by rw [← hat]; exact haΔ δ hδ
    rw [map_mul, hπΔ δ hδ] at h1
    exact h1
  refine ⟨t, htΔ, ?_⟩
  rw [hγ, ← hat, ha]
  ring_nf

theorem H_clause_algebra_identity {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (p Ur tr : A) (r : ℕ)
    (x x₂ : D) : (p ^ r * (Ur + p * tr)) • (x + p • x₂) - p ^ r • x =
      (Ur - 1) • (p ^ r • x) + p ^ (r + 1) • (tr • x + (Ur + p * tr) • x₂) := by
  module

def coreHgr (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Prop :=
  ∀ (r : ℕ) (x : W.DD T), InNΔi W T i x → ∃ x', InNΔi W T i x' ∧
    W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x = (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x'

theorem first_H_clause_of_uniformizer (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (h9 : P9π₀ W)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) : coreHgr W T i := by
  intro r x hx
  obtain ⟨t, htΔ, hγ⟩ := gamma_uniformizer_eq_mul_unit' W h9
  have hπΔ : W.π₀ ∈ W.AΔ := h9.1
  set U : LetA O n := algebraMap O (LetA O n) (u₁ W) with hU
  have hd : ∀ r : ℕ, ∃ tr ∈ W.AΔ, (U + W.π₀ * t) ^ r = U ^ r + W.π₀ * tr := by
    intro r
    induction r with
    | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
    | succ r ih =>
      obtain ⟨tr, htr, he⟩ := ih
      refine ⟨U ^ r * t + tr * U + W.π₀ * tr * t, ?_, ?_⟩
      · have hUΔ : U ∈ W.AΔ := W.AΔ.algebraMap_mem _
        exact W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hUΔ r) htΔ)
          (W.AΔ.mul_mem htr hUΔ)) (W.AΔ.mul_mem (W.AΔ.mul_mem hπΔ htr) htΔ)
      · rw [pow_succ, he]; ring
  obtain ⟨tr, htr, hdr⟩ := hd r
  obtain ⟨x₁, hx₁, hx₁e⟩ := hm.2 x hx.1
  obtain ⟨y, hy, hyx⟩ := hx.2
  have hEx : (letE i : LetA O n) • x = x := by
    rw [← hyx]
    change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
    rw [smul_smul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [letE]
    · simp [letE, hj]
  have hEγ : (letE i : LetA O n) • W.γ T x = W.γ T x := by
    conv_rhs => rw [← hEx]
    change _ = W.γD T W.gam _
    rw [gammaD_semilinear, gammaA_letter_idempotent]
    rfl
  set x₂ : W.DD T := (letE i : LetA O n) • x₁ with hx₂
  have hx₂e : W.γ T x = x + W.π₀ • x₂ := by
    have : W.π₀ • x₂ = W.γ T x - x := by
      rw [hx₂, smul_comm, ← hx₁e, smul_sub, hEγ, hEx]
    rw [this]; abel
  have hx₂m : InNΔi W T i x₂ :=
    ⟨⟨(W.N T).smul_mem _ hx₁.1, fun δ hδ => by rw [hx₂, gammaD_semilinear, gammaA_letter_idempotent, hx₁.2 δ hδ]⟩,
      ⟨x₁, hx₁.1, rfl⟩⟩
  have hdΔ : U ^ r + W.π₀ * tr ∈ W.AΔ :=
    W.AΔ.add_mem (W.AΔ.pow_mem (W.AΔ.algebraMap_mem _) r) (W.AΔ.mul_mem hπΔ htr)
  refine ⟨tr • x + (U ^ r + W.π₀ * tr) • x₂, ⟨(W.NΔ T).add_mem (invariant_smul_mem_invariants' W T _ htr _ hx.1)
    (invariant_smul_mem_invariants' W T _ hdΔ _ hx₂m.1), (W.Nl T i).add_mem ((W.Nl T i).smul_mem _ hx.2)
    ((W.Nl T i).smul_mem _ hx₂m.2)⟩, ?_⟩
  have e1 : W.γ T (W.π₀ ^ r • x) = (W.π₀ ^ r * (U ^ r + W.π₀ * tr)) • (x + W.π₀ • x₂) := by
    change W.γD T W.gam _ = _
    rw [gammaD_semilinear, map_pow, hγ, mul_pow, hdr]
    change _ • W.γ T x = _
    rw [hx₂e]
  have e2 : (u₁ W ^ r - 1) • (W.π₀ ^ r • x) = (U ^ r - 1) • (W.π₀ ^ r • x) := by
    rw [hU, ← map_pow, ← map_one (algebraMap O (LetA O n)), ← map_sub, algebraMap_smul]
  rw [e1, e2]
  exact H_clause_algebra_identity W.π₀ (U ^ r) tr r x x₂

theorem finrank_eq_one_case_A (W : LocWach PD LL O v n) (hA : CaseA W) : Module.finrank K₀ K = 1 := by
  have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
  rw [← e.finrank_eq, Module.finrank_self]

theorem uniformizer_ring_and_module_clauses (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : P9π₀ W ∧ Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ :=
  (h9 T hT hA.2.1 hA.2.2).2.2 (finrank_eq_one_case_A W hA)

theorem coreHgr_of (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) : coreHgr W T i :=
  first_H_clause_of_uniformizer W T i (uniformizer_ring_and_module_clauses W h9 hA T hT).1 (uniformizer_ring_and_module_clauses W h9 hA T hT).2

end PartH1

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Finset

theorem exists_nat_add_nonneg (a : WithTop ℚ) : ∃ k : ℕ, ∀ k' ≥ k, 0 ≤ ((k' : ℕ) : WithTop ℚ) + a := by
  induction a with
  | top => exact ⟨0, fun _ _ => by simp⟩
  | coe q =>
    obtain ⟨k, hk⟩ := exists_nat_ge (-q)
    refine ⟨k, fun k' hk' => ?_⟩
    have e : ((k' : ℕ) : WithTop ℚ) + (q : WithTop ℚ) = (((k' : ℚ) + q : ℚ) : WithTop ℚ) := by
      push_cast; rfl
    rw [e, show (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) from rfl, WithTop.coe_le_coe]
    have : (k : ℚ) ≤ k' := by exact_mod_cast hk'
    linarith

section Seq

variable {α : Type} (Q : ℕ → (ℕ → α) → Prop) (a : α) (h1 : ∀ c : ℕ → α, c 0 = a → Q 1 c)
  (hstep : ∀ R : ℕ, 1 ≤ R → ∀ c : ℕ → α, Q R c → ∃ e, Q (R + 1) (Function.update c R e))

def h3F : (n : ℕ) → {c : ℕ → α // c 0 = a ∧ Q (n + 1) c}
  | 0 => ⟨fun _ => a, rfl, h1 _ rfl⟩
  | n + 1 => ⟨Function.update (h3F n).1 (n + 1)
      (Classical.choose (hstep (n + 1) (by omega) _ (h3F n).2.2)),
      by rw [Function.update_of_ne (by omega)]; exact (h3F n).2.1,
      Classical.choose_spec (hstep (n + 1) (by omega) _ (h3F n).2.2)⟩

theorem recursiveSequence_stable (n r : ℕ) (hr : r ≤ n) : (h3F Q a h1 hstep n).1 r = (h3F Q a h1 hstep r).1 r := by
  induction n with
  | zero =>
    have : r = 0 := by omega
    rw [this]
  | succ n ih =>
    rcases Nat.lt_or_ge r (n + 1) with h | h
    · have e : (h3F Q a h1 hstep (n + 1)).1 r = (h3F Q a h1 hstep n).1 r := by
        change Function.update _ _ _ r = _
        rw [Function.update_of_ne (by omega)]
      rw [e, ih (by omega)]
    · have : r = n + 1 := by omega
      rw [this]

include h1 hstep in

theorem exists_sequence_of_extension (hcongr : ∀ (R : ℕ) (c c' : ℕ → α), (∀ r < R, c r = c' r) → Q R c → Q R c') :
    ∃ c : ℕ → α, c 0 = a ∧ ∀ R : ℕ, 1 ≤ R → Q R c := by
  refine ⟨fun r => (h3F Q a h1 hstep r).1 r, (h3F Q a h1 hstep 0).2.1, fun R hR => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
  exact hcongr (n + 1) _ _ (fun r hr => recursiveSequence_stable Q a h1 hstep n r (by omega))
    (h3F Q a h1 hstep n).2.2

end Seq

section Abs

variable {O A LL D : Type} [CommRing O] [CommRing A] [Algebra O A] [Field LL] [Algebra O LL]
  [AddCommGroup D] [Module O D] [Module A D] [IsScalarTower O A D]

def h3β {d : ℕ} (b : Fin d → D) (y : Fin d → O) : D := ∑ m, y m • b m

theorem h3β_add {d : ℕ} (b : Fin d → D) (y y' : Fin d → O) :
    h3β b (y + y') = h3β b y + h3β b y' := by
  simp [h3β, add_smul, Finset.sum_add_distrib]

theorem h3β_smul {d : ℕ} (b : Fin d → D) (a : O) (y : Fin d → O) :
    h3β b (a • y) = a • h3β b y := by
  simp [h3β, Finset.smul_sum, mul_smul]

theorem h3β_zero {d : ℕ} (b : Fin d → D) : h3β b (0 : Fin d → O) = 0 := by
  simp [h3β]

structure GammaEquationHypotheses (v : AddValuation LL (WithTop ℚ)) (p : ℕ) (P : A) (U : O) (g : D →ₗ[O] D)
    (N : Submodule O D) {d : ℕ} (b : Fin d → D) : Prop where
  hp : p.Prime
  inj : Function.Injective (algebraMap O LL)
  v_p : v ((p : ℕ) : LL) = 1
  v_int : ∀ y : O, 0 ≤ v (algebraMap O LL y)
  v_O : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x
  precomp_injective : ∀ x : D, P • x = 0 → x = 0
  P_N : ∀ x ∈ N, P • x ∈ N
  b_N : ∀ m, b m ∈ N
  dec : ∀ x ∈ N, ∃ y : Fin d → O, ∃ x' ∈ N, x = h3β b y + P • x'
  uniq : ∀ y : Fin d → O, (∃ x' ∈ N, h3β b y = P • x') → y = 0
  gr : ∀ (r : ℕ), ∀ x ∈ N, ∃ x' ∈ N,
    g (P ^ r • x) - P ^ r • x = (U ^ r - 1) • (P ^ r • x) + P ^ (r + 1) • x'
  val : ∀ r : ℕ, 1 ≤ r →
    v (algebraMap O LL (U ^ r - 1)) = ((1 + padicValNat p r : ℕ) : WithTop ℚ)

def h3P (LL : Type) [Field LL] [Algebra O LL] (p : ℕ) (P : A) (g : D →ₗ[O] D) (N : Submodule O D) {d : ℕ}
    (b : Fin d → D) (z : D) (c : ℕ → Fin d → LL) (R : ℕ) : Prop :=
  ∀ (k : ℕ) (y : ℕ → Fin d → O),
    (∀ r < R, ∀ m, algebraMap O LL (y r m) = ((p : ℕ) : LL) ^ k * c r m) →
    ∃ x, x ∈ N ∧ g (∑ r ∈ range R, P ^ r • h3β b (y r)) - (∑ r ∈ range R, P ^ r • h3β b (y r)) -
      ((p : ℕ) : O) ^ k • z = P ^ R • x

variable {v : AddValuation LL (WithTop ℚ)} {p : ℕ} {P : A} {U : O} {g : D →ₗ[O] D}
  {N : Submodule O D} {d : ℕ} {b : Fin d → D}

namespace GammaEquationHypotheses

variable (H : GammaEquationHypotheses v p P U g N b)
include H

theorem p_ne : ((p : ℕ) : LL) ≠ 0 := by
  intro h0
  have := H.v_p
  rw [h0, AddValuation.map_zero] at this
  exact absurd this (by simp)

theorem v_pow_mul (k : ℕ) (x : LL) : v (((p : ℕ) : LL) ^ k * x) = ((k : ℕ) : WithTop ℚ) + v x := by
  rw [AddValuation.map_mul, AddValuation.map_pow, H.v_p]
  simp

theorem β_N (y : Fin d → O) : h3β b y ∈ N :=
  N.sum_mem fun m _ => N.smul_mem _ (H.b_N m)

theorem Ppow_N (r : ℕ) (x : D) (hx : x ∈ N) : P ^ r • x ∈ N := by
  induction r with
  | zero => simpa using hx
  | succ r ih => rw [pow_succ', mul_smul]; exact H.P_N _ ih

theorem g_N (x : D) (hx : x ∈ N) : g x ∈ N := by
  obtain ⟨x', hx', e⟩ := H.gr 0 x hx
  simp only [pow_zero, one_smul, sub_self, zero_smul, zero_add, pow_one] at e
  have : g x = x + P • x' := by rw [← e]; abel
  rw [this]
  exact N.add_mem hx (H.P_N _ hx')

theorem tors_O (j : ℕ) (y : Fin d → O) (h : ((p : ℕ) : O) ^ j • y = 0) : y = 0 := by
  funext m
  have h1 := congrFun h m
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  apply H.inj
  have h2 := congrArg (algebraMap O LL) h1
  rw [map_mul, map_pow, map_natCast, map_zero] at h2
  change _ = algebraMap O LL 0
  rw [map_zero]
  exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ H.p_ne)

theorem tors (R j : ℕ) : ∀ e ∈ N, (∃ x ∈ N, ((p : ℕ) : O) ^ j • e = P ^ R • x) →
    ∃ x ∈ N, e = P ^ R • x := by
  induction R with
  | zero => intro e he _; exact ⟨e, he, by simp⟩
  | succ R ih =>
    intro e he ⟨x, hx, hex⟩
    obtain ⟨y, e', he', hdec⟩ := H.dec e he
    have h1 : h3β b (((p : ℕ) : O) ^ j • y) = P • (P ^ R • x - ((p : ℕ) : O) ^ j • e') := by
      rw [h3β_smul, smul_sub, ← mul_smul, ← pow_succ', ← hex, hdec, smul_add, smul_comm P]
      abel
    have hy : y = 0 := H.tors_O j y
      (H.uniq _ ⟨_, N.sub_mem (H.Ppow_N R x hx) (N.smul_mem _ he'), h1⟩)
    rw [hy, h3β_zero, zero_add] at hdec
    have h2 : ((p : ℕ) : O) ^ j • e' = P ^ R • x := by
      have : P • (((p : ℕ) : O) ^ j • e' - P ^ R • x) = 0 := by
        rw [smul_sub, ← mul_smul, ← pow_succ', ← hex, hdec, smul_comm P, sub_self]
      exact sub_eq_zero.1 (H.precomp_injective _ this)
    obtain ⟨x'', hx'', e''⟩ := ih e' he' ⟨x, hx, h2⟩
    exact ⟨x'', hx'', by rw [hdec, e'', ← mul_smul, ← pow_succ']⟩

theorem step (R k j : ℕ) (w z : D) (ξ yR : Fin d → O) (x' : D) (hx' : x' ∈ N)
    (E1 : g w - w - ((p : ℕ) : O) ^ k • z = P ^ R • (h3β b ξ + P • x')) :
    ∃ x'' ∈ N, g (((p : ℕ) : O) ^ j • w + P ^ R • h3β b yR) -
        (((p : ℕ) : O) ^ j • w + P ^ R • h3β b yR) - ((p : ℕ) : O) ^ (k + j) • z =
      P ^ R • h3β b (((p : ℕ) : O) ^ j • ξ + (U ^ R - 1) • yR) + P ^ (R + 1) • x'' := by
  obtain ⟨x₁, hx₁, e₁⟩ := H.gr R (h3β b yR) (H.β_N yR)
  refine ⟨((p : ℕ) : O) ^ j • x' + x₁, N.add_mem (N.smul_mem _ hx') hx₁, ?_⟩
  have h1 : g w = w + ((p : ℕ) : O) ^ k • z + P ^ R • (h3β b ξ + P • x') := by
    rw [← E1]; abel
  have h2 : g (P ^ R • h3β b yR) = P ^ R • h3β b yR + (U ^ R - 1) • (P ^ R • h3β b yR) +
      P ^ (R + 1) • x₁ := by
    rw [add_assoc, ← e₁]; abel
  rw [map_add, map_smul, h1, h2, h3β_add, h3β_smul, h3β_smul]
  simp only [← algebraMap_smul A (((p : ℕ) : O) ^ j), ← algebraMap_smul A (((p : ℕ) : O) ^ k),
    ← algebraMap_smul A (U ^ R - 1), pow_add]
  module

theorem clear1 (x : LL) : ∃ k : ℕ, ∀ k' ≥ k, 0 ≤ v (((p : ℕ) : LL) ^ k' * x) := by
  obtain ⟨k, hk⟩ := exists_nat_add_nonneg (v x)
  exact ⟨k, fun k' hk' => by rw [H.v_pow_mul]; exact hk k' hk'⟩

theorem clear {ι : Type} (s : Finset ι) (f : ι → LL) :
    ∃ k : ℕ, ∀ i ∈ s, ∀ k' ≥ k, 0 ≤ v (((p : ℕ) : LL) ^ k' * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨k₁, h₁⟩ := ih
    obtain ⟨k₂, h₂⟩ := H.clear1 (f a)
    refine ⟨max k₁ k₂, fun i hi k' hk' => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h₂ k' (le_trans (le_max_right _ _) hk')
    · exact h₁ i hi k' (le_trans (le_max_left _ _) hk')

theorem reps (R k : ℕ) (c : ℕ → Fin d → LL)
    (h : ∀ r < R, ∀ m, 0 ≤ v (((p : ℕ) : LL) ^ k * c r m)) :
    ∃ y : ℕ → Fin d → O, ∀ r < R, ∀ m, algebraMap O LL (y r m) = ((p : ℕ) : LL) ^ k * c r m := by
  have : ∀ r m, ∃ yy : O, r < R → algebraMap O LL yy = ((p : ℕ) : LL) ^ k * c r m := by
    intro r m
    by_cases hr : r < R
    · obtain ⟨yy, hyy⟩ := H.v_O _ (h r hr m)
      exact ⟨yy, fun _ => hyy⟩
    · exact ⟨0, fun h' => absurd h' hr⟩
  choose y hy using this
  exact ⟨y, fun r hr m => hy r m hr⟩

theorem congrP (z : D) (R : ℕ) (c c' : ℕ → Fin d → LL) (h : ∀ r < R, c r = c' r)
    (hP : h3P LL p P g N b z c R) : h3P LL p P g N b z c' R := fun k y hy =>
  hP k y fun r hr m => by rw [h r hr]; exact hy r hr m

theorem sum_N (R : ℕ) (y : ℕ → Fin d → O) : (∑ r ∈ range R, P ^ r • h3β b (y r)) ∈ N :=
  N.sum_mem fun r _ => H.Ppow_N r _ (H.β_N _)

theorem P0 (z : D) (hz : z ∈ N) (c : ℕ → Fin d → LL) : h3P LL p P g N b z c 0 := fun k _ _ =>
  ⟨-(((p : ℕ) : O) ^ k • z), N.neg_mem (N.smul_mem _ hz), by simp⟩

theorem P1 (z' : D) (hz' : z' ∈ N) (c : ℕ → Fin d → LL) : h3P LL p P g N b (P • z') c 1 := by
  intro k y _
  obtain ⟨x', hx', e⟩ := H.gr 0 (h3β b (y 0)) (H.β_N _)
  simp only [pow_zero, one_smul, sub_self, zero_smul, zero_add, pow_one] at e
  refine ⟨x' - ((p : ℕ) : O) ^ k • z', N.sub_mem hx' (N.smul_mem _ hz'), ?_⟩
  simp only [range_one, sum_singleton, pow_zero, one_smul, pow_one]
  rw [e, smul_sub, smul_comm P]

theorem stepP (z : D) (hz : z ∈ N) (R : ℕ) (hR : 1 ≤ R) (c : ℕ → Fin d → LL)
    (hP : h3P LL p P g N b z c R) : ∃ e, h3P LL p P g N b z (Function.update c R e) (R + 1) := by
  obtain ⟨k₀, hk₀⟩ := H.clear (range R ×ˢ (univ : Finset (Fin d))) (fun i => c i.1 i.2)
  obtain ⟨y₀, hy₀⟩ := H.reps R k₀ c
    (fun r hr m => hk₀ (r, m) (by simp [hr]) k₀ le_rfl)
  obtain ⟨xR, hxR, E0⟩ := hP k₀ y₀ hy₀
  obtain ⟨ξ, x', hx', hdec⟩ := H.dec xR hxR
  rw [hdec] at E0
  have ha : algebraMap O LL (U ^ R - 1) ≠ 0 := by
    intro h0
    have := H.val R hR
    rw [h0, AddValuation.map_zero] at this
    exact absurd this.symm (WithTop.natCast_ne_top _)
  have hp0 : ((p : ℕ) : LL) ≠ 0 := H.p_ne
  refine ⟨fun m => -(algebraMap O LL (ξ m)) / (algebraMap O LL (U ^ R - 1) * ((p : ℕ) : LL) ^ k₀), ?_⟩
  intro k y hy
  have hyr : ∀ r < R, ((p : ℕ) : O) ^ k₀ • y r = ((p : ℕ) : O) ^ k • y₀ r := by
    intro r hr
    funext m
    apply H.inj
    have h1 := hy r (by omega) m
    rw [Function.update_of_ne (by omega)] at h1
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [h1, hy₀ r hr m]
    ring
  have hW : ((p : ℕ) : O) ^ k₀ • (∑ r ∈ range R, P ^ r • h3β b (y r)) =
      ((p : ℕ) : O) ^ k • (∑ r ∈ range R, P ^ r • h3β b (y₀ r)) := by
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [smul_comm _ (P ^ r), ← h3β_smul, hyr r (Finset.mem_range.1 hr), h3β_smul, smul_comm _ (P ^ r)]
  obtain ⟨x'', hx'', E2⟩ := H.step R k₀ k _ z ξ (((p : ℕ) : O) ^ k₀ • y R) x' hx' E0
  have hη : ((p : ℕ) : O) ^ k • ξ + (U ^ R - 1) • (((p : ℕ) : O) ^ k₀ • y R) = 0 := by
    funext m
    apply H.inj
    have h1 := hy R (by omega) m
    rw [Function.update_self] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_pow, map_natCast,
      Pi.zero_apply]
    rw [h1, map_zero]
    field_simp
    ring
  rw [hη, h3β_zero, smul_zero, zero_add] at E2
  have hWN := H.sum_N (R + 1) y
  apply H.tors (R + 1) k₀ _ (N.sub_mem (N.sub_mem (H.g_N _ hWN) hWN) (N.smul_mem _ hz))
  refine ⟨x'', hx'', ?_⟩
  rw [← E2, smul_sub, smul_sub, ← map_smul, Finset.sum_range_succ, smul_add, hW, smul_comm _ (P ^ R),
    ← h3β_smul, smul_smul, ← pow_add]

theorem exists_sol (z' : D) (hz' : z' ∈ N) (c₀ : Fin d → LL) :
    ∃ c : ℕ → Fin d → LL, c 0 = c₀ ∧ ∀ R, h3P LL p P g N b (P • z') c R := by
  obtain ⟨c, hc0, hc⟩ := exists_sequence_of_extension (fun R c => h3P LL p P g N b (P • z') c R) c₀
    (fun c _ => H.P1 z' hz' c) (fun R hR c hP => H.stepP _ (H.P_N _ hz') R hR c hP)
    (fun R c c' h hP => H.congrP _ R c c' h hP)
  refine ⟨c, hc0, fun R => ?_⟩
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact H.P0 _ (H.P_N _ hz') c
  · exact hc R hR

end GammaEquationHypotheses

end Abs

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PartH3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def NΔi (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O (W.DD T) :=
  W.NΔ T ⊓ (W.Nl T i).restrictScalars O

theorem letter_idempotent_sq (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [letE]
  · simp [letE, hj]

theorem idempotent_smul_of_mem_letter' (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.Nl T i) : (letE i : LetA O n) • x = x := by
  obtain ⟨y, _, hyx⟩ := hx
  rw [← hyx]
  change (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
  rw [smul_smul, letter_idempotent_sq]

theorem idempotent_mem_invariants (W : LocWach PD LL O v n) (i : ZMod n) : (letE i : LetA O n) ∈ W.AΔ :=
  fun δ _ => gammaA_letter_idempotent W δ i

theorem uniformizer_constantCoeff_zero (W : LocWach PD LL O v n) (h9 : P9π₀ W) (i : ZMod n) :
    PowerSeries.constantCoeff (W.π₀ i) = 0 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := h9
  have hk : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have : W.π₀ i = (w : LetA O n) i * PowerSeries.X ^ (PD.p - 1) := by
    conv_lhs => rw [hw]
    rfl
  rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]

theorem uniformizer_mul_left_cancel (W : LocWach PD LL O v n) (h9 : P9π₀ W) (a b : LetA O n)
    (hab : W.π₀ * a = W.π₀ * b) : a = b := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := h9
  rw [hw] at hab
  exact unit_mul_pi_pow_left_cancel w _ a b hab

theorem uniformizer_smul_injective (W : LocWach PD LL O v n) (h9 : P9π₀ W) (T : LocLat G Qp LL O) (x : W.DD T)
    (hx : W.π₀ • x = 0) : x = 0 := by
  obtain ⟨-, -, ⟨w, hw⟩, -⟩ := h9
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  rw [← algebraMap_smul W.EE] at hx
  exact (hu.smul_eq_zero).1 hx

theorem invariants_eq_constants_add_uniformizer (W : LocWach PD LL O v n) (h9 : P9π₀ W) (a : LetA O n) (ha : a ∈ W.AΔ) :
    ∃ (a₀ : ZMod n → O) (t : LetA O n), t ∈ W.AΔ ∧
      a = (fun j => PowerSeries.C (a₀ j)) + W.π₀ * t := by
  have hπΔ : W.π₀ ∈ W.AΔ := h9.1
  obtain ⟨f, hf, -⟩ := h9.2.1 a ha
  set t : LetA O n := fun i =>
    PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) with ht
  set κ : LetA O n := fun j => PowerSeries.C (PowerSeries.constantCoeff (f j)) with hκ
  have hat : a = κ + W.π₀ * t := by
    funext i
    have hs : PowerSeries.HasSubst (W.π₀ i) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (uniformizer_constantCoeff_zero W h9 i)
    have e1 := hf i
    rw [PowerSeries.eq_X_mul_shift_add_const (f i), PowerSeries.subst_add hs, PowerSeries.subst_mul hs,
      PowerSeries.subst_X hs, PowerSeries.subst_C] at e1
    have e2 : a i = W.π₀ i * t i + PowerSeries.C (PowerSeries.constantCoeff (f i)) := e1
    rw [e2, add_comm]
    rfl
  have hκΔ : κ ∈ W.AΔ := by
    intro δ _
    funext j
    change W.γ₀ δ (PowerSeries.C (PowerSeries.constantCoeff (f j))) = _
    have : ∀ c : O, PowerSeries.C c = algebraMap O (PowerSeries O) c := fun c => by simp
    rw [this, AlgHom.commutes]
    rfl
  refine ⟨fun j => PowerSeries.constantCoeff (f j), t, ?_, hat⟩
  intro δ hδ
  apply uniformizer_mul_left_cancel W h9
  have h1 : W.π₀ * t = a - κ := by rw [hat]; ring
  have h2 : W.γA δ (W.π₀ * t) = W.π₀ * t := by
    rw [h1]; exact W.AΔ.sub_mem ha hκΔ δ hδ
  rw [map_mul, hπΔ δ hδ] at h2
  exact h2

theorem gamma_equation_hypotheses_hold (W : LocWach PD LL O v n) (hO1 : ∀ y : O, 0 ≤ v (algebraMap O LL y))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hO3 : Function.Injective (algebraMap O LL)) (h9 : P9π₀ W) (T : LocLat G Qp LL O)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hval : coreHval W) (i : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (hb : IsFrameΔ W T i b) :
    GammaEquationHypotheses v PD.p W.π₀ (u₁ W) (W.γ T) (NΔi W T i) b where
  hp := PD.hp
  inj := hO3
  v_p := W.v_l
  v_int := hO1
  v_O := hO2
  precomp_injective := uniformizer_smul_injective W h9 T
  P_N := fun x hx => ⟨invariant_smul_mem_invariants' W T _ h9.1 x hx.1, (W.Nl T i).smul_mem _ hx.2⟩
  b_N := hb.1
  dec := by
    intro x hx
    obtain ⟨a, ⟨ha, hxa⟩, -⟩ := hb.2 x hx
    have hsp := fun m => invariants_eq_constants_add_uniformizer W h9 (a m) (ha m).1
    choose a₀ t ht hat using hsp
    refine ⟨fun m => a₀ m i, ∑ m, t m • b m, ?_, ?_⟩
    · exact (NΔi W T i).sum_mem fun m _ =>
        ⟨invariant_smul_mem_invariants' W T _ (ht m) _ (hb.1 m).1, (W.Nl T i).smul_mem _ (hb.1 m).2⟩
    · rw [hxa, h3β, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hE := idempotent_smul_of_mem_letter' W T i (b m) (hb.1 m).2
      have h1 : ((fun j => PowerSeries.C (a₀ m j)) : LetA O n) * letE i =
          algebraMap O (LetA O n) (a₀ m i) * letE i := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [letE]
        · simp [letE, hj]
      have h2 : ((fun j => PowerSeries.C (a₀ m j)) : LetA O n) • b m = a₀ m i • b m := by
        conv_lhs => rw [← hE]
        rw [smul_smul, h1, mul_smul, hE, algebraMap_smul]
      conv_lhs => rw [hat m]
      rw [add_smul, h2, mul_smul]
  uniq := by
    intro y ⟨x', hx', hyx⟩
    obtain ⟨a', ⟨ha', hxa'⟩, -⟩ := hb.2 x' hx'
    have hX : InNΔi W T i (h3β b y) :=
      (NΔi W T i).sum_mem fun m _ => (NΔi W T i).smul_mem _ (hb.1 m)
    have hu := (hb.2 _ hX).unique
      (y₁ := fun m => (letE i : LetA O n) * algebraMap O (LetA O n) (y m))
      (y₂ := fun m => W.π₀ * a' m)
      ⟨fun m => ⟨W.AΔ.mul_mem (idempotent_mem_invariants W i) (W.AΔ.algebraMap_mem _), by
          rw [← mul_assoc, letter_idempotent_sq]⟩, by
        rw [h3β]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_comm, mul_smul, idempotent_smul_of_mem_letter' W T i (b m) (hb.1 m).2, algebraMap_smul]⟩
      ⟨fun m => ⟨W.AΔ.mul_mem h9.1 (ha' m).1, by
          rw [mul_left_comm, (ha' m).2]⟩, by
        rw [hyx, hxa', Finset.smul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [mul_smul]⟩
    funext m
    have h1 := congrArg PowerSeries.constantCoeff (congrFun (congrFun hu m) i)
    have h2 : ((letE i : LetA O n) * algebraMap O (LetA O n) (y m)) i = PowerSeries.C (y m) := by
      simp [letE]
    have h3 : (W.π₀ * a' m) i = W.π₀ i * a' m i := rfl
    rw [h2, h3, PowerSeries.constantCoeff_C, map_mul, uniformizer_constantCoeff_zero W h9, zero_mul] at h1
    exact h1
  gr := first_H_clause_of_uniformizer W T i h9 hm
  val := hval

theorem coreH_sol_exists (W : LocWach PD LL O v n) (hO1 : ∀ y : O, 0 ≤ v (algebraMap O LL y))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hO3 : Function.Injective (algebraMap O LL)) (h9 : P9π₀ W) (T : LocLat G Qp LL O)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hval : coreHval W) (i : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (hb : IsFrameΔ W T i b) (z : W.DD T)
    (hz : ∃ z', InNΔi W T i z' ∧ z = W.π₀ • z') (c₀ : Fin d → O) :
    ∃ c : ℕ → Fin d → LL, IsSol W T i b z c ∧ c 0 = fun m => algebraMap O LL (c₀ m) := by
  obtain ⟨z', hz', rfl⟩ := hz
  obtain ⟨c, hc0, hc⟩ := (gamma_equation_hypotheses_hold W hO1 hO2 hO3 h9 T hm hval i b hb).exists_sol z' hz'
    (fun m => algebraMap O LL (c₀ m))
  exact ⟨c, fun R k y hy => hc R k y hy, hc0⟩

end PartH3

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Frame

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def frameI {LL : Type} [Field LL] (v : AddValuation LL (WithTop ℚ)) (d : ℕ) :
    Subring (Matrix (Fin d) (Fin d) LL) where
  carrier := {M | ∀ i j, 0 ≤ v (M i j)}
  mul_mem' := by
    intro a b ha hb i j
    rw [Matrix.mul_apply]
    refine v.map_le_sum fun k _ => ?_
    rw [v.map_mul]
    exact add_nonneg (ha i k) (hb k j)
  one_mem' := by
    intro i j
    show 0 ≤ v ((1 : Matrix (Fin d) (Fin d) LL) i j)
    rw [Matrix.one_apply]
    split_ifs
    · rw [v.map_one]
    · rw [v.map_zero]
      exact le_top
  add_mem' := by
    intro a b ha hb i j
    exact v.map_le_add (ha i j) (hb i j)
  zero_mem' := by
    intro i j
    simp [v.map_zero]
  neg_mem' := by
    intro a ha i j
    rw [Matrix.neg_apply, v.map_neg]
    exact ha i j

theorem frame_entry {LL : Type} [Field LL] {d : ℕ} (c a : ℕ) (C : Matrix (Fin d) (Fin d) LL)
    (i j : Fin d) :
    (((c : Matrix (Fin d) (Fin d) LL)) ^ a * C) i j = (c : LL) ^ a * C i j := by
  rw [← Nat.cast_pow, ← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem frame_bd_iff (W : LocWach PD LL O v n) (r : ℕ) (x : LL) :
    Bd W r x ↔ 0 ≤ v ((PD.p : LL) ^ Formalism.RepresentationBoundsCohomology.N2.aH PD.p r * x) := by
  rw [v.map_mul, v.map_pow, W.v_l, nsmul_one]
  unfold Bd Formalism.RepresentationBoundsCohomology.N2.aH
  induction v x using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    rw [← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe,
      WithTop.coe_le_coe]
    constructor <;> intro h <;> linarith

theorem coreH_inv_holds (W : LocWach PD LL O v n) {d : ℕ} (sol : Fin d → ℕ → Fin d → LL)
    (h0 : ∀ k, sol k 0 = Pi.single k 1) (hB : ∀ k r m, Bd W r (sol k r m)) :
    ∀ m k r, Bd W r (PowerSeries.coeff r
      ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ m k)) := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  set M : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hM
  have hc0 : M.map (PowerSeries.coeff (R := LL) 0) = 1 := by
    ext i j
    simp [hM, h0, Matrix.one_apply, Pi.single_apply]
  have hdet : IsUnit M.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h1 : PowerSeries.coeff (R := LL) 0 M.det = (M.map (PowerSeries.coeff (R := LL) 0)).det := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff]
      exact RingHom.map_det _ M
    rw [h1, hc0, Matrix.det_one]
    exact isUnit_one
  have hmul : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hconv : ∀ r, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal r,
      M.map (PowerSeries.coeff (R := LL) p.1) * (M⁻¹).map (PowerSeries.coeff (R := LL) p.2) =
        (1 : Matrix (Fin d) (Fin d) (PowerSeries LL)).map (PowerSeries.coeff (R := LL) r) := by
    intro r
    rw [← hmul]
    ext i j
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.map_apply, map_sum, PowerSeries.coeff_mul]
    rw [Finset.sum_comm]
  have hone0 : (1 : Matrix (Fin d) (Fin d) (PowerSeries LL)).map (PowerSeries.coeff (R := LL) 0) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hone : ∀ r, 1 ≤ r →
      (1 : Matrix (Fin d) (Fin d) (PowerSeries LL)).map (PowerSeries.coeff (R := LL) r) = 0 := by
    intro r hr
    ext i j
    have hr' : r ≠ 0 := by omega
    by_cases h : i = j <;> simp [h, PowerSeries.coeff_one, hr']
  have hc0' : (M⁻¹).map (PowerSeries.coeff (R := LL) 0) = 1 := by
    have h := hconv 0
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hc0, one_mul, hone0] at h
    exact h
  have key := Formalism.RepresentationBoundsCohomology.N2.superadditivity_frame_all.2.1 PD.p (Matrix (Fin d) (Fin d) LL) (frameI v d)
    (fun r => M.map (PowerSeries.coeff (R := LL) r)) (fun r => (M⁻¹).map (PowerSeries.coeff (R := LL) r))
    hc0 hc0'
    (by
      intro r i j
      rw [frame_entry]
      refine (frame_bd_iff W r _).1 ?_
      simpa [hM] using hB j r i)
    (by
      intro r hr
      rw [hconv r, hone r hr])
  intro m k r
  have h := key r m k
  rw [frame_entry] at h
  exact (frame_bd_iff W r _).2 h

theorem coreH_frames_of_sol (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (h3 : ∀ (d : ℕ) (b : Fin d → W.DD T), IsFrameΔ W T i b →
      ∀ z : W.DD T, (∃ z', InNΔi W T i z' ∧ z = W.π₀ • z') → ∀ c₀ : Fin d → O,
        (∃ c : ℕ → Fin d → LL, IsSol W T i b z c ∧ c 0 = fun m => algebraMap O LL (c₀ m)) ∧
        ∀ c : ℕ → Fin d → LL, IsSol W T i b z c → c 0 = (fun m => algebraMap O LL (c₀ m)) →
          ∀ r m, Bd W r (c r m)) :
    ∀ (d : ℕ) (b : Fin d → W.DD T), IsFrameΔ W T i b → ∀ sol : Fin d → ℕ → Fin d → LL,
      (∀ k, IsSol W T i b 0 (sol k) ∧ sol k 0 = Pi.single k 1) →
        (∀ k r m, Bd W r (sol k r m)) ∧
        ∀ m k r, Bd W r (PowerSeries.coeff r
          ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
            Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ m k)) := by
  intro d b hb sol hsol
  have hB : ∀ k r m, Bd W r (sol k r m) := by
    intro k
    refine (h3 d b hb 0 ⟨0, ⟨(W.NΔ T).zero_mem, (W.Nl T i).zero_mem⟩, (smul_zero _).symm⟩
      (Pi.single k 1)).2 (sol k) (hsol k).1 ?_
    rw [(hsol k).2]
    funext m
    by_cases h : m = k
    · subst h
      simp
    · simp [h]
  exact ⟨hB, coreH_inv_holds W sol (fun k => (hsol k).2) hB⟩

theorem coreH_of_parts (W : LocWach PD LL O v n)
    (h1 : CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ i : ZMod n,
      ∀ (r : ℕ) (x : W.DD T), InNΔi W T i x → ∃ x', InNΔi W T i x' ∧
        W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x =
          (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x')
    (h2 : CaseA W → ∀ r : ℕ, 1 ≤ r →
      v (algebraMap O LL (u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ))
    (h3 : CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ i : ZMod n,
      ∀ (d : ℕ) (b : Fin d → W.DD T), IsFrameΔ W T i b →
      ∀ z : W.DD T, (∃ z', InNΔi W T i z' ∧ z = W.π₀ • z') → ∀ c₀ : Fin d → O,
        (∃ c : ℕ → Fin d → LL, IsSol W T i b z c ∧ c 0 = fun m => algebraMap O LL (c₀ m)) ∧
        ∀ c : ℕ → Fin d → LL, IsSol W T i b z c → c 0 = (fun m => algebraMap O LL (c₀ m)) →
          ∀ r m, Bd W r (c r m))
    (h4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1)) :
    coreH W := fun hA T hT i =>
  ⟨h1 hA T hT i, h2 hA, h3 hA T hT i, h4, coreH_frames_of_sol W T i (h3 hA T hT i)⟩

end Frame

section FrameG

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem frame_γD_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n)
    (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem frame_γA_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    W.γA g (letE i) = letE i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [LocWach.γA, letγ, letE]
  · simp [LocWach.γA, letγ, letE, h]

theorem frame_letE_idem (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [letE]
  · simp [letE, h]

theorem frame_smul_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (hx : InNΔi W T i x) : InNΔi W T i (a • x) := by
  obtain ⟨⟨hN, hΔ⟩, hl⟩ := hx
  refine ⟨⟨(W.N T).smul_mem a hN, fun δ hδ => ?_⟩, (W.Nl T i).smul_mem a hl⟩
  rw [frame_γD_smul, ha δ hδ, hΔ δ hδ]

theorem frame_add_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    {x y : W.DD T} (hx : InNΔi W T i x) (hy : InNΔi W T i y) : InNΔi W T i (x + y) :=
  ⟨(W.NΔ T).add_mem hx.1 hy.1, (W.Nl T i).add_mem hx.2 hy.2⟩

theorem frame_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    {x : W.DD T} (hx : x ∈ W.NΔ T) : InNΔi W T i ((letE i : LetA O n) • x) := by
  obtain ⟨hN, hΔ⟩ := hx
  refine ⟨⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_⟩, ⟨x, hN, rfl⟩⟩
  rw [frame_γD_smul, frame_γA_letE, hΔ δ hδ]

theorem frame_letE_fix (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    {x : W.DD T} (hx : x ∈ W.Nl T i) : (letE i : LetA O n) • x = x := by
  obtain ⟨y, _, rfl⟩ := hx
  show (letE i : LetA O n) • ((letE i : LetA O n) • y) = (letE i : LetA O n) • y
  rw [smul_smul, frame_letE_idem]

theorem frame_graded (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hπ : W.π₀ ∈ W.AΔ)
    (hγ : ∃ t ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * (algebraMap O (LetA O n) (u₁ W) + W.π₀ * t))
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = W.π₀ • x') (i : ZMod n)
    (r : ℕ) (x : W.DD T) (hx : InNΔi W T i x) : ∃ x', InNΔi W T i x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x =
        (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x' := by
  obtain ⟨t, ht, hγ⟩ := hγ
  have hpow : ∀ r : ℕ, ∃ tr ∈ W.AΔ, (W.γA W.gam W.π₀) ^ r =
      W.π₀ ^ r * (algebraMap O (LetA O n) (u₁ W ^ r) + W.π₀ * tr) := by
    intro r
    induction r with
    | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
    | succ r ih =>
      obtain ⟨tr, htr, h⟩ := ih
      refine ⟨algebraMap O (LetA O n) (u₁ W ^ r) * t + tr * algebraMap O (LetA O n) (u₁ W) +
        W.π₀ * tr * t, ?_, ?_⟩
      · exact W.AΔ.add_mem (W.AΔ.add_mem (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) ht)
          (W.AΔ.mul_mem htr (W.AΔ.algebraMap_mem _))) (W.AΔ.mul_mem (W.AΔ.mul_mem hπ htr) ht)
      · rw [pow_succ, h, hγ, pow_succ (u₁ W), map_mul]
        ring
  obtain ⟨tr, htr, hr⟩ := hpow r
  obtain ⟨x₂, hx₂, hx₂e⟩ := hm x hx.1
  have he : W.γ T x - x = W.π₀ • ((letE i : LetA O n) • x₂) := by
    have h1 : (letE i : LetA O n) • (W.γ T x - x) = W.γ T x - x := by
      have : W.γ T x = W.γ T ((letE i : LetA O n) • x) := by rw [frame_letE_fix W T i hx.2]
      rw [smul_sub, frame_letE_fix W T i hx.2]
      congr 1
      conv_rhs => rw [this]
      show _ = W.γD T W.gam _
      rw [frame_γD_smul, frame_γA_letE]
      rfl
    rw [← h1, hx₂e, smul_comm]
  have hx₃ := frame_letE_mem W T i hx₂
  set x₃ := (letE i : LetA O n) • x₂ with hx₃d
  refine ⟨tr • x + (algebraMap O (LetA O n) (u₁ W ^ r) + W.π₀ * tr) • x₃, ?_, ?_⟩
  · exact frame_add_mem W T i (frame_smul_mem W T i htr hx)
      (frame_smul_mem W T i (W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hπ htr)) hx₃)
  · have hγx : W.γ T x = x + W.π₀ • x₃ := by rw [← he]; abel
    have h2 : W.γ T (W.π₀ ^ r • x) = (W.γA W.gam W.π₀) ^ r • W.γ T x := by
      show W.γD T W.gam _ = _
      rw [frame_γD_smul, map_pow]
      rfl
    rw [h2, hr, hγx, ← algebraMap_smul (LetA O n) (u₁ W ^ r - 1), map_sub, map_one, pow_succ]
    generalize algebraMap O (LetA O n) (u₁ W ^ r) = U
    generalize W.π₀ ^ r = P
    generalize W.π₀ = p₀
    have e1 : (P * (U + p₀ * tr)) • (x + p₀ • x₃) - P • x =
        (P * (U + p₀ * tr) - P) • x + (P * (U + p₀ * tr) * p₀) • x₃ := by
      rw [smul_add, smul_smul, sub_smul]
      abel
    have e2 : (U - 1) • P • x + (P * p₀) • (tr • x + (U + p₀ * tr) • x₃) =
        ((U - 1) * P + P * p₀ * tr) • x + (P * p₀ * (U + p₀ * tr)) • x₃ := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, add_smul]
      abel
    rw [e1, e2]
    congr 2 <;> ring

end FrameG

section FrameP

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem frame_reg (u : (LetA O n)ˣ) (k : ℕ) (a : LetA O n)
    (h : ((u : LetA O n) * letπ ^ k) * a = 0) : a = 0 := by
  rw [mul_assoc, Units.mul_right_eq_zero] at h
  funext i
  ext m
  have h1 := congrArg (fun b : LetA O n => PowerSeries.coeff (m + k) (b i)) h
  simp only [Pi.mul_apply, Pi.pow_apply, letπ, PowerSeries.coeff_X_pow_mul, Pi.zero_apply,
    map_zero] at h1
  simpa using h1

theorem frame_const (g₀ : PowerSeries O →ₐ[O] PowerSeries O)
    (h : PowerSeries.constantCoeff (g₀ PowerSeries.X) = 0) (f : PowerSeries O) :
    PowerSeries.constantCoeff (g₀ f) = PowerSeries.constantCoeff f := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
  have hC : ∀ c : O, g₀ (PowerSeries.C c) = PowerSeries.C c := fun c => g₀.commutes c
  rw [map_add, map_mul, hC, map_add, map_mul, h, zero_mul, zero_add, PowerSeries.constantCoeff_C]

theorem frame_γA_comm (W : LocWach PD LL O v n) (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext i
  have h1 : W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i)) := by
    have e1 : W.γ₀ (g * h) (a i) = W.γ₀ g (W.γ₀ h (a i)) := by rw [map_mul]; rfl
    have e2 : W.γ₀ (h * g) (a i) = W.γ₀ h (W.γ₀ g (a i)) := by rw [map_mul]; rfl
    rw [← e1, ← e2, mul_comm]
  simpa [LocWach.γA, letγ] using h1

theorem gamma_uniformizer_eq_mul_unit (W : LocWach PD LL O v n) (E : ZMod n → Polynomial O)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ E) :
    ∃ t ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * (algebraMap O (LetA O n) (u₁ W) + W.π₀ * t) := by
  obtain ⟨hπ, hsub, ⟨w', hw'⟩, _, _, _, ⟨w, hw⟩, _⟩ := h9
  have hp1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hπ
  set g : LetA O n := 1 + (w : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E W.π₀ with hgd
  have hg : W.γA W.gam W.π₀ = W.π₀ * g := by
    rw [hgd]
    linear_combination hw

  have hreg : ∀ a : LetA O n, W.π₀ * a = 0 → a = 0 := by
    intro a ha
    rw [hw'] at ha
    exact frame_reg w' _ a ha

  have hgΔ : g ∈ W.AΔ := by
    intro δ hδ
    have : W.π₀ * (W.γA δ g - g) = 0 := by
      have e : W.γA δ (W.π₀ * g) = W.π₀ * g := by
        rw [← hg, frame_γA_comm, hπΔ δ hδ]
      rw [map_mul, hπΔ δ hδ] at e
      rw [mul_sub, e, sub_self]
    exact sub_eq_zero.1 (hreg _ this)

  set s₀ : PowerSeries O := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (W.γ₀ W.gam PowerSeries.X)
    with hs₀
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X * s₀ := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hs₀c : PowerSeries.constantCoeff s₀ = ((uγ W : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hs₀, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  have hπS : W.γA W.gam letπ = letπ * (fun _ => s₀) := by
    funext i
    simpa [LocWach.γA, letγ, letπ] using hX
  have hkey : (w' : LetA O n) * g = W.γA W.gam (w' : LetA O n) * (fun _ => s₀) ^ (PD.p - 1) := by
    have e : ((1 : (LetA O n)ˣ) : LetA O n) * letπ ^ (PD.p - 1) *
        ((w' : LetA O n) * g - W.γA W.gam (w' : LetA O n) * (fun _ => s₀) ^ (PD.p - 1)) = 0 := by
      have e1 := hg
      conv_lhs at e1 => rw [hw', map_mul, map_pow, hπS, mul_pow]
      conv_rhs at e1 => rw [hw']
      rw [Units.val_one]
      linear_combination -e1
    exact sub_eq_zero.1 (frame_reg 1 _ _ e)
  have hgc : ∀ i, PowerSeries.constantCoeff (g i) = u₁ W := by
    intro i
    have e := congrArg (fun b : LetA O n => PowerSeries.constantCoeff (b i)) hkey
    simp only [Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, hs₀c] at e
    have e2 : PowerSeries.constantCoeff (W.γA W.gam (w' : LetA O n) i) =
        PowerSeries.constantCoeff ((w' : LetA O n) i) := by
      have := frame_const (W.γ₀ W.gam) (W.γ₀_X W.gam).1 ((w' : LetA O n) i)
      simpa [LocWach.γA, letγ] using this
    rw [e2] at e
    have hu : IsUnit (PowerSeries.constantCoeff ((w' : LetA O n) i)) :=
      (w'.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map
        (PowerSeries.constantCoeff (R := O))
    exact hu.mul_left_cancel e

  have hhΔ : g - algebraMap O (LetA O n) (u₁ W) ∈ W.AΔ := W.AΔ.sub_mem hgΔ (W.AΔ.algebraMap_mem _)
  obtain ⟨f, hf, _⟩ := hsub _ hhΔ
  have hπc : ∀ i, PowerSeries.constantCoeff (W.π₀ i) = 0 := by
    intro i
    rw [hw']
    simp only [Pi.mul_apply, Pi.pow_apply, letπ, map_mul, map_pow, PowerSeries.constantCoeff_X]
    rw [zero_pow (by omega), mul_zero]
  have hdiv : ∀ i, (g - algebraMap O (LetA O n) (u₁ W)) i = W.π₀ i *
      PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (f i)) := by
    intro i
    have hs : PowerSeries.HasSubst (W.π₀ i) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπc i)
    have e := hf i
    rw [PowerSeries.eq_X_mul_shift_add_const (f i), ← PowerSeries.coe_substAlgHom hs, map_add,
      map_mul, PowerSeries.substAlgHom_X] at e
    have hC : PowerSeries.substAlgHom hs (PowerSeries.C (PowerSeries.constantCoeff (f i))) =
        PowerSeries.C (PowerSeries.constantCoeff (f i)) :=
      (PowerSeries.substAlgHom hs).commutes _
    rw [hC] at e
    have e0 := congrArg (PowerSeries.constantCoeff (R := O)) e
    rw [map_add, map_mul, hπc i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at e0
    have e1 : PowerSeries.constantCoeff ((g - algebraMap O (LetA O n) (u₁ W)) i) = 0 := by
      rw [Pi.sub_apply, map_sub, hgc i]
      simp
    rw [e1] at e0
    rw [e, ← e0, map_zero, add_zero, PowerSeries.coe_substAlgHom hs]
  set t : LetA O n := fun i =>
    PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (f i)) with htd
  have hht : g - algebraMap O (LetA O n) (u₁ W) = W.π₀ * t := by
    funext i
    exact hdiv i
  refine ⟨t, ?_, ?_⟩
  · intro δ hδ
    have : W.π₀ * (W.γA δ t - t) = 0 := by
      have e : W.γA δ (W.π₀ * t) = W.π₀ * t := by
        rw [← hht]
        exact hhΔ δ hδ
      rw [map_mul, hπΔ δ hδ] at e
      rw [mul_sub, e, sub_self]
    exact sub_eq_zero.1 (hreg _ this)
  · rw [hg, ← hht]
    ring

end FrameP

section FrameC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem frame_finrank_one (W : LocWach PD LL O v n) (hA : CaseA W) : Module.finrank K₀ K = 1 := by
  have e := (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq
  rw [Module.finrank_self] at e
  exact e.symm

theorem frame_p9A (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) ∧
      Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ :=
  (h9 T hT hA.2.1 hA.2.2).2.2 (frame_finrank_one W hA)

theorem coreH_graded_of (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (r : ℕ) (x : W.DD T)
    (hx : InNΔi W T i x) : ∃ x', InNΔi W T i x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x =
        (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x' :=
  frame_graded W T (frame_p9A W h9 hA T hT).1.1 (gamma_uniformizer_eq_mul_unit W _ (frame_p9A W h9 hA T hT).1)
    (frame_p9A W h9 hA T hT).2.2 i r x hx

end FrameC

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section FrameS

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def frameε (O : Type) [CommRing O] (n : ℕ) (i : ZMod n) : LetA O n →+* O :=
  (PowerSeries.constantCoeff (R := O)).comp (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)

theorem frameε_letE (i : ZMod n) : frameε O n i (letE i) = 1 := by
  simp [frameε, letE]

theorem frameε_alg (i : ZMod n) (c : O) : frameε O n i (algebraMap O (LetA O n) c) = c := by
  simp [frameε]

theorem frameε_π₀ (W : LocWach PD LL O v n)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (i : ZMod n) :
    frameε O n i W.π₀ = 0 := by
  obtain ⟨w, hw⟩ := hw
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  rw [hw]
  simp [frameε, letπ, hp1]

theorem frame_π₀_inj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (r : ℕ) (x : W.DD T)
    (h : W.π₀ ^ r • x = 0) : x = 0 := by
  obtain ⟨w, hw⟩ := hw
  have hu : IsUnit (algebraMap (LetA O n) W.EE (W.π₀ ^ r)) := by
    rw [hw, map_pow, map_mul, map_pow]
    exact ((w.isUnit.map _).mul (W.EE_π.pow _)).pow _
  rw [← algebraMap_smul W.EE] at h
  exact (hu.smul_eq_zero).1 h

theorem frame_vecB_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T) (c : O) (y : Fin d → O) :
    vecB W T b (fun m => c * y m) = c • vecB W T b y := by
  simp [vecB, Finset.smul_sum, mul_smul]

theorem frame_vecB_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (hb : IsFrameΔ W T i b) (y : Fin d → O) : InNΔi W T i (vecB W T b y) := by
  refine ⟨(W.NΔ T).sum_mem fun m _ => (W.NΔ T).smul_mem _ (hb.1 m).1, ?_⟩
  refine (W.Nl T i).sum_mem fun m _ => ?_
  rw [← algebraMap_smul (LetA O n) (y m) (b m)]
  exact (W.Nl T i).smul_mem _ (hb.1 m).2

theorem frame_red (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (hπΔ : W.π₀ ∈ W.AΔ) {d : ℕ}
    (b : Fin d → W.DD T) (hb : IsFrameΔ W T i b) (y : Fin d → O) (c q : O) (x₁ x₂ : W.DD T)
    (hx₁ : InNΔi W T i x₁) (hx₂ : InNΔi W T i x₂)
    (h : c • vecB W T b y + q • x₁ = W.π₀ • x₂) : ∃ e : Fin d → O, ∀ m, c * y m + q * e m = 0 := by
  obtain ⟨a₁, ⟨ha₁, hxa₁⟩, _⟩ := hb.2 x₁ hx₁
  obtain ⟨a₂, ⟨ha₂, hxa₂⟩, _⟩ := hb.2 x₂ hx₂
  have hmem : InNΔi W T i (W.π₀ • x₂) := frame_smul_mem W T i hπΔ hx₂
  have hE : (letE i : LetA O n) ∈ W.AΔ := fun δ _ => frame_γA_letE W δ i
  have hbm : ∀ m, (letE i : LetA O n) • b m = b m := fun m => frame_letE_fix W T i (hb.1 m).2
  have huniq := (hb.2 _ hmem).unique
    (y₁ := fun m => letE i * algebraMap O (LetA O n) (c * y m) + algebraMap O (LetA O n) q * a₁ m)
    (y₂ := fun m => W.π₀ * a₂ m)
    ⟨fun m => ⟨W.AΔ.add_mem (W.AΔ.mul_mem hE (W.AΔ.algebraMap_mem _))
        (W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (ha₁ m).1), by
        rw [mul_add, ← mul_assoc, frame_letE_idem, mul_left_comm, (ha₁ m).2]⟩, by
      calc W.π₀ • x₂ = c • vecB W T b y + q • x₁ := h.symm
        _ = c • (∑ m, y m • b m) + q • ∑ m, a₁ m • b m := by rw [← hxa₁]; rfl
        _ = _ := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [add_smul, mul_comm (letE i), mul_smul, hbm, mul_smul, algebraMap_smul,
            algebraMap_smul, mul_smul]⟩
    ⟨fun m => ⟨W.AΔ.mul_mem hπΔ (ha₂ m).1, by rw [mul_left_comm, (ha₂ m).2]⟩, by
      conv_lhs => rw [hxa₂]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => (mul_smul _ _ _).symm⟩
  refine ⟨fun m => frameε O n i (a₁ m), fun m => ?_⟩
  have e := congrArg (frameε O n i) (congrFun huniq m)
  simpa [map_add, map_mul, frameε_letE, frameε_alg, frameε_π₀ W hw i] using e

theorem frame_aH_succ (p : ℕ) [Fact p.Prime] (s : ℕ) :
    Formalism.RepresentationBoundsCohomology.N2.aH p (s + 1) = Formalism.RepresentationBoundsCohomology.N2.aH p s + (1 + padicValNat p (s + 1)) := by
  unfold Formalism.RepresentationBoundsCohomology.N2.aH
  rw [Nat.factorial_succ, padicValNat.mul (show s + 1 ≠ 0 by omega) (Nat.factorial_ne_zero s)]
  omega

theorem frame_aH_mono (p : ℕ) [Fact p.Prime] {j s : ℕ} (h : j ≤ s) :
    Formalism.RepresentationBoundsCohomology.N2.aH p j ≤ Formalism.RepresentationBoundsCohomology.N2.aH p s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  have := Formalism.RepresentationBoundsCohomology.N2.superadditivity_frame_all.1 p j t
  omega

theorem frame_exists_k (W : LocWach PD LL O v n) (x : LL) :
    ∃ k : ℕ, 0 ≤ v ((PD.p : LL) ^ k * x) := by
  induction hx : v x using WithTop.recTopCoe with
  | top => exact ⟨0, by rw [v.map_mul, hx]; simp⟩
  | coe q =>
    obtain ⟨k, hk⟩ := exists_nat_ge (-q)
    refine ⟨k, ?_⟩
    rw [v.map_mul, v.map_pow, W.v_l, nsmul_one, hx, ← WithTop.coe_natCast, ← WithTop.coe_add,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    linarith

theorem coreH_sol_bound (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (hπΔ : W.π₀ ∈ W.AΔ)
    (h1 : ∀ (r : ℕ) (x : W.DD T), InNΔi W T i x → ∃ x', InNΔi W T i x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x =
        (u₁ W ^ r - 1) • (W.π₀ ^ r • x) + W.π₀ ^ (r + 1) • x')
    (h2 : ∀ r : ℕ, 1 ≤ r →
      v (algebraMap O LL (u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ))
    (hO1 : ∀ y : O, 0 ≤ v (algebraMap O LL y))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    {d : ℕ} (b : Fin d → W.DD T) (hb : IsFrameΔ W T i b) (z : W.DD T) (c : ℕ → Fin d → LL)
    (hc : IsSol W T i b z c) (hc0 : ∀ m, 0 ≤ v (c 0 m)) : ∀ r m, Bd W r (c r m) := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have h' := W.v_l
    rw [h, v.map_zero] at h'
    exact absurd h' (by simp)
  have hpk : ∀ k : ℕ, 0 ≤ v ((PD.p : LL) ^ k) := fun k => by
    have := hO1 ((PD.p : O) ^ k)
    simpa using this
  have hup : ∀ (k k' : ℕ) (x : LL), k ≤ k' → 0 ≤ v ((PD.p : LL) ^ k * x) →
      0 ≤ v ((PD.p : LL) ^ k' * x) := by
    intro k k' x hk h0
    have e : (PD.p : LL) ^ k' * x = (PD.p : LL) ^ (k' - k) * ((PD.p : LL) ^ k * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    rw [e, v.map_mul]
    exact add_nonneg (hpk _) h0
  suffices H : ∀ r m, 0 ≤ v ((PD.p : LL) ^ Formalism.RepresentationBoundsCohomology.N2.aH PD.p r * c r m) from
    fun r m => (frame_bd_iff W r _).2 (H r m)
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero =>
      intro m
      simpa [Formalism.RepresentationBoundsCohomology.N2.aH] using hc0 m
    | succ s =>
      intro m₀
      set a := Formalism.RepresentationBoundsCohomology.N2.aH PD.p s with ha
      have hlow : ∀ j m, ∃ y : O, j < s + 1 → algebraMap O LL y = (PD.p : LL) ^ a * c j m := by
        intro j m
        by_cases hj : j < s + 1
        · obtain ⟨y, hy⟩ := hO2 ((PD.p : LL) ^ a * c j m)
            (hup _ _ _ (frame_aH_mono PD.p (Nat.lt_succ_iff.1 hj)) (ih j hj m))
          exact ⟨y, fun _ => hy⟩
        · exact ⟨0, fun h => absurd h hj⟩
      choose y' hy' using hlow
      choose km hkm using fun m => frame_exists_k W (c (s + 1) m)
      set K := a + ∑ m, km m with hK
      have haK : a ≤ K := Nat.le_add_right _ _
      have htop : ∀ m, ∃ y : O, algebraMap O LL y = (PD.p : LL) ^ K * c (s + 1) m := by
        intro m
        refine hO2 _ (hup _ _ _ ?_ (hkm m))
        exact le_trans (Finset.single_le_sum (f := km) (fun _ _ => Nat.zero_le _) (Finset.mem_univ m))
          (Nat.le_add_left _ _)
      choose yt hyt using htop
      let y : ℕ → Fin d → O := fun j m => if j < s + 1 then (PD.p : O) ^ (K - a) * y' j m else yt m
      have hy : ∀ j < s + 1 + 1, ∀ m, algebraMap O LL (y j m) = (PD.p : LL) ^ K * c j m := by
        intro j hj m
        by_cases hj' : j < s + 1
        · simp only [y, if_pos hj', map_mul, map_pow, map_natCast, hy' j m hj']
          rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel haK]
        · obtain rfl : j = s + 1 := by omega
          simp only [y, if_neg hj']
          exact hyt m
      obtain ⟨x₁, hx₁, e₁⟩ := hc (s + 1 + 1) K y hy
      obtain ⟨x₀, hx₀, e₀⟩ := hc (s + 1) a y' (fun j hj m => hy' j m hj)
      set S₀ := ∑ r ∈ Finset.range (s + 1), W.π₀ ^ r • vecB W T b (y' r) with hS₀
      have hS : ∑ r ∈ Finset.range (s + 1), W.π₀ ^ r • vecB W T b (y r) =
          ((PD.p : ℕ) : O) ^ (K - a) • S₀ := by
        rw [hS₀, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hyj : y j = fun m => ((PD.p : ℕ) : O) ^ (K - a) * y' j m := by
          funext m
          simp only [y, if_pos (Finset.mem_range.1 hj)]
        rw [hyj, frame_vecB_smul, smul_comm]
      have hyt' : y (s + 1) = yt := by
        funext m
        simp only [y, if_neg (lt_irrefl _)]
      rw [Finset.sum_range_succ, hS, hyt'] at e₁
      obtain ⟨x₂, hx₂, e₂⟩ := h1 (s + 1) (vecB W T b yt) (frame_vecB_mem W T i b hb yt)
      have hKa : ((PD.p : ℕ) : O) ^ K = ((PD.p : ℕ) : O) ^ (K - a) * ((PD.p : ℕ) : O) ^ a := by
        rw [← pow_add, Nat.sub_add_cancel haK]
      have E : ((PD.p : ℕ) : O) ^ (K - a) • (W.π₀ ^ (s + 1) • x₀) +
          ((u₁ W ^ (s + 1) - 1) • (W.π₀ ^ (s + 1) • vecB W T b yt) + W.π₀ ^ (s + 1 + 1) • x₂) =
          W.π₀ ^ (s + 1 + 1) • x₁ := by
        rw [← e₁, ← e₀, ← e₂, map_add, LinearMap.map_smul (W.γ T) (((PD.p : ℕ) : O) ^ (K - a)) S₀, hKa,
          mul_smul, smul_sub, smul_sub]
        abel
      have heq : (u₁ W ^ (s + 1) - 1) • vecB W T b yt + ((PD.p : ℕ) : O) ^ (K - a) • x₀ =
          W.π₀ • (x₁ - x₂) := by
        refine sub_eq_zero.1 (frame_π₀_inj W T hw (s + 1) _ ?_)
        rw [smul_sub, smul_add, smul_comm (W.π₀ ^ (s + 1)) (u₁ W ^ (s + 1) - 1),
          smul_comm (W.π₀ ^ (s + 1)) (((PD.p : ℕ) : O) ^ (K - a)), smul_smul (W.π₀ ^ (s + 1)) W.π₀,
          ← pow_succ, smul_sub, ← E]
        abel
      obtain ⟨e, he⟩ := frame_red W T i hw hπΔ b hb yt _ _ x₀ (x₁ - x₂) hx₀
        ⟨(W.NΔ T).sub_mem hx₁.1 hx₂.1, (W.Nl T i).sub_mem hx₁.2 hx₂.2⟩ heq
      have h3 := congrArg (algebraMap O LL) (he m₀)
      rw [map_add, map_mul, map_mul, hyt m₀, map_pow, map_natCast, map_zero] at h3
      set U := algebraMap O LL (u₁ W ^ (s + 1) - 1) with hU
      have h4 : (PD.p : LL) ^ a * U * c (s + 1) m₀ = -algebraMap O LL (e m₀) := by
        have h5 : (PD.p : LL) ^ (K - a) *
            ((PD.p : LL) ^ a * U * c (s + 1) m₀ + algebraMap O LL (e m₀)) = 0 := by
          have h6 : (PD.p : LL) ^ K = (PD.p : LL) ^ (K - a) * (PD.p : LL) ^ a := by
            rw [← pow_add, Nat.sub_add_cancel haK]
          rw [h6] at h3
          linear_combination h3
        rcases mul_eq_zero.1 h5 with h7 | h7
        · exact absurd h7 (pow_ne_zero _ hp0)
        · exact eq_neg_of_add_eq_zero_left h7
      have h8 : v ((PD.p : LL) ^ Formalism.RepresentationBoundsCohomology.N2.aH PD.p (s + 1) * c (s + 1) m₀) =
          v ((PD.p : LL) ^ a * U * c (s + 1) m₀) := by
        rw [frame_aH_succ, pow_add, v.map_mul, v.map_mul, v.map_mul, v.map_mul, hU,
          h2 (s + 1) (Nat.succ_le_succ (Nat.zero_le _)),
          v.map_pow (PD.p : LL) (1 + padicValNat PD.p (s + 1)), W.v_l, nsmul_one]
      rw [h8, h4, v.map_neg]
      exact hO1 _

end FrameS

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section FrameA

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def coreHex (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (d : ℕ) (b : Fin d → W.DD T),
    IsFrameΔ W T i b → ∀ z : W.DD T, (∃ z', InNΔi W T i z' ∧ z = W.π₀ • z') → ∀ c₀ : Fin d → O,
      ∃ c : ℕ → Fin d → LL, IsSol W T i b z c ∧ c 0 = fun m => algebraMap O LL (c₀ m)

theorem coreH_of_ex (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2 : CaseA W → coreHval W) (h4 : coreHleg PD.p)
    (hO1 : ∀ y : O, 0 ≤ v (algebraMap O LL y))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x) (hex : coreHex W) : coreH W :=
  coreH_of_parts W (fun hA T hT i => coreH_graded_of W h9 hA T hT i) h2
    (fun hA T hT i d b hb z hz c₀ => ⟨hex hA T hT i d b hb z hz c₀, fun c hc hc0 =>
      coreH_sol_bound W T i (frame_p9A W h9 hA T hT).1.2.2.1 (frame_p9A W h9 hA T hT).1.1
        (coreH_graded_of W h9 hA T hT i) (h2 hA) hO1 hO2 b hb z c hc
        (fun m => by rw [hc0]; exact hO1 _)⟩) h4

end FrameA

def GammaSubSolutionsExist (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    coreHex ((HW l).W K s LL h)

theorem gamma_equation_clause_of_solutions (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (hex : GammaSubSolutionsExist D HW F) : ConclusionH D HW F := fun l _ K s LL h =>
  coreH_of_ex _ (h9 l K s LL h) (fun hA => coreH_val_holds D HW F l K s LL h hA) (coreH_leg_holds D HW F l K)
    (fun y => ((D.loc l).v_O LL _).2 y.2)
    (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) (hex l K s LL h)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem gamma_sub_solutions_exist (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) : GammaSubSolutionsExist D HW F := fun l _ K s LL h hA T hT i _ b hb z hz c₀ =>
  coreH_sol_exists _ (fun y => ((D.loc l).v_O LL _).2 y.2)
    (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) (zl_O_inj LL)
    (uniformizer_ring_and_module_clauses _ (h9 l K s LL h) hA T hT).1 T (uniformizer_ring_and_module_clauses _ (h9 l K s LL h) hA T hT).2
    (coreH_val_holds D HW F l K s LL h hA) i b hb z hz c₀

theorem gamma_equation_clause_of_uniformizer (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) : ConclusionH D HW F := gamma_equation_clause_of_solutions D HW F h9 (gamma_sub_solutions_exist D HW F h9)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem arith_JSet_eq (jumps : Finset ℤ) (M : ℕ) : JSet jumps M = Formalism.RepresentationBoundsCohomology.N2.JSet jumps M := by
  unfold JSet Formalism.RepresentationBoundsCohomology.N2.JSet Formalism.RepresentationBoundsCohomology.N2.eigSet
  rw [Finset.filter_ne']

theorem arith_ePA_eq (l M H : ℕ) (jumps : Finset ℤ) :
    ePA l M H jumps =
      2 * Formalism.RepresentationBoundsCohomology.N2.eWA l H + Formalism.RepresentationBoundsCohomology.N2.eUA l M (Formalism.RepresentationBoundsCohomology.N2.JSet jumps M) := by
  unfold ePA
  rw [arith_JSet_eq]
  rfl

theorem arith_ePB_eq (l s M H : ℕ) (jumps : Finset ℤ) :
    ePB l s M H jumps =
      2 * Formalism.RepresentationBoundsCohomology.N2.eWB l H s + Formalism.RepresentationBoundsCohomology.N2.eUB l M s (Formalism.RepresentationBoundsCohomology.N2.JSet jumps M) := by
  unfold ePB
  rw [arith_JSet_eq]
  rfl

theorem arith_eWA_mono (l : ℕ) (hl : 2 ≤ l) {H H' : ℕ} (h : H ≤ H') : eWA l H ≤ eWA l H' := by
  unfold eWA
  apply Nat.floor_mono
  have hl' : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hH : (H : ℝ) ≤ (H' : ℝ) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have h1 : (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 ≤ (H' : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hH (by positivity)
  have h2 : Real.logb l ((H : ℝ) + 1) ≤ Real.logb l ((H' : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl' (by linarith) (by linarith)
  linarith

theorem arith_val_fact_mono (l : ℕ) [Fact l.Prime] {a b : ℕ} (h : a ≤ b) :
    padicValNat l a.factorial ≤ padicValNat l b.factorial := by
  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero b)).1
    (dvd_trans pow_padicValNat_dvd (Nat.factorial_dvd_factorial h))

theorem arith_eWB_mono (l : ℕ) [Fact l.Prime] (s : ℕ) {H H' : ℕ} (h : H ≤ H') :
    eWB l s H ≤ eWB l s H' := by
  unfold eWB
  have h1 : 2 * H * s ≤ 2 * H' * s := Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 h)
  have h2 := arith_val_fact_mono l (Nat.mul_le_mul_left 2 h)
  omega

theorem arith_sizeA (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (M h H : ℕ) (jumps : Finset ℤ)
    (hM : M ≤ H) (hh : h ≤ H) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    (ePA l M H jumps : ℝ) ≤ 23 * (1 + (H : ℝ) / l + (1 + Real.logb l ((H : ℝ) + 1))) := by
  have hp : l.Prime := Fact.out
  have hl3 : 3 ≤ l := by
    have := hp.two_le
    omega
  have hl3' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl3
  have hS := Formalism.RepresentationBoundsCohomology.N2.lifting_size_bounds_all.2.2.2.2.2 l hl M h (2 * H) jumps (by omega) hj
  have hmono : eWA l H ≤ eWA l (2 * H) := arith_eWA_mono l hp.two_le (by omega)
  have hle : ePA l M H jumps ≤
      2 * Formalism.RepresentationBoundsCohomology.N2.eWA l (2 * H) + Formalism.RepresentationBoundsCohomology.N2.eUA l M (Formalism.RepresentationBoundsCohomology.N2.JSet jumps M) := by
    rw [arith_ePA_eq]
    have : Formalism.RepresentationBoundsCohomology.N2.eWA l H ≤ Formalism.RepresentationBoundsCohomology.N2.eWA l (2 * H) := hmono
    omega
  have hle' : (ePA l M H jumps : ℝ) ≤
      ((2 * Formalism.RepresentationBoundsCohomology.N2.eWA l (2 * H) + Formalism.RepresentationBoundsCohomology.N2.eUA l M (Formalism.RepresentationBoundsCohomology.N2.JSet jumps M) : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hcast : ((2 * H : ℕ) : ℝ) = 2 * (H : ℝ) := by push_cast; ring
  rw [hcast] at hS

  have h1 : 15 / 2 * (2 * (H : ℝ)) / ((l : ℝ) - 1) ≤ 45 / 2 * ((H : ℝ) / l) := by
    rw [div_le_iff₀ (by linarith)]
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    have : 45 / 2 * ((H : ℝ) / l) * ((l : ℝ) - 1) = 45 / 2 * (H : ℝ) - 45 / 2 * ((H : ℝ) / l) := by
      field_simp
    rw [this]
    have h3 : (H : ℝ) / l ≤ (H : ℝ) / 3 := div_le_div_of_nonneg_left hH0 (by norm_num) hl3'
    linarith

  have h2 : Real.logb l (2 * (H : ℝ) + 1) ≤ 1 + Real.logb l ((H : ℝ) + 1) := by
    have hl1 : (1 : ℝ) < (l : ℝ) := by linarith
    have hprod : Real.logb l ((l : ℝ) * ((H : ℝ) + 1)) = 1 + Real.logb l ((H : ℝ) + 1) := by
      rw [Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one hl1]
    rw [← hprod]
    apply Real.logb_le_logb_of_le hl1 (by linarith)
    nlinarith
  have h4 : 0 ≤ Real.logb l ((H : ℝ) + 1) :=
    Real.logb_nonneg (by linarith) (by linarith)
  have h5 : 0 ≤ (H : ℝ) / l := by positivity
  linarith

theorem arith_sizeB (l : ℕ) [Fact l.Prime] (s M h H : ℕ) (jumps : Finset ℤ) (hs : 1 ≤ s)
    (hM : M ≤ H) (hh : h ≤ H) (hj : ∀ a ∈ jumps, -(M : ℤ) ≤ a ∧ a ≤ h) :
    ePB l s M H jumps ≤ 32 * H * s := by
  have hS := Formalism.RepresentationBoundsCohomology.N2.lifting_size_bounds_all.2.2.2.2.1 l M h (2 * H) s jumps hs (by omega) hj
  have hmono : eWB l s H ≤ eWB l s (2 * H) := arith_eWB_mono l s (by omega)
  rw [arith_ePB_eq]
  have h1 : Formalism.RepresentationBoundsCohomology.N2.eWB l H s ≤ Formalism.RepresentationBoundsCohomology.N2.eWB l (2 * H) s := hmono
  have h2 : 16 * (2 * H) * s = 32 * H * s := by ring
  omega

theorem arith_Mmax_le_left (n : ℕ) (Mi hi : ZMod n → ℕ) : Mmax n Mi ≤ Hmax n Mi hi := by
  unfold Mmax Hmax
  exact Finset.sup_mono_fun fun k _ => Nat.le_add_right _ _

theorem arith_Mmax_le_right (n : ℕ) (Mi hi : ZMod n → ℕ) : Mmax n hi ≤ Hmax n Mi hi := by
  unfold Mmax Hmax
  exact Finset.sup_mono_fun fun k _ => Nat.le_add_left _ _

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem arith_jumpSet_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M h : ℕ) :
    ∀ a ∈ jumpSet W T M h, -(M : ℤ) ≤ a ∧ a ≤ h := by
  intro a ha
  classical
  unfold jumpSet at ha
  exact Finset.mem_Icc.1 (Finset.mem_filter.1 ha).1

theorem coreLiftO_holds (W : LocWach PD LL O v n) : coreLiftO W 23 32 32 := by
  intro T₁ Mi hi _ _
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hM := arith_Mmax_le_left n Mi hi
  have hh := arith_Mmax_le_right n Mi hi
  have hj := arith_jumpSet_mem W T₁ (Mmax n Mi) (Mmax n hi)
  have hB := arith_sizeB PD.p W.s (Mmax n Mi) (Mmax n hi) (Hmax n Mi hi) _ W.s_pos hM hh hj
  have hB' : (ePB PD.p W.s (Mmax n Mi) (Hmax n Mi hi) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) : ℝ) ≤
      32 * (Hmax n Mi hi : ℝ) * W.s := by exact_mod_cast hB
  refine ⟨fun hA => ?_, fun _ => ?_, fun _ hs => ?_⟩
  · exact arith_sizeA PD.p hA.2.2 _ _ _ _ hM hh hj
  · linarith
  · have h1 : ((W.s : ℕ) : ℝ) = 1 := by rw [hs]; norm_num
    rw [h1, mul_one] at hB'
    exact hB'

end Local

theorem lifting_exponent_shapes (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : LiftExponentShapes D HW F 23 32 32 :=
  fun l _ K s LL h => coreLiftO_holds ((HW l).W K s LL h)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LagLocal

theorem lag_v_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {ι : Type} (S : Finset ι)
    (f : ι → F) : v (∏ b ∈ S, f b) = ∑ b ∈ S, v (f b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert b S hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, v.map_mul, ih]

theorem lag_deriv_eval {O : Type} [CommRing O] (S : Finset ℤ) (c : ℤ → O) (a : ℤ) (ha : a ∈ S) :
    (Polynomial.derivative (∏ b ∈ S, (Polynomial.X - Polynomial.C (c b)))).eval (c a) =
      ∏ b ∈ S.erase a, (c a - c b) := by
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum, Finset.sum_eq_single a]
  · simp [Polynomial.eval_prod]
  · intro i _ hia
    rw [Polynomial.eval_mul, Polynomial.eval_prod,
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hia, ha⟩) (by simp), zero_mul]
  · intro h; exact absurd ha h

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lag_coreL (W : LocWach PD LL O v n) [IsDomain O]
    (hA : ∀ (x : O) (k : ℕ), v (algebraMap O LL x) = ((k : ℕ) : WithTop ℚ) →
      Associated x (((PD.p : ℕ) : O) ^ k)) : coreL W := by
  intro S₁ S₂ sg c hdis hv E hE
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hcore := Formalism.RepresentationBoundsCohomology.N2.lagrange_and_w_all.1 PD.p O S₁ S₂ c sg hdis
    (fun a ha b hb hab => hA _ _ (hv a ha b hb hab))
  have hle : Formalism.RepresentationBoundsCohomology.N2.lagE PD.p sg S₁ S₂ ≤ E := by
    unfold Formalism.RepresentationBoundsCohomology.N2.lagE
    apply Finset.sup_le
    intro a ha
    have h := hE a ha
    rw [lag_deriv_eval S₁ c a ha, Polynomial.eval_prod, map_prod (algebraMap O LL),
      map_prod (algebraMap O LL), lag_v_prod, lag_v_prod] at h
    have h2 : ∀ b ∈ S₂, v (algebraMap O LL
        ((Polynomial.X - Polynomial.C (c b)).eval (c a))) =
        ((sg + padicValInt PD.p (a - b) : ℕ) : WithTop ℚ) := by
      intro b hb
      have hab : a ≠ b := fun e => (Finset.disjoint_left.1 hdis ha) (e ▸ hb)
      simpa using hv a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb) hab
    have h1 : ∀ b ∈ S₁.erase a, v (algebraMap O LL (c a - c b)) =
        ((sg + padicValInt PD.p (a - b) : ℕ) : WithTop ℚ) := by
      intro b hb
      exact hv a (Finset.mem_union_left _ ha) b
        (Finset.mem_union_left _ (Finset.mem_of_mem_erase hb)) (Finset.ne_of_mem_erase hb).symm
    rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h1, ← Nat.cast_sum, ← Nat.cast_sum,
      ← Nat.cast_add] at h
    rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_le_coe] at h
    exact_mod_cast h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, Polynomial.C_mul]
  exact Ideal.mul_mem_left _ _ hcore

end LagLocal

theorem lattice_clause_every_situation (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : ConclusionL D HW F := by
  intro l _ K s LL h
  refine lag_coreL _ ?_
  intro x k hx
  rw [(D.loc l).PD_p K]
  exact assoc_of_v (D.loc l) LL x k hx

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section DescGen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')

abbrev descCls (L' : Lattice (O := O) ρ') : ↥(latticeCocycles L') →ₗ[O] LatticeCohomology L' := Submodule.mkQ _

theorem desc_mem_H1fT_iff (x : LatticeCohomology L') :
    x ∈ latticeFiniteCohomology PD L' ↔ ∃ c : ↥(latticeCocycles L'), (c : G → V') ∈ latticeFiniteCocycles PD L' ∧ descCls L' c = x := by
  unfold latticeFiniteCohomology
  rw [Submodule.mem_map]
  rfl

theorem desc_cls_eq_zero (c : ↥(latticeCocycles L')) : descCls L' c = 0 ↔ (c : G → V') ∈ latticeCoboundaries L' := by
  unfold descCls
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

theorem desc_H1map_cls (c : ↥(latticeCocycles L)) :
    F.H1map (descCls L c) = descCls L' ⟨F.post c, F.post_Z1T c c.2⟩ := rfl

theorem desc_mem_ImF_of_cls (p : ↥(latticeCocycles L')) (h : descCls L' p ∈ (latticeFiniteCohomology PD L).map F.H1map) :
    (p : G → V') ∈ F.ImF PD := by
  obtain ⟨x, hx, hxp⟩ := h
  obtain ⟨c, hc, rfl⟩ := (desc_mem_H1fT_iff PD x).1 hx
  rw [desc_H1map_cls] at hxp
  have h0 : descCls L' (p - ⟨F.post c, F.post_Z1T c c.2⟩) = 0 := by rw [map_sub, hxp, sub_self]
  have h1 := (desc_cls_eq_zero _).1 h0
  have h2 : (p : G → V') = F.post c + ((p - ⟨F.post c, F.post_Z1T c c.2⟩ : ↥(latticeCocycles L')) : G → V') := by
    simp
  rw [h2]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc) h1

theorem desc_cls_mem_of_ImF (p : ↥(latticeCocycles L')) (h : (p : G → V') ∈ F.ImF PD) :
    descCls L' p ∈ (latticeFiniteCohomology PD L).map F.H1map := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
  obtain ⟨c, hc, rfl⟩ := ha
  have hcZ : c ∈ latticeCocycles L := hc.1
  refine ⟨descCls L ⟨c, hcZ⟩, (desc_mem_H1fT_iff PD _).2 ⟨⟨c, hcZ⟩, hc, rfl⟩, ?_⟩
  rw [desc_H1map_cls]
  have h0 : descCls L' (p - ⟨F.post c, F.post_Z1T c hcZ⟩) = 0 := by
    rw [desc_cls_eq_zero]
    have : ((p - ⟨F.post c, F.post_Z1T c hcZ⟩ : ↥(latticeCocycles L')) : G → V') = b := by
      simp [← hab]
    rw [this]; exact hb
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm

theorem desc_LiftF_iff (e : ℕ) :
    F.LiftF PD e ↔ ∀ κ ∈ latticeFiniteCohomology PD L', ∃ κ₁ ∈ latticeFiniteCohomology PD L, F.H1map κ₁ = ((PD.p : O) ^ e) • κ := by
  constructor
  · intro h κ hκ
    obtain ⟨c, hc, rfl⟩ := (desc_mem_H1fT_iff PD κ).1 hκ
    have h1 := desc_cls_mem_of_ImF PD F (((PD.p : O) ^ e) • c) (h c hc)
    obtain ⟨κ₁, hκ₁, h2⟩ := h1
    exact ⟨κ₁, hκ₁, by rw [h2, map_smul]⟩
  · intro h c hc
    have hcZ : c ∈ latticeCocycles L' := hc.1
    obtain ⟨κ₁, hκ₁, h2⟩ := h (descCls L' ⟨c, hcZ⟩) ((desc_mem_H1fT_iff PD _).2 ⟨⟨c, hcZ⟩, hc, rfl⟩)
    have h3 : descCls L' (((PD.p : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles L'))) ∈ (latticeFiniteCohomology PD L).map F.H1map :=
      ⟨κ₁, hκ₁, by rw [h2, map_smul]⟩
    exact desc_mem_ImF_of_cls PD F _ h3

end DescGen

theorem desc_sub (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [Algebra ℤ_[ℓ] O]
    (H₁ H₂ H₁' H₂' : Type)
    [AddCommGroup H₁] [Module O H₁] [AddCommGroup H₂] [Module O H₂]
    [AddCommGroup H₁'] [Module O H₁'] [AddCommGroup H₂'] [Module O H₂']
    (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂) (Hf₁' : Submodule O H₁') (Hf₂' : Submodule O H₂')
    (h : H₁ →ₗ[O] H₂) (h' : H₁' →ₗ[O] H₂') (res₂ : H₂' →ₗ[O] H₂)
    (cor₁ : H₁ →ₗ[O] H₁') (cor₂ : H₂ →ₗ[O] H₂') (g E : ℕ) (hg : 0 < g)
    (hcr : ∀ x, cor₂ (res₂ x) = (g : O) • x)
    (hnat : ∀ x, h' (cor₁ x) = cor₂ (h x))
    (hres : ∀ x ∈ Hf₂', res₂ x ∈ Hf₂) (hcor : ∀ x ∈ Hf₁, cor₁ x ∈ Hf₁')
    (hE : ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁, h κ₁ = ((ℓ : O) ^ E) • κ) :
    ∀ κ' ∈ Hf₂', ∃ κ₁' ∈ Hf₁', h' κ₁' = ((ℓ : O) ^ (E + padicValNat ℓ g)) • κ' := by
  let _ : Module ℤ_[ℓ] H₁ := Module.compHom H₁ (algebraMap ℤ_[ℓ] O)
  let _ : Module ℤ_[ℓ] H₂ := Module.compHom H₂ (algebraMap ℤ_[ℓ] O)
  let _ : Module ℤ_[ℓ] H₁' := Module.compHom H₁' (algebraMap ℤ_[ℓ] O)
  let _ : Module ℤ_[ℓ] H₂' := Module.compHom H₂' (algebraMap ℤ_[ℓ] O)
  have _ : IsScalarTower ℤ_[ℓ] O H₁ := ⟨fun a b x => by
    change (a • b) • x = algebraMap ℤ_[ℓ] O a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower ℤ_[ℓ] O H₂ := ⟨fun a b x => by
    change (a • b) • x = algebraMap ℤ_[ℓ] O a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower ℤ_[ℓ] O H₁' := ⟨fun a b x => by
    change (a • b) • x = algebraMap ℤ_[ℓ] O a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  have _ : IsScalarTower ℤ_[ℓ] O H₂' := ⟨fun a b x => by
    change (a • b) • x = algebraMap ℤ_[ℓ] O a • b • x
    rw [Algebra.smul_def, mul_smul]⟩
  have key := Formalism.RepresentationBoundsCohomology.N2.lifting_theorem.2.2 ℓ H₁ H₂ H₁' H₂'
    (Hf₁.restrictScalars ℤ_[ℓ]) (Hf₂.restrictScalars ℤ_[ℓ]) (Hf₁'.restrictScalars ℤ_[ℓ])
    (Hf₂'.restrictScalars ℤ_[ℓ]) (h.restrictScalars ℤ_[ℓ]) (h'.restrictScalars ℤ_[ℓ])
    (res₂.restrictScalars ℤ_[ℓ]) (cor₁.restrictScalars ℤ_[ℓ]) (cor₂.restrictScalars ℤ_[ℓ]) g E hg
    (fun x => by
      change cor₂ (res₂ x) = algebraMap ℤ_[ℓ] O (g : ℤ_[ℓ]) • x
      rw [map_natCast]; exact hcr x)
    hnat hres hcor
    (fun κ hκ => by
      obtain ⟨κ₁, h1, h2⟩ := hE κ hκ
      refine ⟨κ₁, h1, ?_⟩
      change h κ₁ = algebraMap ℤ_[ℓ] O ((ℓ : ℤ_[ℓ]) ^ E) • κ
      rw [map_pow, map_natCast]; exact h2)
  intro κ' hκ'
  obtain ⟨κ₁', h1, h2⟩ := key κ' hκ'
  refine ⟨κ₁', h1, ?_⟩
  have h3 : h' κ₁' = algebraMap ℤ_[ℓ] O ((ℓ : ℤ_[ℓ]) ^ (E + padicValNat ℓ g)) • κ' := h2
  rw [map_pow, map_natCast] at h3
  exact h3

section DescCore

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem desc_LiftF (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (g : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]
    (hp : PD.p = ℓ) (hp' : PD'.p = ℓ) (hg : 0 < g) (hcor : coreCor PD PD' LL O ι hι g)
    {T₁ T₂ : LocLat G' Qp LL O} (F : LatHom T₁.L T₂.L) (E : ℕ)
    (hE : (resHom ι hι F).LiftF PD E) : F.LiftF PD' (E + padicValNat ℓ g) := by
  obtain ⟨hres, cor, hcr, hcf, hnat⟩ := hcor
  rw [desc_LiftF_iff] at hE ⊢
  rw [hp] at hE
  rw [hp']
  exact desc_sub ℓ O (LatticeCohomology (resLoc ι hι T₁).L) (LatticeCohomology (resLoc ι hι T₂).L) (LatticeCohomology T₁.L) (LatticeCohomology T₂.L)
    (latticeFiniteCohomology PD (resLoc ι hι T₁).L) (latticeFiniteCohomology PD (resLoc ι hι T₂).L) (latticeFiniteCohomology PD' T₁.L) (latticeFiniteCohomology PD' T₂.L)
    (resHom ι hι F).H1map F.H1map (resH1 ι hι T₂) (cor T₁) (cor T₂) g E hg
    (hcr T₂) (fun x => (hnat T₁ T₂ F x).symm) (hres T₂) (hcf T₁) hE

theorem coreDesc_of (W : LocWach PD LL O v n) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (g : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]
    (hp : PD.p = ℓ) (hp' : PD'.p = ℓ) (hg : 0 < g)
    (hA : coreLiftA W) (hB : coreLiftB W) (hcor : coreCor PD PD' LL O ι hι g) :
    coreDesc W PD' ι hι g := by
  intro _ T₁ T₂ F Mi hi hS hJ
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · have h1 := hA hc (resLoc ι hι T₁) (resLoc ι hι T₂) (resHom ι hι F) Mi hi hS hJ
    have h2 := desc_LiftF PD PD' ι hι g ℓ hp hp' hg hcor F _ h1
    rw [← hp] at h2
    exact h2
  · have h1 := hB hc (resLoc ι hι T₁) (resLoc ι hι T₂) (resHom ι hι F) Mi hi hS hJ
    have h2 := desc_LiftF PD PD' ι hι g ℓ hp hp' hg hcor F _ h1
    rw [← hp] at h2
    exact h2

end DescCore

section DescD

variable {l : ℕ} [Fact l.Prime]

theorem desc_g_pos (K K' : FinExt l) (hKK : K'.1 ≤ K.1) :
    0 < Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1 := by
  have := K.2
  have := K'.2
  exact Nat.div_pos (Nat.le_of_dvd Module.finrank_pos (IntermediateField.finrank_dvd_of_le_right hKK))
    Module.finrank_pos

theorem desc_val_g (K K' : FinExt l) (hKK : K'.1 ≤ K.1) (h0 : K0 K ≤ K'.1)
    (hd : Module.finrank ↥(K0 K) ↥K.1 = l - 1) :
    padicValNat l (Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1) = 0 := by
  have := K.2
  have := K'.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective (IntermediateField.inclusion h0).toLinearMap
      (IntermediateField.inclusion h0).injective
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨b', hb'⟩ := IntermediateField.finrank_dvd_of_le_right h0
  obtain ⟨g, hg⟩ := IntermediateField.finrank_dvd_of_le_right hKK
  have ha : 0 < Module.finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  have hb : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
  have hc : Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥(K0 K) ↥K.1 = Module.finrank ℚ_[l] ↥K.1 :=
    Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1
  rw [hg, Nat.mul_div_cancel_left _ hb]
  rw [hd, hg, hb', mul_assoc] at hc
  have h1 : l - 1 = b' * g := Nat.eq_of_mul_eq_mul_left ha hc
  apply padicValNat.eq_zero_of_not_dvd
  intro hdv
  have h2 : l ∣ l - 1 := h1 ▸ Dvd.dvd.mul_left hdv b'
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

end DescD

theorem lifting_descent_to_subfields (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hA : LiftTheoremCaseA D HW F) (hB : LiftTheoremCaseB D HW F) (h20 : adm20 D HW F) :
    LiftGaloisDescent D HW F := by
  intro l _ K K' hKK hle _ s LL h
  refine ⟨?_, fun hc hs h0 => ?_⟩
  · exact coreDesc_of ((HW l).W K s LL h) ((D.loc l).PD K') (Subgroup.inclusion hle) _ _ l
      ((D.loc l).PD_p K) ((D.loc l).PD_p K') (desc_g_pos K K' hKK) (hA l K s LL h) (hB l K s LL h)
      (h20 l K K' hKK hle LL)
  · apply desc_val_g K K' hKK h0
    have h1 := hc.2
    rw [(HW l).W_s K s LL h, hs, (D.loc l).PD_p K] at h1
    simpa using h1

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section TruncPart

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def UniformizerRingClause (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

theorem tr_Eat (W : LocWach PD LL O v n) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qp]

theorem tr_γA_mul (W : LocWach PD LL O v n) (g h : W.Gam) (a : LetA O n) :
    W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext i
  simp [LocWach.γA, letγ, map_mul]

theorem tr_γA_one (W : LocWach PD LL O v n) (a : LetA O n) : W.γA 1 a = a := by
  funext i
  simp [LocWach.γA, letγ]

theorem tr_γA_mem (W : LocWach PD LL O v n) (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) :
    W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [← tr_γA_mul, mul_comm, tr_γA_mul, ha δ hδ]

theorem tr_φA_mem (W : LocWach PD LL O v n) {a : LetA O n} (ha : a ∈ W.AΔ) :
    W.φA a ∈ W.AΔ := by
  intro δ hδ
  rw [← W.φA_γA, ha δ hδ]

def trφ (W : LocWach PD LL O v n) : ↥W.AΔ →ₐ[O] ↥W.AΔ :=
  (W.φA.comp W.AΔ.val).codRestrict W.AΔ fun a => tr_φA_mem W a.2

def trγ (W : LocWach PD LL O v n) : ↥W.AΔ →ₐ[O] ↥W.AΔ :=
  ((W.γA W.gam).comp W.AΔ.val).codRestrict W.AΔ fun a => tr_γA_mem W W.gam a.2

theorem tr_cancel [IsDomain O] {x a b : LetA O n} (hx : ∀ i, x i ≠ 0) (h : a * x = b * x) : a = b := by
  funext i
  exact mul_right_cancel₀ (hx i) (congrFun h i)

theorem tr_quot_mem [IsDomain O] (W : LocWach PD LL O v n) {x y w : LetA O n} (hx : x ∈ W.AΔ)
    (hx0 : ∀ i, x i ≠ 0) (hy : y ∈ W.AΔ) (h : y = w * x) : w ∈ W.AΔ := by
  intro δ hδ
  apply tr_cancel hx0
  have := congrArg (W.γA δ) h
  rw [map_mul, hy δ hδ, hx δ hδ] at this
  rw [← this, h]

theorem tr_unit_ne [Nontrivial O] (w : (LetA O n)ˣ) (i : ZMod n) : (w : LetA O n) i ≠ 0 := by
  intro h
  have := congrFun w.mul_inv i
  rw [Pi.mul_apply, h, zero_mul] at this
  exact zero_ne_one this

theorem tr_unit_AΔ [IsDomain O] (W : LocWach PD LL O v n) (w : (LetA O n)ˣ)
    (hw : (w : LetA O n) ∈ W.AΔ) : IsUnit (⟨(w : LetA O n), hw⟩ : ↥W.AΔ) := by
  have hinv : ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ∈ W.AΔ :=
    tr_quot_mem W hw (tr_unit_ne w) W.AΔ.one_mem (by simp)
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp)⟩

theorem tr_p_ne (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 : ((PD.p : ℕ) : LL) = 0 := by
    have := congrArg (algebraMap O LL) h
    simpa using this
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

theorem tr_π₀_const (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (i : ZMod n) :
    PowerSeries.constantCoeff (W.π₀ i) = 0 := by
  obtain ⟨w, hw⟩ := h9.2.2.1
  have hp : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  rw [hw]
  obtain ⟨k, hk⟩ : ∃ k, PD.p - 1 = k + 1 := ⟨PD.p - 2, by omega⟩
  simp [letπ, hk, pow_succ]

theorem tr_π₀_ne [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (i : ZMod n) : W.π₀ i ≠ 0 := by
  obtain ⟨w, hw⟩ := h9.2.2.1
  rw [hw, Pi.mul_apply]
  exact mul_ne_zero (tr_unit_ne w i) (by simp [letπ, PowerSeries.X_ne_zero])

theorem tr_qp_ne (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (i : ZMod n) : qp W i ≠ 0 := by
  intro h
  have := congrArg PowerSeries.constantCoeff h
  simp only [qp, Pi.add_apply, map_add, tr_π₀_const W h9 i, zero_add, map_zero] at this
  apply tr_p_ne W
  simpa using this

theorem tr_const_γ (W : LocWach PD LL O v n) (g : W.Gam) (c : ZMod n → O) :
    W.γA g (fun i => PowerSeries.C (c i)) = fun i => PowerSeries.C (c i) := by
  funext i
  have h : (PowerSeries.C (c i) : PowerSeries O) = algebraMap O (PowerSeries O) (c i) := rfl
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  rw [h, AlgHom.commutes]

theorem tr_split [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) {a : LetA O n}
    (ha : a ∈ W.AΔ) :
    ∃ (c : ZMod n → O) (b : LetA O n), b ∈ W.AΔ ∧ a = (fun i => PowerSeries.C (c i)) + b * W.π₀ := by
  obtain ⟨f, hf, -⟩ := h9.2.1 a ha
  have hs : ∀ i, PowerSeries.HasSubst (W.π₀ i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (tr_π₀_const W h9 i)
  let g : ZMod n → PowerSeries O := fun i => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (f i)
  have hab : a = (fun i => PowerSeries.C (PowerSeries.constantCoeff (f i))) +
      (fun i => PowerSeries.subst (W.π₀ i) (g i)) * W.π₀ := by
    funext i
    have h : (PowerSeries.C (PowerSeries.constantCoeff (f i)) : PowerSeries O) =
        algebraMap O (PowerSeries O) (PowerSeries.constantCoeff (f i)) := rfl
    rw [hf i, Pi.add_apply, Pi.mul_apply]
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (f i)]
    rw [← PowerSeries.coe_substAlgHom (hs i), map_add, map_mul, PowerSeries.substAlgHom_X, h,
      AlgHom.commutes]
    ring
  refine ⟨_, _, ?_, hab⟩
  refine tr_quot_mem W (x := W.π₀) (y := a - fun i => PowerSeries.C (PowerSeries.constantCoeff (f i)))
    h9.1 (tr_π₀_ne W h9) ?_ ?_
  · exact W.AΔ.sub_mem ha fun δ _ => tr_const_γ W δ _
  · conv_lhs => rw [hab]
    ring

theorem tr_exists_base [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) :
    ∃ Bs : Formalism.WachCohomologyFacts.Base O ↥W.AΔ, Bs.ℓ = PD.p ∧ (Bs.X : LetA O n) = W.π₀ ∧ Bs.φ = trφ W := by
  have hπ : W.π₀ ∈ W.AΔ := h9.1
  obtain ⟨wφ, hwφ⟩ := h9.2.2.2.2.2.1
  obtain ⟨wγ, hwγ⟩ := h9.2.2.2.2.2.2.1
  rw [tr_Eat] at hwφ hwγ
  have hq : qp W ∈ W.AΔ := W.AΔ.add_mem hπ (natCast_mem _ _)
  have hwφm : (wφ : LetA O n) ∈ W.AΔ :=
    tr_quot_mem W (x := W.π₀ * qp W ^ (PD.p - 1)) (y := W.φA W.π₀)
      (W.AΔ.mul_mem hπ (W.AΔ.pow_mem hq _))
      (fun i => mul_ne_zero (tr_π₀_ne W h9 i) (pow_ne_zero _ (tr_qp_ne W h9 i)))
      (tr_φA_mem W hπ) (by rw [hwφ, mul_assoc])
  have hwγm : (wγ : LetA O n) ∈ W.AΔ :=
    tr_quot_mem W (x := W.π₀ * qp W) (y := W.γA W.gam W.π₀ - W.π₀)
      (W.AΔ.mul_mem hπ hq)
      (fun i => mul_ne_zero (tr_π₀_ne W h9 i) (tr_qp_ne W h9 i))
      (W.AΔ.sub_mem (tr_γA_mem W _ hπ) hπ) (by rw [hwγ, mul_assoc])
  refine ⟨{ ℓ := PD.p, hℓ := PD.hp, X := ⟨W.π₀, hπ⟩, u := ⟨wφ, hwφm⟩, c := ⟨wγ, hwγm⟩,
            φ := trφ W, γ := trγ W, hu := tr_unit_AΔ W wφ hwφm, hc := tr_unit_AΔ W wγ hwγm,
            comm := ?_, γ_bij := ⟨?_, ?_⟩, hφX := ?_, hγX := ?_, γ_modX := ?_ }, rfl, rfl, rfl⟩
  · intro a
    exact Subtype.ext (W.φA_γA W.gam a)
  · intro a b hab
    have h1 : W.γA W.gam a = W.γA W.gam b := congrArg Subtype.val hab
    have h2 := congrArg (W.γA W.gam⁻¹) h1
    rw [← tr_γA_mul, ← tr_γA_mul, inv_mul_cancel, tr_γA_one, tr_γA_one] at h2
    exact Subtype.ext h2
  · intro a
    refine ⟨⟨W.γA W.gam⁻¹ a, tr_γA_mem W _ a.2⟩, Subtype.ext ?_⟩
    change W.γA W.gam (W.γA W.gam⁻¹ a) = a
    rw [← tr_γA_mul, mul_inv_cancel, tr_γA_one]
  · apply Subtype.ext
    change W.φA W.π₀ = _
    rw [hwφ]
    simp [qp]
  · apply Subtype.ext
    change W.γA W.gam W.π₀ - W.π₀ = _
    rw [hwγ]
    simp [qp]
  · intro a
    obtain ⟨c, b, hb, hab⟩ := tr_split W h9 a.2
    have hγπ : W.γA W.gam W.π₀ = W.π₀ + wγ * W.π₀ * qp W := by rw [← hwγ]; ring
    refine Ideal.mem_span_singleton'.2
      ⟨⟨(1 + wγ * qp W) * W.γA W.gam b - b, W.AΔ.sub_mem (W.AΔ.mul_mem
        (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hwγm hq)) (tr_γA_mem W _ hb)) hb⟩, Subtype.ext ?_⟩
    change ((1 + wγ * qp W) * W.γA W.gam b - b) * W.π₀ = W.γA W.gam a - a
    rw [hab, map_add, map_mul, tr_const_γ, hγπ]
    ring

theorem tr_iter (W : LocWach PD LL O v n) (a : ↥W.AΔ) (k : ℕ) :
    (((⇑(trφ W))^[k] a : ↥W.AΔ) : LetA O n) = (W.φA ^ k) (a : LetA O n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply, ← ih]
    rfl

theorem tr_base_spec [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) :
    ∃ (X : ↥W.AΔ) (p : ℕ → ↥W.AΔ), (X : LetA O n) = W.π₀ ∧ (∀ s, (p s : LetA O n) = pk W s) ∧
      (∀ s, p s ∈ Ideal.span {((PD.p : ℕ) : ↥W.AΔ), X ^ (PD.p ^ s)}) ∧
      ∀ j, ∃ u u' : ↥W.AΔ, u * u' = 1 ∧
        (W.φA ^ j) W.π₀ = ((u * X * ∏ s ∈ Finset.range j, p s ^ (PD.p - 1) : ↥W.AΔ) : LetA O n) := by
  obtain ⟨Bs, hl, hX, hφ⟩ := tr_exists_base W h9
  refine ⟨Bs.X, Bs.p, hX, ?_, ?_, ?_⟩
  · intro s
    unfold Formalism.WachCohomologyFacts.Base.p Formalism.WachCohomologyFacts.Base.q
    rw [hφ, tr_iter]
    simp [pk, qp, hX, hl]
  · intro s
    have h := Formalism.NOK.psIdeal_proof O ↥W.AΔ Bs s
    rwa [hl] at h
  · intro j
    obtain ⟨u, hu, huj⟩ := Formalism.NOK.phiIterX_proof O ↥W.AΔ Bs j
    obtain ⟨u', hu'⟩ := isUnit_iff_exists_inv.1 hu
    refine ⟨u, u', hu', ?_⟩
    rw [hl, hφ] at huj
    rw [← huj, tr_iter, hX]

theorem frobenius_factor_mem_ideal [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (k : ℕ) :
    ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      pk W k = ((PD.p : ℕ) : LetA O n) * a + W.π₀ ^ (PD.p ^ k) * b := by
  obtain ⟨X, p, hX, hp, hI, -⟩ := tr_base_spec W h9
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (hI k)
  refine ⟨a, a.2, b, b.2, ?_⟩
  rw [← hp k, ← hab, ← hX]
  push_cast
  ring

theorem frobenius_pow_uniformizer_factorisation [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (j r : ℕ) :
    ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, pk W k ^ ((PD.p - 1) * r) := by
  obtain ⟨X, p, hX, hp, -, hJ⟩ := tr_base_spec W h9
  obtain ⟨u, u', huu, hj⟩ := hJ j
  refine ⟨(u ^ r : ↥W.AΔ), (u ^ r : ↥W.AΔ).2, (u' ^ r : ↥W.AΔ), (u' ^ r : ↥W.AΔ).2, ?_, ?_⟩
  · rw [← Subalgebra.coe_mul, ← mul_pow, huu, one_pow, Subalgebra.coe_one]
  · rw [hj]
    push_cast
    rw [hX, mul_pow, mul_pow, ← Finset.prod_pow]
    simp only [hp, pow_mul]

theorem tr_trunc_int [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W) (h2 : PD.p ≠ 2)
    (j y M' r : ℕ) (hj : 1 ≤ j) :
    ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p y M' j * ((W.φA ^ j) W.π₀) ^ r =
        a * ((PD.p : ℕ) : LetA O n) ^ ⌈(r : ℝ) * PD.p / ((PD.p : ℝ) - 1)⌉₊ + b * JJ W j y M' := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have h3 : 3 ≤ PD.p := by have := PD.hp.two_le; omega
  obtain ⟨X, p, hX, hp, hI, hJ⟩ := tr_base_spec W h9
  obtain ⟨u, u', -, hj'⟩ := hJ j
  have h := Formalism.NOK.scaledPowMemSpanCeil ↥W.AΔ PD.p h3 X u p y M' j hj (hI (j - 1)) r
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h
  refine ⟨a, a.2, b, b.2, ?_⟩
  have h' := congrArg (Subtype.val) hab
  rw [hj']
  simp only [JJ, ← hX, ← hp]
  push_cast at h' ⊢
  exact h'.symm

theorem tr_vanish_int [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W)
    (j y M' r : ℕ) (h1 : M' ≤ r) (h2 : y ≤ (PD.p - 1) * r) :
    ∃ b ∈ W.AΔ, ((W.φA ^ j) W.π₀) ^ r = b * JJ W j y M' := by
  obtain ⟨X, p, hX, hp, -, hJ⟩ := tr_base_spec W h9
  obtain ⟨u, u', -, hj'⟩ := hJ j
  have h := Formalism.NOK.powMemSpanOfLe ↥W.AΔ PD.p X u p y M' j r h1 h2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine ⟨b, b.2, ?_⟩
  have h' := congrArg (Subtype.val) hb
  rw [hj']
  simp only [JJ, ← hX, ← hp]
  push_cast at h' ⊢
  exact h'.symm

theorem tr_toLL_smul (o : O) (a : LetA O n) :
    (toLL (o • a) : ZMod n → PowerSeries LL) = algebraMap O LL o • toLL a := by
  funext i
  ext k
  simp [toLL, Algebra.smul_def]

theorem tr_nat_smul (m k : ℕ) (x : ZMod n → PowerSeries LL) :
    ((m : ℕ) : ZMod n → PowerSeries LL) ^ k * x = ((m : LL) ^ k) • x := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem tr_toLL_ppow (m k : ℕ) (x : LetA O n) :
    (toLL (((m : ℕ) : LetA O n) ^ k * x) : ZMod n → PowerSeries LL) = ((m : LL) ^ k) • toLL x := by
  rw [map_mul, map_pow, map_natCast, tr_nat_smul]

theorem tr_v_pow (W : LocWach PD LL O v n) (k : ℕ) :
    v ((PD.p : LL) ^ k) = ((k : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_pow, W.v_l, nsmul_one]
  rfl

theorem tr_pLL_ne (W : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h1
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

theorem mem_valuation_ring_smul_invariant (W : LocWach PD LL O v n) (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (c : LL) (t : ℚ) (hc : v c = (t : WithTop ℚ)) {b : LetA O n} (hb : b ∈ W.AΔ) :
    InWachLocalised W (c • toLL b) := by
  have hk : 0 ≤ v (c * (PD.p : LL) ^ ⌈-t⌉₊) := by
    rw [AddValuation.map_mul, hc, tr_v_pow W, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have := Nat.le_ceil (-t)
    linarith
  obtain ⟨o, ho⟩ := hO _ hk
  refine ⟨⌈-t⌉₊, o • b, W.AΔ.smul_mem hb o, ?_⟩
  rw [tr_toLL_smul, ho, smul_smul]
  congr 1
  field_simp [tr_pLL_ne W]

theorem tr_sig_le (l j y M' : ℕ) (hl : 2 ≤ l) : (Formalism.NOK.sigNOK l y M' j : ℚ) ≤ sigT l j y M' := by
  have h0 : (0 : ℝ) ≤ ((y : ℝ) + (M' : ℝ) / (l : ℝ) ^ (j - 1)) * (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by
    positivity
  have h1 := Nat.floor_le h0
  have h2 : ((Formalism.NOK.sigNOK l y M' j : ℚ) : ℝ) ≤ ((sigT l j y M' : ℚ) : ℝ) := by
    unfold Formalism.NOK.sigNOK sigT
    push_cast
    linarith
  exact_mod_cast h2

theorem tr_ceil_ge (l r : ℕ) :
    (r : ℚ) * l / ((l : ℚ) - 1) ≤ (⌈(r : ℝ) * l / ((l : ℝ) - 1)⌉₊ : ℚ) := by
  have h := Nat.le_ceil ((r : ℝ) * l / ((l : ℝ) - 1))
  have h' : (((r : ℚ) * l / ((l : ℚ) - 1) : ℚ) : ℝ) ≤
      (((⌈(r : ℝ) * l / ((l : ℝ) - 1)⌉₊ : ℕ) : ℚ) : ℝ) := by
    push_cast
    exact h
  exact_mod_cast h'

theorem valuation_decomposition_frobenius_pow [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W)
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h2 : PD.p ≠ 2)
    (j y M' r : ℕ) (hj : 1 ≤ j) (c : LL)
    (hc : v c = (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ)) :
    ∃ x₁ x₂, InLA0 W (sigT PD.p j y M') x₁ ∧ InWachLocalised W x₂ ∧
      c • toLL (((W.φA ^ j) W.π₀) ^ r) = x₁ + toLL (JJ W j y M') * x₂ := by
  obtain ⟨a, ha, b, hb, hab⟩ := tr_trunc_int W h9 h2 j y M' r hj
  set σ := Formalism.NOK.sigNOK PD.p y M' j with hσ
  set e := ⌈(r : ℝ) * PD.p / ((PD.p : ℝ) - 1)⌉₊ with he
  have hp0 := tr_pLL_ne W
  rw [mul_comm a] at hab
  have hab' := congrArg (toLL (LL := LL)) hab
  rw [tr_toLL_ppow, map_add, tr_toLL_ppow, map_mul] at hab'
  have hcσ : v (c * ((PD.p : LL) ^ σ)⁻¹) + ((σ : ℚ) : WithTop ℚ) =
      (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ) := by
    rw [← tr_v_pow W, ← AddValuation.map_mul, ← hc]
    congr 1
    field_simp
  refine ⟨(c * ((PD.p : LL) ^ σ)⁻¹ * (PD.p : LL) ^ e) • toLL a, (c * ((PD.p : LL) ^ σ)⁻¹) • toLL b,
    ⟨_, a, ha, ?_, rfl⟩, ?_, ?_⟩
  · rw [AddValuation.map_mul, tr_v_pow W]
    rcases hx : v (c * ((PD.p : LL) ^ σ)⁻¹) with _ | x
    · exact le_top
    · rw [hx] at hcσ
      have h1 : x + (σ : ℚ) = -((r : ℚ) * PD.p / ((PD.p : ℚ) - 1)) := by
        have : ((x + (σ : ℚ) : ℚ) : WithTop ℚ) =
            (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ) := by
          rw [WithTop.coe_add]; exact hcσ
        exact WithTop.coe_injective this
      have h3 := tr_sig_le PD.p j y M' PD.hp.two_le
      have h4 := tr_ceil_ge PD.p r
      change ((-(sigT PD.p j y M') : ℚ) : WithTop ℚ) ≤ ((x : ℚ) : WithTop ℚ) + ((e : ℚ) : WithTop ℚ)
      rw [← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
  · rcases hx : v (c * ((PD.p : LL) ^ σ)⁻¹) with _ | x
    · rw [hx] at hcσ
      have h6 : (⊤ : WithTop ℚ) + ((σ : ℚ) : WithTop ℚ) = ⊤ := top_add _
      exact absurd (h6.symm.trans hcσ) WithTop.top_ne_coe
    · exact mem_valuation_ring_smul_invariant W hO _ x hx hb
  · have h5 : c • (toLL (((W.φA ^ j) W.π₀) ^ r) : ZMod n → PowerSeries LL) =
        (c * ((PD.p : LL) ^ σ)⁻¹) • (((PD.p : LL) ^ σ) • toLL (((W.φA ^ j) W.π₀) ^ r)) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [h5, hab', smul_add, smul_smul, mul_smul_comm, mul_comm (toLL b)]

theorem valuation_decomposition_eventually [IsDomain O] (W : LocWach PD LL O v n) (h9 : UniformizerRingClause W)
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (j y M' N : ℕ) : ∃ r₀ : ℕ, ∀ r ≥ r₀, ∀ c : LL,
      v c = (((-((r : ℚ) * PD.p / ((PD.p : ℚ) - 1))) : ℚ) : WithTop ℚ) →
      ∃ x₁ x₂, (∃ a ∈ W.AΔ, x₁ = ((PD.p : LL) ^ N) • toLL a) ∧ InWachLocalised W x₂ ∧
        c • toLL (((W.φA ^ j) W.π₀) ^ r) = x₁ + toLL (JJ W j y M') * x₂ := by
  refine ⟨max M' y, fun r hr c hc => ?_⟩
  have h1 : M' ≤ r := le_trans (le_max_left _ _) hr
  have h2 : y ≤ (PD.p - 1) * r := by
    have h3 : y ≤ r := le_trans (le_max_right _ _) hr
    have h4 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
    calc y ≤ 1 * r := by omega
      _ ≤ (PD.p - 1) * r := Nat.mul_le_mul_right _ h4
  obtain ⟨b, hb, hbr⟩ := tr_vanish_int W h9 j y M' r h1 h2
  refine ⟨0, c • toLL b, ⟨0, W.AΔ.zero_mem, by simp⟩, mem_valuation_ring_smul_invariant W hO c _ hc hb, ?_⟩
  rw [hbr, map_mul, zero_add, mul_smul_comm, mul_comm]

theorem coreTr_of [IsDomain O] (W : LocWach PD LL O v n) (h9 : CaseA W → UniformizerRingClause W)
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) : coreTr W := fun hA =>
  ⟨frobenius_factor_mem_ideal W (h9 hA), frobenius_pow_uniformizer_factorisation W (h9 hA),
    fun j y M' r hj c hc => valuation_decomposition_frobenius_pow W (h9 hA) hO hA.2.2 j y M' r hj c hc,
    fun j y M' _ N => valuation_decomposition_eventually W (h9 hA) hO j y M' N⟩

end TruncPart

theorem tr_exists_crys {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [FiniteDimensional Qp LL] [CommRing O] [IsDomain O] [Algebra O LL]
    (hinj : Function.Injective (algebraMap O LL)) : ∃ T : LocLat G Qp LL O, IsCrys PD T.ρ := by
  have := PD.finK₀
  obtain ⟨L⟩ := Formalism.WeaklyAdmissibleFiltrations.existsStableLattice_holds G LL O hinj
  exact ⟨{ V := LL, ρ := 1, cont := fun x => by simpa using continuous_const, L := L },
    Formalism.WeaklyAdmissibleFiltrations.trivialIsCrystalline_holds G Qp K₀ K B BdR PD LL⟩

theorem uniformizer_clause_case_A (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (hA : CaseA ((HW l).W K s LL h)) : UniformizerRingClause ((HW l).W K s LL h) := by
  have := LL.2
  obtain ⟨T, hT⟩ := tr_exists_crys ((D.loc l).PD K) ↥LL.1 ↥(OL LL) Subtype.val_injective
  have h1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId ↥(K0 K) ↥K.1) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  exact ((h9 l K s LL h T hT hA.2.1 hA.2.2).2.2 h1).1

theorem truncation_of_uniformizer_clause (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) : ExistsUnitClasses D HW F := by
  intro l _ K s LL h
  exact coreTr_of _ (uniformizer_clause_case_A D HW F h9 l K s LL h)
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem gen_ceil_eq (l s : ℕ) (hl : 3 ≤ l) :
    ⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ = (s + (l - 2)) / (l - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have e1 : (((m + 2 : ℕ) : ℝ) - 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have e2 : m + 2 - 2 = m := by omega
  have e3 : m + 2 - 1 = m + 1 := by omega
  rw [e1, e2, e3]
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hpos]
    have h := Nat.lt_mul_div_succ (s + m) (show 0 < m + 1 by omega)
    have h' : s ≤ (s + m) / (m + 1) * (m + 1) := by
      have : (m + 1) * ((s + m) / (m + 1) + 1) = (s + m) / (m + 1) * (m + 1) + (m + 1) := by ring
      omega
    exact_mod_cast h'
  · have h := Nat.le_ceil ((s : ℝ) / ((m + 1 : ℕ) : ℝ))
    rw [div_le_iff₀ hpos] at h
    have h' : s ≤ ⌈(s : ℝ) / ((m + 1 : ℕ) : ℝ)⌉₊ * (m + 1) := by exact_mod_cast h
    have : (s + m) / (m + 1) < ⌈(s : ℝ) / ((m + 1 : ℕ) : ℝ)⌉₊ + 1 := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < m + 1 by omega)]
      have : (⌈(s : ℝ) / ((m + 1 : ℕ) : ℝ)⌉₊ + 1) * (m + 1) =
        ⌈(s : ℝ) / ((m + 1 : ℕ) : ℝ)⌉₊ * (m + 1) + (m + 1) := by ring
      omega
    omega

theorem gen_div_le (l s : ℕ) (hl : 3 ≤ l) :
    (((s + (l - 2)) / (l - 1) : ℕ) : ℝ) ≤ (s : ℝ) / ((l : ℝ) - 1) + 1 := by
  rw [← gen_ceil_eq l s hl]
  have hl' : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    linarith
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem real_bound_of_integer_bound (l : ℕ) (hl : 3 ≤ l) (s' s Hi c : ℕ)
    (h : s' ≤ Hi + c + 2 + (s + (l - 2)) / (l - 1)) :
    (s' : ℝ) ≤ (Hi : ℝ) + c + 3 + (s : ℝ) / ((l : ℝ) - 1) := by
  have h1 : (s' : ℝ) ≤ (Hi : ℝ) + c + 2 + (((s + (l - 2)) / (l - 1) : ℕ) : ℝ) := by exact_mod_cast h
  have h2 := gen_div_le l s hl
  linarith

theorem gen_always (l s H r : ℕ) (c : ℝ) (hl : 3 ≤ l) (hs : s ≤ H)
    (hr : (r : ℝ) ≤ (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 + c) :
    ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ : ℕ) : ℝ) ≤ (H : ℝ) / ((l : ℝ) - 1) + 1 ∧
    ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ + r : ℕ) : ℝ) ≤
      (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + c + 1 := by
  have h := Formalism.RepresentationBoundsCohomology.N2.descent_cost_all.2.2.2.2.2.2.2.2.2.2.1 l s H c (r : ℝ) hl hs hr
  rw [gen_ceil_eq l s hl]
  refine ⟨h.1, ?_⟩
  push_cast
  exact h.2

theorem gen_decimals (l H : ℕ) (x c : ℝ)
    (h : x ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + c + 1) :
    (l = 5 → x ≤ 0.57 * (H : ℝ) + c + 1) ∧ (l = 7 → x ≤ 0.37 * (H : ℝ) + c + 1) ∧
      (l = 11 → x ≤ 0.21 * (H : ℝ) + c + 1) := by
  have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at h ⊢ <;> linarith

theorem gen_tsum_eq (l : ℝ) (f : ℕ → ℝ) :
    (∑' a : ℕ, f a * (l - 1) ^ (-(a : ℤ))) = ∑' a : ℕ, f a / (l - 1) ^ a := by
  congr 1
  funext a
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem gen_cW_le (l H : ℕ) (hl : 3 ≤ l) :
    (Formalism.RepresentationBoundsCohomology.N2.cW l H : ℝ) ≤ 2 + Real.log ((H : ℝ) + 1) := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hH : (0 : ℝ) ≤ Real.log ((H : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    linarith)
  have hlog : (1 : ℝ) ≤ Real.log l := by
    have h1 : Real.exp 1 ≤ (l : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log l := Real.log_le_log (Real.exp_pos 1) h1
  have hb : Real.logb l ((H : ℝ) + 1) ≤ Real.log ((H : ℝ) + 1) := by
    unfold Real.logb
    exact div_le_self hH hlog
  have hb0 : 0 ≤ Real.logb l ((H : ℝ) + 1) := by
    unfold Real.logb
    exact div_nonneg hH (by linarith)
  have := Nat.ceil_lt_add_one (a := 1 + Real.logb l ((H : ℝ) + 1)) (by linarith)
  unfold Formalism.RepresentationBoundsCohomology.N2.cW
  linarith

theorem gen_Oform (l : ℕ) (hl : 3 ≤ l) (H j : ℕ) (G r : ℝ) (hG : 0 ≤ G)
    (h : r ≤ (2 * G + (Formalism.RepresentationBoundsCohomology.N2.cW l H : ℝ) + 3) * (l : ℝ) / (((l : ℝ) - 1) * ((l : ℝ) - 2))
      + (H : ℝ) * (l : ℝ) / ((l : ℝ) - 1) ^ (j + 2) + (Formalism.RepresentationBoundsCohomology.N2.cW l H : ℝ)) :
    r ≤ 10 * (G / l + (H : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + (1 + Real.log ((H : ℝ) + 1))) := by
  have hl' : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hL
  set c : ℝ := (Formalism.RepresentationBoundsCohomology.N2.cW l H : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hcle : c ≤ 2 + Real.log ((H : ℝ) + 1) := gen_cW_le l H hl
  have hH : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have h1 : (0 : ℝ) < L - 1 := by linarith
  have h2 : (0 : ℝ) < L - 2 := by linarith
  have h12 : (0 : ℝ) < (L - 1) * (L - 2) := mul_pos h1 h2
  have hL0 : (0 : ℝ) < L := by linarith

  have a1 : L / ((L - 1) * (L - 2)) ≤ 3 / 2 := by
    rw [div_le_iff₀ h12]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * L - 2) (by linarith : (0 : ℝ) ≤ L - 3)]
  have a2 : L / ((L - 1) * (L - 2)) ≤ (9 / 2) / L := by
    rw [div_le_div_iff₀ h12 hL0]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 7 * L - 6) (by linarith : (0 : ℝ) ≤ L - 3)]
  have t1 : (2 * G + c + 3) * L / ((L - 1) * (L - 2)) ≤ 9 * (G / L) + (c + 3) * (3 / 2) := by
    have : (2 * G + c + 3) * L / ((L - 1) * (L - 2)) =
        2 * G * (L / ((L - 1) * (L - 2))) + (c + 3) * (L / ((L - 1) * (L - 2))) := by ring
    rw [this]
    have b1 : 2 * G * (L / ((L - 1) * (L - 2))) ≤ 2 * G * ((9 / 2) / L) :=
      mul_le_mul_of_nonneg_left a2 (by linarith)
    have b2 : (c + 3) * (L / ((L - 1) * (L - 2))) ≤ (c + 3) * (3 / 2) :=
      mul_le_mul_of_nonneg_left a1 (by linarith)
    have b3 : 2 * G * ((9 / 2) / L) = 9 * (G / L) := by ring
    linarith
  have t2 : (H : ℝ) * L / (L - 1) ^ (j + 2) ≤ (3 / 2) * ((H : ℝ) / (L - 1) ^ (j + 1)) := by
    have hp : (0 : ℝ) < (L - 1) ^ (j + 1) := pow_pos h1 _
    have : (H : ℝ) * L / (L - 1) ^ (j + 2) = ((H : ℝ) / (L - 1) ^ (j + 1)) * (L / (L - 1)) := by
      rw [pow_succ (L - 1) (j + 1)]
      field_simp
    rw [this, mul_comm (3 / 2 : ℝ)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ h1]
    linarith
  have hq : (0 : ℝ) ≤ (H : ℝ) / (L - 1) ^ (j + 1) := by positivity
  have hg : (0 : ℝ) ≤ G / L := by positivity
  have hlog : (0 : ℝ) ≤ Real.log ((H : ℝ) + 1) := Real.log_nonneg (by linarith)
  linarith

theorem gen_WR_num (l s H r : ℕ) (hl : 3 ≤ l) (hs : s ≤ H)
    (hr : (r : ℝ) ≤ (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 + cH l H) :
    ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ : ℕ) : ℝ) ≤ (H : ℝ) / ((l : ℝ) - 1) + 1 ∧
    ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ + r : ℕ) : ℝ) ≤
      (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cH l H + 1 ∧
    (l = 5 → ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ + r : ℕ) : ℝ) ≤ 0.57 * (H : ℝ) + cH l H + 1) ∧
    (l = 7 → ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ + r : ℕ) : ℝ) ≤ 0.37 * (H : ℝ) + cH l H + 1) ∧
    (l = 11 → ((⌈(s : ℝ) / ((l : ℝ) - 1)⌉₊ + r : ℕ) : ℝ) ≤ 0.21 * (H : ℝ) + cH l H + 1) := by
  obtain ⟨h1, h2⟩ := gen_always l s H r (cH l H : ℝ) hl hs hr
  obtain ⟨d5, d7, d11⟩ := gen_decimals l H _ _ h2
  exact ⟨h1, h2, d5, d7, d11⟩

theorem gen_resQ_elem {A : Type} [CommRing A] {D : Type} [AddCommGroup D] [Module A D]
    (N' : Submodule A D) (π₀ : A) (l a r : ℕ) (y : D) (h1 : π₀ ^ a • y ∈ N')
    (h2 : (l : A) ^ r • y ∈ N') : (π₀ + (l : A)) ^ (a + r) • y ∈ N' := by
  rw [add_pow, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ a + r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  by_cases hia : a ≤ i
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hia
    have e : π₀ ^ (a + t) * (l : A) ^ (a + r - (a + t)) * ((a + r).choose (a + t) : A) =
        (π₀ ^ t * (l : A) ^ (a + r - (a + t)) * ((a + r).choose (a + t) : A)) * π₀ ^ a := by ring
    rw [e, mul_smul]
    exact N'.smul_mem _ h1
  · obtain ⟨t, ht⟩ : ∃ t, a + r - i = r + t := ⟨a - i, by omega⟩
    have e : π₀ ^ i * (l : A) ^ (a + r - i) * ((a + r).choose i : A) =
        (π₀ ^ i * (l : A) ^ t * ((a + r).choose i : A)) * (l : A) ^ r := by rw [ht]; ring
    rw [e, mul_smul]
    exact N'.smul_mem _ h2

section GenZ

variable {l : ℕ} [Fact l.Prime]

theorem gen_dvd_iff (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

def genRed (l : ℕ) [Fact l.Prime] : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod (p := l)).toMonoidHom

theorem gen_red_one_iff (z : ℤ_[l]ˣ) : genRed l z = 1 ↔ (l : ℤ_[l]) ∣ (z : ℤ_[l]) - 1 := by
  rw [gen_dvd_iff, map_sub, map_one, sub_eq_zero]
  constructor
  · intro h
    have := congrArg (fun u : (ZMod l)ˣ => (u : ZMod l)) h
    simpa [genRed] using this
  · intro h
    apply Units.ext
    simpa [genRed] using h

theorem gen_tors_one (hl : l ≠ 2) (z : ℤ_[l]ˣ) (k : ℕ) (hk : 0 < k) (hz : z ^ k = 1)
    (hd : (l : ℤ_[l]) ∣ (z : ℤ_[l]) - 1) : z = 1 := by
  by_contra hne
  have h0 : (z : ℤ_[l]) - 1 ≠ 0 := fun h => hne (Units.ext (by simpa using sub_eq_zero.1 h))
  obtain ⟨y, hy⟩ := hd
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact h0 (by rw [hy, mul_zero])
  have hl0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hv : 1 ≤ PadicInt.valuation ((z : ℤ_[l]) - 1) := by
    rw [hy, PadicInt.valuation_mul hl0 hy0, PadicInt.valuation_p]
    omega
  have := (Formalism.WindowSums.arc_ZpowVal l z _ hv (fun h => absurd h hl) rfl (k : ℤ)
    (by exact_mod_cast hk.ne')).1
  apply this
  rw [zpow_natCast, hz]
  simp

theorem gen_dvd_of_val (x : ℤ_[l]) (h : PadicInt.valuation x = 1) : (l : ℤ_[l]) ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  · rw [PadicInt.unitCoeff_spec hx, h, pow_one]
    exact dvd_mul_left _ _

theorem gen_isGen (hl : l ≠ 2) (zd zg : ℤ_[l]ˣ) (k : ℕ) (hk : 0 < k) (hzd : zd ^ k = 1)
    (hgen : ∀ x : (ZMod l)ˣ, x ∈ Subgroup.zpowers (genRed l zd))
    (hzg : PadicInt.valuation ((zg : ℤ_[l]) - 1) = 1) : Formalism.RepresentationBoundsCohomology.N2.IsGen l (zd * zg) := by
  have hp : l.Prime := Fact.out
  have hrg : genRed l zg = 1 := (gen_red_one_iff zg).2 (gen_dvd_of_val _ hzg)
  have hord : orderOf (genRed l zd) = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card, ZMod.card_units]
  constructor
  · intro k' hk'
    have h1 : genRed l ((zd * zg) ^ k') = 1 := by
      rw [gen_red_one_iff]
      simpa using hk'
    rw [map_pow, map_mul, hrg, mul_one] at h1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1
  · have h1 : zd ^ (l - 1) = 1 := by
      apply gen_tors_one hl _ k hk
      · rw [← pow_mul, mul_comm, pow_mul, hzd, one_pow]
      · rw [← gen_red_one_iff, map_pow, ← hord, pow_orderOf_eq_one]
    have h2 : (((zd * zg : ℤ_[l]ˣ) : ℤ_[l])) ^ (l - 1) = ((zg ^ (((l - 1 : ℕ)) : ℤ) : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [← Units.val_pow_eq_pow_val, mul_pow, h1, one_mul, zpow_natCast]
    have hne : (((l - 1 : ℕ)) : ℤ) ≠ 0 := by
      have := hp.two_le
      omega
    rw [h2, (Formalism.WindowSums.arc_ZpowVal l zg 1 le_rfl (fun h => absurd h hl) hzg _ hne).2]
    have : padicValInt l (((l - 1 : ℕ)) : ℤ) = 0 := by
      rw [padicValInt.of_nat]
      apply padicValNat.eq_zero_of_not_dvd
      apply Nat.not_dvd_of_pos_of_lt
      · have := hp.two_le
        omega
      · have := hp.two_le
        omega
    rw [this]

theorem gen_exists_delta (hl : l ≠ 2) {Γ : Type} [CommGroup Γ] (ψ : Γ →* ℤ_[l]ˣ)
    (hψ : Function.Injective ψ) (S : Finset Γ) (hS : ∀ g, g ∈ S ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1)
    (hcard : S.card = l - 1) :
    ∃ δ ∈ S, ∀ x : (ZMod l)ˣ, x ∈ Subgroup.zpowers (genRed l (ψ δ)) := by
  classical
  let f : Γ →* (ZMod l)ˣ := (genRed l).comp ψ
  have hinj : Set.InjOn f (S : Set Γ) := by
    intro a ha b hb hab
    obtain ⟨ka, hka, hka'⟩ := (hS a).1 ha
    obtain ⟨kb, hkb, hkb'⟩ := (hS b).1 hb
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (a * b⁻¹) ^ (ka * kb) = 1 := by
      rw [mul_pow, inv_pow, pow_mul, hka', one_pow, mul_comm ka kb, pow_mul, hkb', one_pow,
        inv_one, mul_one]
    have h3 : ψ (a * b⁻¹) = 1 := by
      apply gen_tors_one hl _ (ka * kb) (Nat.mul_pos hka hkb)
      · rw [← map_pow, h2, map_one]
      · exact (gen_red_one_iff _).1 h1
    have h4 : a * b⁻¹ = 1 := hψ (by rw [h3, map_one])
    exact mul_inv_eq_one.1 h4
  have himg : S.image f = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcard, ZMod.card_units]
  obtain ⟨gb, hgb⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  obtain ⟨δ, hδ, hδf⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ gb)
  refine ⟨δ, hδ, fun x => ?_⟩
  have : genRed l (ψ δ) = gb := hδf
  rw [this]
  exact hgb x

end GenZ

section GenW

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P}

def genPsi {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    (H.W K s LL h).Gam →* ℤ_[l]ˣ :=
  MonoidHom.mk' (fun g => Classical.choose (chi_zl h g)) (by
    intro a b
    apply Units.ext
    apply zl_inj_O LL
    have hab := Classical.choose_spec (chi_zl h (a * b))
    have ha := Classical.choose_spec (chi_zl h a)
    have hb := Classical.choose_spec (chi_zl h b)
    rw [hab, Units.val_mul, RingHom.map_mul, ha, hb, MonoidHom.map_mul, Units.val_mul])

theorem genPsi_spec {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (g : (H.W K s LL h).Gam) :
    algebraMap ℤ_[l] ↥(OL LL) ((genPsi (H := H) h g : ℤ_[l]ˣ) : ℤ_[l]) =
      (((H.W K s LL h).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) :=
  Classical.choose_spec (chi_zl h g)

theorem genPsi_inj {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) :
    Function.Injective (genPsi (P := P) (H := H) h) := by
  intro a b hab
  apply (H.W K s LL h).χΓ_inj
  apply Units.ext
  rw [← genPsi_spec, ← genPsi_spec, hab]

end GenW

section GenW2

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P}

theorem gen_exists_abs (hl : l ≠ 2) {Γ : Type} [CommGroup Γ] (ψ : Γ →* ℤ_[l]ˣ)
    (hψ : Function.Injective ψ) (S : Finset Γ) (hS : ∀ g, g ∈ S ↔ ∃ k : ℕ, 0 < k ∧ g ^ k = 1)
    (hcard : S.card = l - 1) (γ : Γ) (hγ : PadicInt.valuation (((ψ γ : ℤ_[l]ˣ) : ℤ_[l]) - 1) = 1) :
    ∃ g : Γ, Formalism.RepresentationBoundsCohomology.N2.IsGen l (ψ g) := by
  obtain ⟨δ, hδ, hgen⟩ := gen_exists_delta hl ψ hψ S hS hcard
  obtain ⟨k, hk, hk'⟩ := (hS δ).1 hδ
  refine ⟨δ * γ, ?_⟩
  rw [map_mul]
  exact gen_isGen hl _ _ k hk (by rw [← map_pow, hk', map_one]) hgen hγ

theorem exists_gen_of_card {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hl : l ≠ 2)
    (hs : s = 1) (hcard : (H.W K s LL h).DelF.card = l - 1) :
    ∃ g : (H.W K s LL h).Gam, ∃ z : ℤ_[l]ˣ,
      algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) =
        (((H.W K s LL h).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) ∧ Formalism.RepresentationBoundsCohomology.N2.IsGen l z := by
  obtain ⟨zg, hzg, hzgv⟩ := gam_zl (P := P) (H := H) h
  have hz : genPsi (H := H) h (H.W K s LL h).gam = zg := by
    apply Units.ext
    apply zl_inj_O LL
    rw [genPsi_spec, hzg]
  obtain ⟨g, hg⟩ := gen_exists_abs hl (genPsi (H := H) h) (genPsi_inj (P := P) (H := H) h) (H.W K s LL h).DelF
    (H.W K s LL h).DelF_def hcard (H.W K s LL h).gam (by rw [hz, hzgv, hs])
  exact ⟨g, genPsi (H := H) h g, genPsi_spec h g, hg⟩

end GenW2

section GenCrys

open TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

theorem gen_isCrys_congr (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  let E : V ⊗[Qp] B ≃ₗ[LL] V' ⊗[Qp] B := AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)
  have hE : ∀ g x, E (actVB PD ρ g x) = actVB PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVB, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : Dcris PD ρ = (Dcris PD ρ').comap (E : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B) := by
    ext x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (Dcris PD ρ')).finrank_eq.symm

variable [TopologicalSpace G]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem gen_one_crys (W : LocWach PD LL O v n) [FiniteDimensional Qp LL] : IsCrys PD W.one.ρ := by
  have := PD.finK₀
  obtain ⟨e₀, he₀, hT⟩ := W.one_line
  have hspan : Submodule.span LL ({e₀} : Set W.one.V) = ⊤ := by
    rw [eq_top_iff, ← W.one.L.span, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, hT, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [← algebraMap_smul LL c e₀]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₀)
  let e : LL ≃ₗ[LL] W.one.V := LinearEquiv.ofBijective (LinearMap.toSpanSingleton LL W.one.V e₀) (by
    constructor
    · intro a b hab
      simp only [LinearMap.toSpanSingleton_apply] at hab
      exact smul_left_injective LL he₀ hab
    · intro x
      have hx : x ∈ Submodule.span LL ({e₀} : Set W.one.V) := by rw [hspan]; trivial
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact ⟨c, by simp⟩)
  refine gen_isCrys_congr PD (1 : Representation LL G LL) W.one.ρ e (fun g x => ?_)
    (Formalism.WeaklyAdmissibleFiltrations.pht_galois.2.2.2.2.1 G Qp K₀ K B BdR PD LL)
  rw [W.one_triv]
  rfl

theorem gen_finrank_one (h : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 := by
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) h).finrank_eq, Module.finrank_self]

end GenCrys

theorem exists_gen (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (hA : CaseA ((HW l).W K s LL h)) :
    ∃ g : ((HW l).W K s LL h).Gam, ∃ z : ℤ_[l]ˣ,
      algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) =
        ((((HW l).W K s LL h).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) ∧ Formalism.RepresentationBoundsCohomology.N2.IsGen l z := by
  obtain ⟨hbij, hs1, hp2⟩ := hA
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hc := (h9 l K s LL h ((HW l).W K s LL h).one (gen_one_crys _) hs1 hp2).1
  rw [gen_finrank_one hbij, Nat.div_one, hp] at hc
  exact exists_gen_of_card h (by rw [← hp]; exact hp2) (by rw [← (HW l).W_s K s LL h]; exact hs1) hc

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftBRing

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem liftb_φE_pow (W : LocWach PD LL O v n) (k : ℕ) (a : LetA O n) :
    algebraMap (LetA O n) W.EE ((W.φA ^ k) a) = (W.φE ^ k) (algebraMap (LetA O n) W.EE a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φE_ext]
    rfl

theorem liftb_X_unit (W : LocWach PD LL O v n) : IsUnit (algebraMap (LetA O n) W.EE W.X) := by
  rw [LocWach.X, liftb_φE_pow]
  exact W.EE_π.map (W.φE ^ (W.s - 1))

theorem liftb_X_cancel (a b : PowerSeries O) (h : PowerSeries.X * a = PowerSeries.X * b) : a = b := by
  ext n
  have h' := congrArg (PowerSeries.coeff (n + 1)) h
  simpa [PowerSeries.coeff_succ_X_mul] using h'

theorem liftb_q₀ (W : LocWach PD LL O v n) :
    ∃ w : PowerSeries O, W.q₀ = PowerSeries.X ^ (PD.p - 1) + ((PD.p : ℕ) : PowerSeries O) * w := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : PowerSeries O) PowerSeries.X
  refine ⟨r, liftb_X_cancel _ _ ?_⟩
  have hp : PD.p = (PD.p - 1) + 1 := (Nat.sub_add_cancel PD.hp.one_le).symm
  have hX : (PowerSeries.X : PowerSeries O) ^ PD.p = PowerSeries.X * PowerSeries.X ^ (PD.p - 1) := by
    conv_lhs => rw [hp, pow_succ']
  rw [W.q₀_def, hr, hX]
  ring

theorem liftb_q (W : LocWach PD LL O v n) :
    ∃ w : LetA O n, W.q = letπ ^ (PD.p - 1) + ((PD.p : ℕ) : LetA O n) * w := by
  obtain ⟨w, hw⟩ := liftb_q₀ W
  refine ⟨fun _ => w, ?_⟩
  funext i
  simp only [LocWach.q, letπ, Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.natCast_apply]
  exact hw

theorem liftb_q_unit (W : LocWach PD LL O v n) : IsUnit (algebraMap (LetA O n) W.EE W.q) := by
  obtain ⟨w, hw⟩ := liftb_q W
  have := W.EE_complete
  have hj : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨u, hu⟩ := (W.EE_π.pow (PD.p - 1))
  have h1 := (Ideal.mem_jacobson_bot.1 hj) (algebraMap (LetA O n) W.EE w * ((u⁻¹ : W.EEˣ) : W.EE))
  have h2 : algebraMap (LetA O n) W.EE W.q =
      (u : W.EE) * (((PD.p : ℕ) : W.EE) * (algebraMap (LetA O n) W.EE w * ((u⁻¹ : W.EEˣ) : W.EE)) + 1) := by
    rw [hw, map_add, map_mul, map_pow, map_natCast, ← hu]
    have : (u : W.EE) * ((u⁻¹ : W.EEˣ) : W.EE) = 1 := u.mul_inv
    linear_combination (-(((PD.p : ℕ) : W.EE) * algebraMap (LetA O n) W.EE w)) * this
  rw [h2]
  exact u.isUnit.mul h1

theorem liftb_Q_unit (W : LocWach PD LL O v n) : IsUnit (algebraMap (LetA O n) W.EE W.Q) := by
  rw [LocWach.Q, liftb_φE_pow]
  exact (liftb_q_unit W).map (W.φE ^ (W.s - 1))

theorem liftb_unit_bij (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n)
    (h : IsUnit (algebraMap (LetA O n) W.EE a)) : Function.Bijective (fun x : W.DD T => a • x) := by
  obtain ⟨u, hu⟩ := h
  have e : ∀ x : W.DD T, a • x = (u : W.EE) • x := fun x => by rw [hu, algebraMap_smul]
  constructor
  · intro x y hxy
    simp only [e] at hxy
    have := congrArg (fun z => ((u⁻¹ : W.EEˣ) : W.EE) • z) hxy
    simpa [smul_smul] using this
  · intro y
    refine ⟨((u⁻¹ : W.EEˣ) : W.EE) • y, ?_⟩
    simp only [e, smul_smul, Units.mul_inv, one_smul]

theorem liftb_X_inj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    ∀ x : W.DD T, W.X • x = 0 → x = 0 := fun x hx =>
  (liftb_unit_bij W T W.X (liftb_X_unit W)).1 (by simpa using hx)

theorem liftb_Q_bij (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    Function.Bijective (fun x : W.DD T => W.Q • x) :=
  liftb_unit_bij W T W.Q (liftb_Q_unit W)

theorem liftb_φpow_π (W : LocWach PD LL O v n) (k : ℕ) :
    ∃ c : LetA O n, (W.φA ^ k) letπ = letπ * c := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (W.φA ^ k) W.q, ?_⟩
    rw [pow_succ, AlgHom.mul_apply, W.φA_π, map_mul, hc, mul_assoc]

theorem liftb_one_add_X_unit (W : LocWach PD LL O v n) (t : LetA O n) : IsUnit (1 + W.X * t) := by
  obtain ⟨c, hc⟩ := liftb_φpow_π W (W.s - 1)
  rw [Pi.isUnit_iff]
  intro i
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have : PowerSeries.constantCoeff ((1 + W.X * t) i) = 1 := by
    simp [LocWach.X, hc, letπ]
  rw [this]
  exact isUnit_one

theorem liftb_φpow_γ (W : LocWach PD LL O v n) (g : W.Gam) (k : ℕ) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, W.φA_γA, ih]

theorem liftb_γ₀_X (W : LocWach PD LL O v n) (g : W.Gam) :
    ∃ t : PowerSeries O, W.γ₀ g PowerSeries.X =
      PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t) := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨f₁, hf₁⟩ := PowerSeries.X_dvd_iff.2 h0
  have hc : PowerSeries.constantCoeff f₁ = ((W.χΓ g : Oˣ) : O) := by
    rw [hf₁] at h1
    have := PowerSeries.coeff_succ_X_mul 0 f₁
    rw [zero_add] at this
    rw [this] at h1
    simpa using h1
  have h2 : PowerSeries.constantCoeff (f₁ - PowerSeries.C ((W.χΓ g : Oˣ) : O)) = 0 := by
    simp [hc]
  obtain ⟨t, ht⟩ := PowerSeries.X_dvd_iff.2 h2
  refine ⟨t, ?_⟩
  rw [hf₁, ← ht]
  ring

theorem liftb_gammaXk (W : LocWach PD LL O v n) (g : W.Gam) (k : ℕ) :
    ∃ t : LetA O n, W.γA g ((W.φA ^ k) letπ) = (W.φA ^ k) letπ *
      (algebraMap O (LetA O n) ((W.χΓ g : Oˣ) : O) + (W.φA ^ k) letπ * t) := by
  obtain ⟨t, ht⟩ := liftb_γ₀_X W g
  have h : W.γA g letπ =
      letπ * (algebraMap O (LetA O n) ((W.χΓ g : Oˣ) : O) + letπ * (fun _ => t)) := by
    funext i
    simp only [LocWach.γA, letγ, letπ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply,
      Pi.mul_apply, Pi.add_apply, Pi.algebraMap_apply]
    rw [ht]
    rfl
  refine ⟨(W.φA ^ k) (fun _ => t), ?_⟩
  rw [← liftb_φpow_γ, h, map_mul, map_add, map_mul, AlgHom.commutes]

theorem liftb_gammaX (W : LocWach PD LL O v n) :
    ∃ t : LetA O n, W.γA W.gam W.X =
      W.X * (algebraMap O (LetA O n) ((W.χΓ W.gam : Oˣ) : O) + W.X * t) :=
  liftb_gammaXk W W.gam (W.s - 1)

end LiftBRing

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.RepresentationBoundsCohomology.N2 (GBase GPair IsGen Letters lagrange_and_w_all descent_cost_all dual_w_by_letters dual_w_by_letters_extended cost cW)

section WMap

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem wmap_γ₀X (W : LocWach PD LL O v n) (g : W.Gam) : ∃ t : PowerSeries O,
    W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C (W.χΓ g : O) + PowerSeries.X * t) := by
  obtain ⟨h0, h1⟩ := W.γ₀_X g
  obtain ⟨f₁, hf₁⟩ := PowerSeries.X_dvd_iff.mpr h0
  have h2 : PowerSeries.constantCoeff (f₁ - PowerSeries.C (W.χΓ g : O)) = 0 := by
    rw [hf₁, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul] at h1
    rw [map_sub, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, h1,
      sub_self]
  obtain ⟨t, ht⟩ := PowerSeries.X_dvd_iff.mpr h2
  exact ⟨t, by rw [hf₁, ← ht]; ring⟩

theorem wmap_φpow_γA (W : LocWach PD LL O v n) (g : W.Gam) (k : ℕ) (a : LetA O n) :
    W.γA g ((W.φA ^ k) a) = (W.φA ^ k) (W.γA g a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

theorem wmap_γAX (W : LocWach PD LL O v n) (g : W.Gam) (k : ℕ) : ∃ t : LetA O n,
    W.γA g ((W.φA ^ k) letπ) =
      (W.φA ^ k) letπ * (algebraMap O (LetA O n) (W.χΓ g : O) + (W.φA ^ k) letπ * t) := by
  obtain ⟨t, ht⟩ := wmap_γ₀X W g
  have hπ : W.γA g letπ = letπ * (algebraMap O (LetA O n) (W.χΓ g : O) + letπ * fun _ => t) := by
    funext i
    simp only [LocWach.γA, letγ, letπ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply,
      Pi.mul_apply, Pi.add_apply, Pi.algebraMap_apply, ht]
    rfl
  refine ⟨(W.φA ^ k) fun _ => t, ?_⟩
  rw [wmap_φpow_γA, hπ, map_mul, map_add, map_mul, AlgHom.commutes]

theorem wmap_φE_pow (W : LocWach PD LL O v n) (k : ℕ) (a : LetA O n) :
    algebraMap (LetA O n) W.EE ((W.φA ^ k) a) = (W.φE ^ k) (algebraMap (LetA O n) W.EE a) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, pow_succ, AlgHom.mul_apply, ih, W.φE_ext]
    rfl

theorem wmap_unit (W : LocWach PD LL O v n) (k : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ k) letπ)) := by
  rw [wmap_φE_pow]
  exact W.EE_π.map (W.φE ^ k)

theorem wmap_γA_letE (W : LocWach PD LL O v n) (g : W.Gam) (i : ZMod n) :
    W.γA g (letE i) = letE i := by
  funext j
  simp only [LocWach.γA, letγ, letE, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem wmap_φA_letE (W : LocWach PD LL O v n) (i : ZMod n) :
    W.φA (letE (i - 1)) = letE i := by
  funext j
  simp only [LocWach.φA, letφ, letE, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : j - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

theorem wmap_letE_idem (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem wmap_γD_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n)
    (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem wmap_φD_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

theorem wmap_map_smul (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L)
    (a : LetA O n) (x : W.DD T) : W.map F (a • x) = a • W.map F x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem wmap_mem_Nl (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ ∃ y ∈ W.N T, (letE i : LetA O n) • y = x := by
  unfold LocWach.Nl
  rw [Submodule.mem_map]
  rfl

theorem wmap_Nl_le (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    W.Nl T i ≤ W.N T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nl W T i x).1 hx
  exact (W.N T).smul_mem _ hy

theorem wmap_Nl_fix (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.Nl T i) : (letE i : LetA O n) • x = x := by
  obtain ⟨y, _, rfl⟩ := (wmap_mem_Nl W T i x).1 hx
  rw [smul_smul, wmap_letE_idem]

theorem wmap_mem_Nimg (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (x : W.DD T₂) : x ∈ Nimg W F i ↔ ∃ y ∈ W.Nl T₁ i, W.map F y = x := by
  unfold Nimg
  rw [Submodule.mem_map]
  rfl

theorem wmap_Nimg_le (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ) (i : ZMod n) : Nimg W F i ≤ W.Nl T₂ i := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nimg W F i x).1 hx
  obtain ⟨y', hy', rfl⟩ := (wmap_mem_Nl W T₁ i y).1 hy
  rw [wmap_map_smul]
  exact (wmap_mem_Nl W T₂ i _).2 ⟨_, W.map_N F c₁ c₂ _ hy', rfl⟩

theorem wmap_Nl_γ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (X : LetA O n)
    (h : ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γD T g x - x = X • x') (i : ZMod n) :
    ∀ x ∈ W.Nl T i, ∃ x' ∈ W.Nl T i, W.γD T g x - x = X • x' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nl W T i x).1 hx
  obtain ⟨y', hy', e⟩ := h y hy
  refine ⟨(letE i : LetA O n) • y', (wmap_mem_Nl W T i _).2 ⟨y', hy', rfl⟩, ?_⟩
  rw [wmap_γD_smul, wmap_γA_letE, ← smul_sub, e, smul_comm]

theorem wmap_Nimg_γ (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (g : W.Gam) (X : LetA O n) (i : ZMod n)
    (h : ∀ x ∈ W.Nl T₁ i, ∃ x' ∈ W.Nl T₁ i, W.γD T₁ g x - x = X • x') :
    ∀ x ∈ Nimg W F i, ∃ x' ∈ Nimg W F i, W.γD T₂ g x - x = X • x' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nimg W F i x).1 hx
  obtain ⟨y', hy', e⟩ := h y hy
  refine ⟨W.map F y', (wmap_mem_Nimg W F i _).2 ⟨y', hy', rfl⟩, ?_⟩
  rw [← W.map_γ, ← map_sub, e, wmap_map_smul]

variable {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

def DZ (_ℓ : ℕ) (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Type := W.DD T

instance DZ.acg (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : AddCommGroup (DZ ℓ W T) :=
  inferInstanceAs (AddCommGroup (W.DD T))

instance DZ.modA (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    Module (LetA O n) (DZ ℓ W T) :=
  inferInstanceAs (Module (LetA O n) (W.DD T))

instance DZ.modZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Module ℤ_[ℓ] (DZ ℓ W T) :=
  Module.compHom (W.DD T) (algebraMap ℤ_[ℓ] O)

theorem wmap_tow (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (z : ℤ_[ℓ]) (a : LetA O n)
    (x : W.DD T) : (z • a) • x = algebraMap ℤ_[ℓ] O z • (a • x) := by
  rw [← smul_assoc, algebraMap_smul]

instance DZ.tow (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    IsScalarTower ℤ_[ℓ] (LetA O n) (DZ ℓ W T) :=
  ⟨fun z a x => wmap_tow W T z a x⟩

theorem wmap_X_inj (W : LocWach PD LL O v n) (k : ℕ) (T : LocLat G Qp LL O) (x : W.DD T)
    (hx : (W.φA ^ k) letπ • x = 0) : x = 0 := by
  rw [← algebraMap_smul W.EE] at hx
  exact (wmap_unit W k).smul_eq_zero.1 hx

def gBase (W : LocWach PD LL O v n) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (k : ℕ) : GBase ℓ (LetA O n) where
  γ := (W.γA g).restrictScalars ℤ_[ℓ]
  X := (W.φA ^ k) letπ
  u := z
  γX := by
    obtain ⟨t, ht⟩ := wmap_γAX W g k
    refine ⟨t, ?_⟩
    rw [IsScalarTower.algebraMap_apply ℤ_[ℓ] O (LetA O n), hz]
    exact ht

def gPair (W : LocWach PD LL O v n) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (k : ℕ) (T : LocLat G Qp LL O)
    (N N' : Submodule (LetA O n) (W.DD T)) (le : N' ≤ N)
    (hN : ∀ x ∈ N, ∃ x' ∈ N, W.γD T g x - x = (W.φA ^ k) letπ • x')
    (hN' : ∀ x ∈ N', ∃ x' ∈ N', W.γD T g x - x = (W.φA ^ k) letπ • x') :
    GPair (gBase W g z hz k) (DZ ℓ W T) where
  N := N
  N' := N'
  le := le
  γ :=
    { toFun := W.γD T g
      map_add' := map_add _
      map_smul' := fun c x => (W.γD T g).map_smul (algebraMap ℤ_[ℓ] O c) x }
  γ_smul := fun a x => wmap_γD_smul W T g a x
  X_inj := fun x hx => wmap_X_inj W k T x hx
  γ_N := hN
  γ_N' := hN'

theorem wmap_n_pos (W : LocWach PD LL O v n) : 0 < n := by
  rw [W.n_eq]
  have := PD.finK₀
  exact Module.finrank_pos

theorem wmap_sup (hn : 0 < n) (f : ZMod n → ℕ) :
    (⨆ j, f j) = (Finset.range n).sup fun k : ℕ => f (k : ZMod n) := by
  have : NeZero n := ⟨hn.ne'⟩
  apply le_antisymm
  · apply ciSup_le
    intro j
    have h := Finset.le_sup (f := fun k : ℕ => f (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt j))
    simpa [ZMod.natCast_zmod_val] using h
  · apply Finset.sup_le
    intro k _
    exact le_ciSup (Set.finite_range f).bddAbove _

theorem wmap_Jumps (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ)
    (h : JumpsLet W T Mi hi) : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mi hi := fun τ i hτ => h i τ hτ

theorem coreWX_of (W : LocWach PD LL O v n) (h : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) : coreWX W := by
  intro T₁ T₂ F Mi hi hS hJ i y hy
  have h1 := (h T₁ T₂ F Mi hi hS.1 hS.2.1 hS.2.2 (wmap_Jumps W T₁ Mi hi hJ)).1 i y hy
  rw [wmap_sup (wmap_n_pos W)] at h1
  exact h1

theorem wmap_P2X (W : LocWach PD LL O v n) (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) :
    ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γD T W.gam x - x = (W.φA ^ (W.s - 1)) letπ • x' := by
  intro x hx
  obtain ⟨x', hx', e⟩ := Submodule.mem_map.1 ((h2 T hT).2.2 x hx)
  exact ⟨x', hx', e.symm⟩

theorem wmap_P2π (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) :
    ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γD T g x - x = (W.φA ^ 0) letπ • x' := by
  intro x hx
  obtain ⟨x', hx', e⟩ := W.N_π T g x hx
  exact ⟨x', hx', e⟩

def gPairL (W : LocWach PD LL O v n) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (k : ℕ) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ)
    (h₁ : ∀ x ∈ W.N T₁, ∃ x' ∈ W.N T₁, W.γD T₁ g x - x = (W.φA ^ k) letπ • x')
    (h₂ : ∀ x ∈ W.N T₂, ∃ x' ∈ W.N T₂, W.γD T₂ g x - x = (W.φA ^ k) letπ • x') (i : ZMod n) :
    GPair (gBase W g z hz k) (DZ ℓ W T₂) :=
  gPair W g z hz k T₂ (W.Nl T₂ i) (Nimg W F i) (wmap_Nimg_le W F c₁ c₂ i) (wmap_Nl_γ W T₂ g _ h₂ i)
    (wmap_Nimg_γ W F g _ i (wmap_Nl_γ W T₁ g _ h₁ i))

theorem coreWB_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ W.gam : O))
    (hv : PadicInt.valuation ((z : ℤ_[ℓ]) - 1) = W.s) (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hX : coreWX W) :
    coreWB W := by
  subst hp
  intro _ T₁ T₂ F Mi hi hS hJ i
  exact lagrange_and_w_all.2.2.1 PD.p (LetA O n) _ (DZ PD.p W T₂)
    (gPairL W W.gam z hz (W.s - 1) F hS.1 hS.2.1 (wmap_P2X W h2 T₁ hS.1) (wmap_P2X W h2 T₂ hS.2.1) i)
    W.s (Hmax n Mi hi) W.s_pos W.s_two hv (hX T₁ T₂ F Mi hi hS hJ i)

theorem wmap_X_one (W : LocWach PD LL O v n) (hs : W.s = 1) : W.X = letπ := by
  unfold LocWach.X
  rw [hs]
  simp

theorem wmap_Q_one (W : LocWach PD LL O v n) (hs : W.s = 1) : W.Q = W.q := by
  unfold LocWach.Q
  rw [hs]
  simp

def gPairπ (W : LocWach PD LL O v n) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ) (i : ZMod n) : GPair (gBase W g z hz 0) (DZ ℓ W T₂) :=
  gPairL W g z hz 0 F c₁ c₂ (wmap_P2π W T₁ g) (wmap_P2π W T₂ g) i

theorem wmap_KillsH (W : LocWach PD LL O v n) (hs : W.s = 1) (hX : coreWX W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ) (hS : Sur W F)
    (hJ : JumpsLet W T₁ Mi hi) (i : ZMod n) : Kills W F i (letπ ^ Hmax n Mi hi) := by
  have h := hX T₁ T₂ F Mi hi hS hJ i
  rwa [wmap_X_one W hs] at h

theorem wmap_sI_mem (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (H : ℕ) (h : Kills W F i (letπ ^ H)) :
    Kills W F i (letπ ^ sI W F i) ∧ sI W F i ≤ H ∧ ∀ t, Kills W F i (letπ ^ t) → sI W F i ≤ t :=
  ⟨Nat.sInf_mem (s := {k : ℕ | Kills W F i (letπ ^ k)}) ⟨H, h⟩, Nat.sInf_le h,
    fun _ ht => Nat.sInf_le ht⟩

theorem coreWA_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (hgen : IsGen ℓ z) (hX : coreWX W) :
    coreWA W := by
  subst hp
  intro hA T₁ T₂ F Mi hi hS hJ i
  exact lagrange_and_w_all.2.2.2.1 PD.p hA.2.2 (LetA O n) _ (DZ PD.p W T₂) (gPairπ W g z hz F hS.1 hS.2.1 i)
    (Hmax n Mi hi) hgen (wmap_KillsH W hA.2.1 hX F Mi hi hS hJ i)

theorem wach_first_of_generator (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (hgen : IsGen ℓ z) (hX : coreWX W) :
    WachQuotientAnnihilator W := by
  subst hp
  intro hA T₁ T₂ F Mi hi hS hJ i a j haj
  obtain ⟨h1, h2, _⟩ := wmap_sI_mem W F i _ (wmap_KillsH W hA.2.1 hX F Mi hi hS hJ i)
  exact descent_cost_all.2.2.2.2.2.2.1 PD.p hA.2.2 (LetA O n) _ (DZ PD.p W T₂) (gPairπ W g z hz F hS.1 hS.2.1 i)
    (sI W F i) (Hmax n Mi hi) a j hgen h2 h1 haj

theorem wmap_three {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

theorem wmap_q₀ (W : LocWach PD LL O v n) : ∃ w : PowerSeries O,
    W.q₀ = ((PD.p : ℕ) : PowerSeries O) * w + PowerSeries.X ^ (PD.p - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq PD.hp (1 : PowerSeries O) PowerSeries.X
  refine ⟨r, ?_⟩
  have h : PowerSeries.X * W.q₀ =
      PowerSeries.X * (((PD.p : ℕ) : PowerSeries O) * r + PowerSeries.X ^ (PD.p - 1)) := by
    rw [W.q₀_def, hr, mul_add, ← pow_succ', Nat.sub_add_cancel PD.hp.one_le, one_pow]
    ring
  ext m
  have h' := congrArg (PowerSeries.coeff (m + 1)) h
  rwa [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul] at h'

def PhiBasis (W : LocWach PD LL O v n) : Prop :=
  ∀ a : LetA O n, ∃ e : Fin PD.p → LetA O n, a = ∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (e k)

def PhiLinInj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∀ (i : ZMod n) (x : Fin PD.p → W.DD T), (∀ k, x k ∈ W.Nl T (i - 1)) →
    ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (x k) = 0 → ∀ k, x k = 0

def JumpsQuot (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ),
    Sur W F → JumpsLet W T₁ Mi hi → JumpsLet W T₂ Mi hi

theorem frobenius_q_pow_mem_letter (W : LocWach PD LL O v n) (hs : W.s = 1) (T : LocLat G Qp LL O)
    (Mi hi : ZMod n → ℕ) (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi) (i : ZMod n) :
    ∀ x ∈ W.Nl T (i - 1), W.q ^ Mi i • W.φD T x ∈ W.Nl T i := by
  intro x hx
  have h := h5.1 i x hx
  rw [wmap_Q_one W hs] at h
  refine (wmap_mem_Nl W T i _).2 ⟨_, h, ?_⟩
  have e : W.φD T x = (letE i : LetA O n) • W.φD T x := by
    conv_lhs => rw [← wmap_Nl_fix W T (i - 1) x hx, wmap_φD_smul, wmap_φA_letE]
  rw [smul_comm, ← e]

theorem q_pow_smul_mem_frobenius_span (W : LocWach PD LL O v n) (hs : W.s = 1) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ) (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T₁ Mi hi) (i : ZMod n) :
    ∀ r ∈ Nimg W F i, W.q ^ hi i • r ∈
      Submodule.span (LetA O n) (W.φD T₂ '' (Nimg W F (i - 1) : Set (W.DD T₂))) := by
  intro r hr
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nimg W F i r).1 hr
  have h := h5.2.1 i y hy
  rw [wmap_Q_one W hs] at h
  rw [← wmap_map_smul]
  have hle : (Formalism.MainNotions.DeltaInvariantLattices.φspan W T₁ (W.Nl T₁ (i - 1))).map
      ((W.map F).restrictScalars (LetA O n)) ≤
      Submodule.span (LetA O n) (W.φD T₂ '' (Nimg W F (i - 1) : Set (W.DD T₂))) := by
    unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨s, hs', rfl⟩, rfl⟩
    exact ⟨W.map F s, (wmap_mem_Nimg W F (i - 1) _).2 ⟨s, hs', rfl⟩, (W.map_φ F s).symm⟩
  exact hle (Submodule.mem_map_of_mem h)

section LettersA

variable [Fact PD.p.Prime] [Algebra ℤ_[PD.p] O]

def gLetters (W : LocWach PD LL O v n) (g : W.Gam) (z : ℤ_[PD.p]ˣ)
    (hz : algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O)) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ) : Letters (gBase W g z hz 0) n (DZ PD.p W T₂) where
  pair := gPairπ W g z hz F c₁ c₂
  φA := (W.φA : LetA O n →+* LetA O n)
  q := W.q
  w := fun _ => Classical.choose (wmap_q₀ W)
  φπ := W.φA_π
  hq := by
    funext i
    exact Classical.choose_spec (wmap_q₀ W)
  φ := fun _ => (W.φD T₂).toAddMonoidHom
  φ_smul := fun _ a x => wmap_φD_smul W T₂ a x

end LettersA

theorem wach_second_of_generator (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (hgen : IsGen ℓ z) (hX : coreWX W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hJQ : JumpsQuot W) (hB : PhiBasis W)
    (hI : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → PhiLinInj W T) : WachExponentRecursion W := by
  subst hp
  intro hA T₁ T₂ F Mi hi hS hJ i
  have hn : NeZero n := ⟨(wmap_n_pos W).ne'⟩
  have hs := hA.2.1
  have hK := fun i => wmap_KillsH W hs hX F Mi hi hS hJ i
  have hsI := fun i => wmap_sI_mem W F i _ (hK i)
  have C := dual_w_by_letters PD.p hA.2.2 (LetA O n) _ n (DZ PD.p W T₂) (gLetters W g z hz F hS.1 hS.2.1) Mi hi
    (fun i => sI W F i) (Hmax n Mi hi) hgen
    (fun i => frobenius_q_pow_mem_letter W hs T₂ Mi hi
      (h5 T₂ Mi hi hS.2.1 (wmap_Jumps W T₂ Mi hi (hJQ T₁ T₂ F Mi hi hS hJ))) i)
    (fun i => q_pow_smul_mem_frobenius_span W hs F Mi hi (h5 T₁ Mi hi hS.1 (wmap_Jumps W T₁ Mi hi hJ)) i)
    hB (hI T₂ hS.2.1) hK (fun i => ⟨(hsI i).1, (hsI i).2.2⟩)
  exact real_bound_of_integer_bound PD.p (wmap_three PD.hp hA.2.2) _ _ _ _ (C.1 i)

theorem coreWR_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (g : W.Gam) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ g : O)) (hgen : IsGen ℓ z) (hX : coreWX W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hJQ : JumpsQuot W) (hB : PhiBasis W)
    (hI : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → PhiLinInj W T) : coreWR W 10 := by
  subst hp
  intro hA T₁ T₂ F Mi hi hS hJ i
  have hn : NeZero n := ⟨(wmap_n_pos W).ne'⟩
  have hs := hA.2.1
  have h3 : 3 ≤ PD.p := wmap_three PD.hp hA.2.2
  have hK := fun i => wmap_KillsH W hs hX F Mi hi hS hJ i
  have hsI := fun i => wmap_sI_mem W F i _ (hK i)
  obtain ⟨w, hw⟩ := ((h9 T₁ hS.1 hs hA.2.2).2.2 (gen_finrank_one hA.1)).1.2.2.1
  obtain ⟨_, E2, _, _, _, E6⟩ := dual_w_by_letters_extended PD.p hA.2.2 (LetA O n) _ n (DZ PD.p W T₂)
    (gLetters W g z hz F hS.1 hS.2.1) (fun i => sI W F i) (Hmax n Mi hi) W.π₀ (w : LetA O n) hgen hw hK
    (fun i => ⟨(hsI i).1, (hsI i).2.2⟩)
  obtain ⟨UnramifiedEulerProductIntegral, E6b⟩ := E6 Mi hi
    (fun i => frobenius_q_pow_mem_letter W hs T₂ Mi hi
      (h5 T₂ Mi hi hS.2.1 (wmap_Jumps W T₂ Mi hi (hJQ T₁ T₂ F Mi hi hS hJ))) i)
    (fun i => q_pow_smul_mem_frobenius_span W hs F Mi hi (h5 T₁ Mi hi hS.1 (wmap_Jumps W T₁ Mi hi hJ)) i)
    hB (hI T₂ hS.2.1)
  have hc : Kills W F i (lp W (cost PD.p 0 (sI W F i))) := by
    have h := descent_cost_all.2.2.2.2.2.1 PD.p hA.2.2 (LetA O n) _ (DZ PD.p W T₂) (gPairπ W g z hz F hS.1 hS.2.1 i)
      (sI W F i) 0 hgen (Nat.zero_le _) (hsI i).1
    rw [pow_zero, mul_one] at h
    exact h
  have hcb := descent_cost_all.2.2.2.2.1 PD.p hA.2.2 0 (sI W F i) (Hmax n Mi hi) (Nat.zero_le _) (hsI i).2.1
  have hceil : 1 + Real.logb PD.p ((Hmax n Mi hi : ℝ) + 1) ≤ (cH PD.p (Hmax n Mi hi) : ℝ) :=
    Nat.le_ceil _
  have hcΔ : KillsΔ W F i (lp W (cost PD.p 0 (sI W F i))) := fun y hy _ => hc y hy
  have hr_le : rI W F i ≤ cost PD.p 0 (sI W F i) := Nat.sInf_le hcΔ
  have hr_mem : KillsΔ W F i (lp W (rI W F i)) :=
    Nat.sInf_mem (s := {r : ℕ | KillsΔ W F i (lp W r)}) ⟨_, hcΔ⟩
  have hr_le' : (rI W F i : ℝ) ≤ (cost PD.p 0 (sI W F i) : ℝ) := by exact_mod_cast hr_le
  have hr : (rI W F i : ℝ) ≤
      (sI W F i : ℝ) * PD.p / ((PD.p : ℝ) - 1) ^ 2 + cH PD.p (Hmax n Mi hi) := by
    rw [Nat.cast_zero, sub_zero] at hcb
    linarith
  have hA2 : KillsΔ W F i (W.π₀ ^ AI W F i) := by
    intro y hy _
    unfold AI
    rw [gen_ceil_eq _ _ h3]
    exact E2 i y hy
  obtain ⟨n1, n2, n3, n4, n5⟩ := gen_WR_num PD.p (sI W F i) (Hmax n Mi hi) (rI W F i) h3
    (hsI i).2.1 hr
  refine ⟨le_of_le_of_eq (UnramifiedEulerProductIntegral i).2 (gen_tsum_eq (PD.p : ℝ) _).symm, hA2, hr, hr_mem, ?_, n1, n2, n3,
    n4, n5, ?_⟩
  · intro y hy hΔ
    exact gen_resQ_elem (Nimg W F i) W.π₀ PD.p (AI W F i) (rI W F i) y (hA2 y hy hΔ)
      (hr_mem y hy hΔ)
  · intro j Gc hG hw'
    exact gen_Oform PD.p h3 (Hmax n Mi hi) j Gc _ hG (le_trans hr_le' (E6b i j Gc hG hw'))

theorem natCeil_div_rat_eq_real (m p : ℕ) :
    ⌈((m : ℕ) : ℚ) / ((p : ℚ) - 1)⌉₊ = ⌈((m : ℕ) : ℝ) / ((p : ℝ) - 1)⌉₊ := by
  rw [← Int.ceil_toNat, ← Int.ceil_toNat]
  congr 1
  rw [← Rat.ceil_cast (α := ℝ)]
  push_cast
  rfl

theorem coreWK1a_of (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W)
    (e : ℕ) (hK : IntermediateUnramifiedOdd W e) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Mi hi : ZMod n → ℕ) (hS : Sur W F) (hJ : JumpsLet W T₁ Mi hi) (i : ZMod n)
    (π' u : LetA O n) (hπ : π' = u * letπ ^ ((PD.p - 1) / e)) :
    KillsΔ W F i (π' ^ ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊) := by
  obtain ⟨hs, h2, rfl⟩ := hK
  obtain ⟨π₁, E, hr, -⟩ := (h9 T₁ hS.1 hs h2).2.1
  obtain ⟨w, hw⟩ := hr.2.2.1
  intro y hy hΔ
  have h := (h3 T₁ T₂ F Mi hi hS.1 hS.2.1 hS.2.2 (wmap_Jumps W T₁ Mi hi hJ)).2 hs π₁ hr.1 ⟨w, hw⟩
    i y hy (fun δ hδ => by rw [hΔ δ hδ, sub_self]; exact Submodule.zero_mem _)
  rw [wmap_sup (wmap_n_pos W), natCeil_div_rat_eq_real] at h
  have e1 : π' = (u * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π₁ := by
    rw [hπ, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
  rw [e1, mul_pow, mul_smul]
  exact (Nimg W F i).smul_mem _ h

end WMap

theorem wach_first_claim_of_lemma (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h16 : adm16 D HW F) : WachKillsQuotients D HW F :=
  fun l _ K s LL hg => coreWX_of _ (h16 l K s LL hg)

theorem wach_statement_case_B (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h2 : adm2 D HW F) (h16 : adm16 D HW F) : WachKillsCaseB D HW F := by
  intro l _ K s LL hg
  obtain ⟨z, hz, hv⟩ := gam_zl (P := D.loc l) (H := HW l) hg
  exact coreWB_of _ ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hv) (h2 l K s LL hg)
    (coreWX_of _ (h16 l K s LL hg))

theorem wach_statement_case_A (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (h16 : adm16 D HW F) : WachKillsCaseA D HW F := by
  intro l _ K s LL hg hA
  obtain ⟨g, z, hz, hgen⟩ := exists_gen D HW F h9 l K s LL hg hA
  exact coreWA_of _ ((D.loc l).PD_p K) g z hz hgen (coreWX_of _ (h16 l K s LL hg)) hA

theorem wach_first_clause_of_literature (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (h16 : adm16 D HW F) : WachAnnihilatorAll D HW F := by
  intro l _ K s LL hg hA
  obtain ⟨g, z, hz, hgen⟩ := exists_gen D HW F h9 l K s LL hg hA
  exact wach_first_of_generator _ ((D.loc l).PD_p K) g z hz hgen (coreWX_of _ (h16 l K s LL hg)) hA

def opnJumpsQuot (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    CaseA ((HW l).W K s LL h) → JumpsQuot ((HW l).W K s LL h)

def opnPhiBasis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    CaseA ((HW l).W K s LL h) → PhiBasis ((HW l).W K s LL h)

def opnPhiLinInj (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    CaseA ((HW l).W K s LL h) → ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL),
      IsCrys ((D.loc l).PD K) T.ρ → PhiLinInj ((HW l).W K s LL h) T

theorem wach_second_clause_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h5 : adm5 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) (hJ : opnJumpsQuot D HW F)
    (hB : opnPhiBasis D HW F) (hI : opnPhiLinInj D HW F) : WachExponentRecursionAll D HW F := by
  intro l _ K s LL hg hA
  obtain ⟨g, z, hz, hgen⟩ := exists_gen D HW F h9 l K s LL hg hA
  exact wach_second_of_generator _ ((D.loc l).PD_p K) g z hz hgen (coreWX_of _ (h16 l K s LL hg))
    (h5 l K s LL hg) (hJ l K s LL hg hA) (hB l K s LL hg hA) (hI l K s LL hg hA) hA

theorem wach_result_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h5 : adm5 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) (hJ : opnJumpsQuot D HW F)
    (hB : opnPhiBasis D HW F) (hI : opnPhiLinInj D HW F) : WachResultConstant D HW F 10 := by
  intro l _ K s LL hg hA
  obtain ⟨g, z, hz, hgen⟩ := exists_gen D HW F h9 l K s LL hg hA
  exact coreWR_of _ ((D.loc l).PD_p K) g z hz hgen (coreWX_of _ (h16 l K s LL hg))
    (h5 l K s LL hg) (h9 l K s LL hg) (hJ l K s LL hg hA) (hB l K s LL hg hA)
    (hI l K s LL hg hA) hA

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.RepresentationBoundsCohomology.N2 (GBase GPair lagrange_and_w_all)

section WK1

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem gammaA_comm' (W : LocWach PD LL O v n) (g g' : W.Gam) (a : LetA O n) :
    W.γA g (W.γA g' a) = W.γA g' (W.γA g a) := by
  funext i
  have h1 : W.γ₀ g (W.γ₀ g' (a i)) = (W.γ₀ (g * g')) (a i) := by rw [map_mul]; rfl
  have h2 : W.γ₀ g' (W.γ₀ g (a i)) = (W.γ₀ (g' * g)) (a i) := by rw [map_mul]; rfl
  change W.γ₀ g (W.γ₀ g' (a i)) = W.γ₀ g' (W.γ₀ g (a i))
  rw [h1, h2, mul_comm]

theorem gammaD_comm (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g g' : W.Gam) (x : W.DD T) :
    W.γD T g (W.γD T g' x) = W.γD T g' (W.γD T g x) := by
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem delta_mul_mem (W : LocWach PD LL O v n) {δ δ' : W.Gam} (h : δ ∈ W.DelF) (h' : δ' ∈ W.DelF) :
    δ * δ' ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  obtain ⟨k', hk', e'⟩ := (W.DelF_def δ').1 h'
  exact (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', by
    rw [mul_pow, pow_mul, e, one_pow, mul_comm k k', pow_mul, e', one_pow, one_mul]⟩

theorem delta_inv_mem_alt (W : LocWach PD LL O v n) {δ : W.Gam} (h : δ ∈ W.DelF) : δ⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, e, inv_one]⟩

theorem mem_delta_iff_mul_mem (W : LocWach PD LL O v n) {δ' : W.Gam} (h' : δ' ∈ W.DelF) (δ : W.Gam) :
    δ ∈ W.DelF ↔ δ' * δ ∈ W.DelF :=
  ⟨fun h => delta_mul_mem W h' h, fun h => by
    have := delta_mul_mem W (delta_inv_mem_alt W h') h
    rwa [inv_mul_cancel_left] at this⟩

def wk1Tr (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : W.DD T :=
  ∑ δ ∈ W.DelF, W.γD T δ x

theorem trace_delta_invariant (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) :
    ∀ δ' ∈ W.DelF, W.γD T δ' (wk1Tr W T x) = wk1Tr W T x := by
  intro δ' h'
  unfold wk1Tr
  rw [map_sum]
  simp_rw [← W.γD_mul]
  exact Finset.sum_equiv (Equiv.mulLeft δ') (fun δ => mem_delta_iff_mul_mem W h' δ) (fun δ _ => rfl)

theorem trace_of_fixed (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T)
    (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) : wk1Tr W T x = (W.DelF.card : O) • x := by
  unfold wk1Tr
  rw [Finset.sum_congr rfl h, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O]

theorem trace_map_comm (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (x : W.DD T₁) : W.map F (wk1Tr W T₁ x) = wk1Tr W T₂ (W.map F x) := by
  unfold wk1Tr
  rw [map_sum]
  simp_rw [W.map_γ]

theorem gammaD_mem_letter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n)
    (x : W.DD T) (hx : x ∈ W.Nl T i) : W.γD T g x ∈ W.Nl T i := by
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nl W T i x).1 hx
  rw [wmap_γD_smul, wmap_γA_letE]
  exact (wmap_mem_Nl W T i _).2 ⟨_, W.N_Γ T g y hy, rfl⟩

theorem trace_mem_letter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.Nl T i) : wk1Tr W T x ∈ W.Nl T i :=
  Submodule.sum_mem _ fun δ _ => gammaD_mem_letter W T δ i x hx

theorem exists_invariant_preimage_trace (W : LocWach PD LL O v n) (c : O) (hc : c * (W.DelF.card : O) = 1)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n) (x : W.DD T₂)
    (hx : x ∈ Nimg W F i) (hΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ x = x) :
    ∃ y ∈ W.Nl T₁ i, (∀ δ ∈ W.DelF, W.γD T₁ δ y = y) ∧ W.map F y = x := by
  obtain ⟨y, hy, rfl⟩ := (wmap_mem_Nimg W F i x).1 hx
  refine ⟨c • wk1Tr W T₁ y, Submodule.smul_of_tower_mem _ c (trace_mem_letter W T₁ i y hy),
    fun δ hδ => by rw [map_smul, trace_delta_invariant W T₁ y δ hδ], ?_⟩
  rw [LinearMap.map_smul_of_tower, trace_map_comm, trace_of_fixed W T₂ _ hΔ, smul_smul, hc, one_smul]

theorem exists_invariant_gamma_sub (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n)
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = π' • x') (i : ZMod n) (x : W.DD T)
    (hx : x ∈ W.Nl T i) (hΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∃ x' ∈ W.Nl T i, (∀ δ ∈ W.DelF, W.γD T δ x' = x') ∧ W.γD T W.gam x - x = π' • x' := by
  obtain ⟨x₁, hx₁, e⟩ := hm x ⟨wmap_Nl_le W T i hx, hΔ⟩
  refine ⟨(letE i : LetA O n) • x₁, (wmap_mem_Nl W T i _).2 ⟨x₁, hx₁.1, rfl⟩,
    fun δ hδ => by rw [wmap_γD_smul, wmap_γA_letE, hx₁.2 δ hδ], ?_⟩
  have h1 : (letE i : LetA O n) • W.γ T x = W.γ T x :=
    wmap_Nl_fix W T i _ (gammaD_mem_letter W T W.gam i x hx)
  rw [smul_comm, ← e, smul_sub, h1, wmap_Nl_fix W T i x hx]
  rfl

theorem unit_mul_pi_pow_left_cancel' (w : (LetA O n)ˣ) (k : ℕ) (a b : LetA O n)
    (h : ((w : LetA O n) * letπ ^ k) * a = ((w : LetA O n) * letπ ^ k) * b) : a = b := by
  have h' : (letπ : LetA O n) ^ k * a = letπ ^ k * b := by
    have := congrArg (fun z => ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * z) h
    simpa [mul_assoc] using this
  funext i
  have hi := congrFun h' i
  exact PowerSeries.X_pow_mul_cancel (k := k) hi

theorem invariant_smul_mem_invariants (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n)
    (ha : a ∈ W.AΔ) (x : W.DD T) (hx : x ∈ W.NΔ T) : a • x ∈ W.NΔ T :=
  ⟨(W.N T).smul_mem a hx.1, fun δ hδ => by rw [wmap_γD_smul, ha δ hδ, hx.2 δ hδ]⟩

theorem exists_invariant_ratio (W : LocWach PD LL O v n) (k : ℕ) (π₁ π₂ : LetA O n) (h₁ : π₁ ∈ W.AΔ)
    (h₂ : π₂ ∈ W.AΔ) (w₁ w₂ : (LetA O n)ˣ) (e₁ : π₁ = (w₁ : LetA O n) * letπ ^ k)
    (e₂ : π₂ = (w₂ : LetA O n) * letπ ^ k) : ∃ c ∈ W.AΔ, π₁ = π₂ * c := by
  have e : π₁ = π₂ * (((w₂⁻¹ : (LetA O n)ˣ) : LetA O n) * (w₁ : LetA O n)) := by
    rw [e₁, e₂]
    calc (w₁ : LetA O n) * letπ ^ k
        = ((w₂ : LetA O n) * ((w₂⁻¹ : (LetA O n)ˣ) : LetA O n)) * ((w₁ : LetA O n) * letπ ^ k) := by
          rw [Units.mul_inv, one_mul]
      _ = _ := by ring
  refine ⟨_, fun δ hδ => ?_, e⟩
  apply unit_mul_pi_pow_left_cancel' w₂ k
  rw [← e₂]
  have h := h₁ δ hδ
  rw [e, map_mul, h₂ δ hδ] at h
  exact h

theorem gamma_sub_mod_change_unit (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π₁ π₂ c : LetA O n)
    (hc : c ∈ W.AΔ) (e : π₁ = π₂ * c)
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = π₁ • x') :
    ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = π₂ • x' := by
  intro x hx
  obtain ⟨x', hx', h⟩ := hm x hx
  exact ⟨c • x', invariant_smul_mem_invariants W T c hc x' hx', by rw [h, e, mul_smul]⟩

theorem constantCoeff_gamma_eq (W : LocWach PD LL O v n) (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  have hC : ∀ c : O, W.γ₀ g (PowerSeries.C c) = PowerSeries.C c := by
    intro c
    have : PowerSeries.C c = algebraMap O (PowerSeries O) c := by
      simp
    rw [this, AlgHom.commutes]
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  rw [map_add, map_mul, hC, map_add, map_mul, (W.γ₀_X g).1, zero_mul, zero_add,
    PowerSeries.constantCoeff_C]

theorem gamma_uniformizer_power_eq (W : LocWach PD LL O v n) (e s' : ℕ) (hk : s' ≠ 0) (π' : LetA O n)
    (E : ZMod n → Polynomial O) (h9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) :
    ∃ t ∈ W.AΔ, W.γA W.gam π' =
      π' * (algebraMap O (LetA O n) (((uγ W : Oˣ) : O) ^ s') + π' * t) := by
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, -, -, ⟨w', hw'⟩, -⟩ := h9
  have hreg : ∀ a b : LetA O n, π' * a = π' * b → a = b := fun a b hab => by
    rw [hw] at hab
    exact unit_mul_pi_pow_left_cancel' w _ a b hab
  set c : LetA O n := 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' with hc
  have hγ : W.γA W.gam π' = π' * c := by
    have : W.γA W.gam π' = π' + (w' : LetA O n) * π' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by rw [← hw']; ring
    rw [this, hc]; ring
  have hcΔ : c ∈ W.AΔ := by
    intro δ hδ
    apply hreg
    have h1 : W.γA δ (π' * c) = π' * c := by
      rw [← hγ, gammaA_comm', hπΔ δ hδ]
    rw [map_mul, hπΔ δ hδ] at h1
    exact h1
  have hπi : ∀ i, π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by
    intro i
    conv_lhs => rw [hw]
    rfl
  have hcc : ∀ i, PowerSeries.constantCoeff (c i) = ((uγ W : Oˣ) : O) ^ s' := by
    intro i
    obtain ⟨t, ht⟩ := wmap_γ₀X W W.gam
    have e1 : (W.γA W.gam π') i = W.γ₀ W.gam ((w : LetA O n) i) *
        (PowerSeries.X * (PowerSeries.C ((W.χΓ W.gam : Oˣ) : O) + PowerSeries.X * t)) ^ s' := by
      change W.γ₀ W.gam (π' i) = _
      rw [hπi, map_mul, map_pow, ht]
    have e2 : (π' * c) i = ((w : LetA O n) i * PowerSeries.X ^ s') * c i := by
      rw [← hπi]
      rfl
    have e3 : PowerSeries.X ^ s' * ((w : LetA O n) i * c i) =
        PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
          (PowerSeries.C ((W.χΓ W.gam : Oˣ) : O) + PowerSeries.X * t) ^ s') := by
      have := congrFun hγ i
      rw [e1, e2] at this
      rw [mul_pow] at this
      linear_combination -this
    have e4 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel e3)
    rw [map_mul, map_mul, constantCoeff_gamma_eq, map_pow, map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul,
      add_zero, PowerSeries.constantCoeff_C] at e4
    have hu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) := by
      have h1 : IsUnit ((w : LetA O n) i) :=
        (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i))
      exact h1.map PowerSeries.constantCoeff
    exact hu.mul_left_cancel e4
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    rw [hπi, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]
  set a : LetA O n := c - algebraMap O (LetA O n) (((uγ W : Oˣ) : O) ^ s') with ha
  have haΔ : a ∈ W.AΔ := W.AΔ.sub_mem hcΔ (W.AΔ.algebraMap_mem _)
  have ha0 : ∀ i, PowerSeries.constantCoeff (a i) = 0 := by
    intro i
    have : a i = c i - PowerSeries.C (((uγ W : Oˣ) : O) ^ s') := by
      rw [ha]
      simp
    rw [this, map_sub, hcc, PowerSeries.constantCoeff_C, sub_self]
  obtain ⟨f, hf, -⟩ := hsub a haΔ
  set t : LetA O n := fun i =>
    PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) with ht
  have hat : a = π' * t := by
    funext i
    have hs : PowerSeries.HasSubst (π' i) := PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
    have e1 := hf i
    rw [PowerSeries.eq_X_mul_shift_add_const (f i), PowerSeries.subst_add hs, PowerSeries.subst_mul hs,
      PowerSeries.subst_X hs, PowerSeries.subst_C] at e1
    have e2 : a i = π' i * t i + PowerSeries.C (PowerSeries.constantCoeff (f i)) := e1
    have e3 := congrArg PowerSeries.constantCoeff e2
    rw [ha0, map_add, map_mul, hπ0, zero_mul, zero_add, PowerSeries.constantCoeff_C] at e3
    rw [e2, ← e3, map_zero, add_zero]
    rfl
  have htΔ : t ∈ W.AΔ := by
    intro δ hδ
    apply hreg
    have h1 : W.γA δ (π' * t) = π' * t := by rw [← hat]; exact haΔ δ hδ
    rw [map_mul, hπΔ δ hδ] at h1
    exact h1
  refine ⟨t, htΔ, ?_⟩
  rw [hγ, ← hat, ha]
  ring_nf

def wk1Sub (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (S : Submodule (LetA O n) (W.DD T)) :
    Submodule ↥W.AΔ (W.DD T) where
  carrier := {x | x ∈ S ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨S.zero_mem, fun δ _ => map_zero _⟩
  add_mem' := fun {a b} ha hb =>
    ⟨S.add_mem ha.1 hb.1, fun δ hδ => by rw [map_add, ha.2 δ hδ, hb.2 δ hδ]⟩
  smul_mem' := fun a x hx => ⟨S.smul_mem (a : LetA O n) hx.1, fun δ hδ => by
    change W.γD T δ ((a : LetA O n) • x) = (a : LetA O n) • x
    rw [wmap_γD_smul, a.2 δ hδ, hx.2 δ hδ]⟩

theorem unit_mul_pi_pow_smul_injective (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (T : LocLat G Qp LL O)
    (x : W.DD T) (h : ((w : LetA O n) * letπ ^ k) • x = 0) : x = 0 := by
  have h1 : (letπ : LetA O n) ^ k • x = 0 := by
    have := congrArg (fun y => ((w⁻¹ : (LetA O n)ˣ) : LetA O n) • y) h
    simpa [smul_smul, ← mul_assoc] using this
  rw [← algebraMap_smul W.EE, map_pow] at h1
  exact (W.EE_π.pow k).smul_eq_zero.1 h1

theorem gamma_sub_mem_trace_image (W : LocWach PD LL O v n) (π' : LetA O n) (c : O)
    (hc : c * (W.DelF.card : O) = 1) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (i : ZMod n)
    (hm₁ : ∀ x ∈ W.NΔ T₁, ∃ x' ∈ W.NΔ T₁, W.γ T₁ x - x = π' • x') :
    ∀ x ∈ wk1Sub W T₂ (Nimg W F i), ∃ x' ∈ wk1Sub W T₂ (Nimg W F i),
      W.γD T₂ W.gam x - x = π' • x' := by
  intro x hx
  obtain ⟨y, hy, hyΔ, rfl⟩ := exists_invariant_preimage_trace W c hc F i x hx.1 hx.2
  obtain ⟨y', h1, h2, h3⟩ := exists_invariant_gamma_sub W T₁ π' hm₁ i y hy hyΔ
  refine ⟨W.map F y', ⟨(wmap_mem_Nimg W F i _).2 ⟨y', h1, rfl⟩,
    fun δ hδ => by rw [← W.map_γ, h2 δ hδ]⟩, ?_⟩
  rw [← W.map_γ, ← map_sub, h3, wmap_map_smul]

theorem gamma_sub_mem_invariants_sub (W : LocWach PD LL O v n) (π' : LetA O n) (T : LocLat G Qp LL O) (i : ZMod n)
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = π' • x') :
    ∀ x ∈ wk1Sub W T (W.Nl T i), ∃ x' ∈ wk1Sub W T (W.Nl T i),
      W.γD T W.gam x - x = π' • x' := by
  intro x hx
  obtain ⟨x', h1, h2, h3⟩ := exists_invariant_gamma_sub W T π' hm i x hx.1 hx.2
  exact ⟨x', ⟨h1, h2⟩, h3⟩

theorem kills_of_kills_invariants (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (i : ZMod n) (r : ℕ) (b : Fin r → W.DD T₂) (hb : ∀ j, b j ∈ W.NΔ T₂)
    (hgen : ∀ x ∈ W.N T₂, ∃ a : Fin r → LetA O n, x = ∑ j, a j • b j) (a₀ : LetA O n)
    (h : KillsΔ W F i a₀) : Kills W F i a₀ := by
  intro y hy
  obtain ⟨y', hy', rfl⟩ := (wmap_mem_Nl W T₂ i y).1 hy
  obtain ⟨a, rfl⟩ := hgen y' hy'
  rw [Finset.smul_sum, Finset.smul_sum]
  apply Submodule.sum_mem
  intro j _
  rw [smul_comm (letE i : LetA O n) (a j), smul_comm a₀ (a j)]
  exact (Nimg W F i).smul_mem _ (h _ ((wmap_mem_Nl W T₂ i _).2 ⟨b j, (hb j).1, rfl⟩)
    (fun δ hδ => by rw [wmap_γD_smul, wmap_γA_letE, (hb j).2 δ hδ]))

variable {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

def wk1γ (W : LocWach PD LL O v n) : ↥W.AΔ →ₐ[O] ↥W.AΔ :=
  ((W.γA W.gam).comp W.AΔ.val).codRestrict W.AΔ (fun a δ hδ => by
    change W.γA δ (W.γA W.gam (a : LetA O n)) = W.γA W.gam (a : LetA O n)
    rw [gammaA_comm', a.2 δ hδ])

instance DZ.towΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    IsScalarTower ℤ_[ℓ] ↥W.AΔ (DZ ℓ W T) :=
  ⟨fun z a x => wmap_tow W T z (a : LetA O n) x⟩

def wk1Base (W : LocWach PD LL O v n) (π' t : LetA O n) (hπ : π' ∈ W.AΔ) (ht : t ∈ W.AΔ)
    (u : ℤ_[ℓ]ˣ)
    (h : W.γA W.gam π' =
      π' * (algebraMap O (LetA O n) (algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ])) + π' * t)) :
    GBase ℓ ↥W.AΔ where
  γ := (wk1γ W).restrictScalars ℤ_[ℓ]
  X := ⟨π', hπ⟩
  u := u
  γX := ⟨⟨t, ht⟩, Subtype.ext (by
    rw [← IsScalarTower.algebraMap_apply ℤ_[ℓ] O (LetA O n)] at h
    exact h)⟩

def wk1Pair (W : LocWach PD LL O v n) (π' t : LetA O n) (hπ : π' ∈ W.AΔ) (ht : t ∈ W.AΔ)
    (u : ℤ_[ℓ]ˣ)
    (h : W.γA W.gam π' =
      π' * (algebraMap O (LetA O n) (algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ])) + π' * t))
    (w : (LetA O n)ˣ) (k : ℕ) (hw : π' = (w : LetA O n) * letπ ^ k) (c : O)
    (hc : c * (W.DelF.card : O) = 1) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ) (i : ZMod n)
    (hm₁ : ∀ x ∈ W.NΔ T₁, ∃ x' ∈ W.NΔ T₁, W.γ T₁ x - x = π' • x')
    (hm₂ : ∀ x ∈ W.NΔ T₂, ∃ x' ∈ W.NΔ T₂, W.γ T₂ x - x = π' • x') :
    GPair (wk1Base W π' t hπ ht u h) (DZ ℓ W T₂) where
  N := wk1Sub W T₂ (W.Nl T₂ i)
  N' := wk1Sub W T₂ (Nimg W F i)
  le := fun x hx => ⟨wmap_Nimg_le W F c₁ c₂ i hx.1, hx.2⟩
  γ :=
    { toFun := W.γD T₂ W.gam
      map_add' := map_add _
      map_smul' := fun z x => (W.γD T₂ W.gam).map_smul (algebraMap ℤ_[ℓ] O z) x }
  γ_smul := fun a x => wmap_γD_smul W T₂ W.gam (a : LetA O n) x
  X_inj := fun x hx => unit_mul_pi_pow_smul_injective W w k T₂ x (by rw [← hw]; exact hx)
  γ_N := gamma_sub_mem_invariants_sub W π' T₂ i hm₂
  γ_N' := gamma_sub_mem_trace_image W π' c hc F i hm₁

theorem isUnit_natCast_of_lt (k : ℕ) (h0 : 0 < k) (hlt : k < ℓ) : IsUnit ((k : ℕ) : ℤ_[ℓ]) := by
  by_contra h
  have hm : ((k : ℕ) : ℤ_[ℓ]) ∈ IsLocalRing.maximalIdeal ℤ_[ℓ] := (IsLocalRing.mem_maximalIdeal _).2 h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at hm
  exact absurd (Nat.le_of_dvd h0 hm) (by omega)

theorem coreWK1b_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ W.gam : O))
    (hv : PadicInt.valuation ((z : ℤ_[ℓ]) - 1) = W.s) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) (e : ℕ) (hK : IntermediateUnramifiedOdd W e) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ) (hS : Sur W F) (hJ : JumpsLet W T₁ Mi hi)
    (i : ZMod n) :
    Kills W F i (lp W (2 * ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊ +
      padicValNat PD.p (2 * ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊).factorial)) := by
  subst hp
  have hK' := hK
  obtain ⟨hs, h2, he⟩ := hK
  obtain ⟨hcard, ⟨π₁, E₁, hr₁, hm₁⟩, -⟩ := h9 T₁ hS.1 hs h2
  obtain ⟨-, ⟨π₂, E₂, hr₂, hm₂⟩, -⟩ := h9 T₂ hS.2.1 hs h2
  rw [he] at hcard hr₁ hr₂
  set s' := (PD.p - 1) / e with hs'
  have hpos : 0 < s' := by
    rw [← hcard]
    exact Finset.card_pos.2 ⟨1, (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩⟩
  have hlt : s' < PD.p := lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt PD.hp.pos one_pos)
  obtain ⟨cu, hcu⟩ := isUnit_natCast_of_lt (ℓ := PD.p) s' hpos hlt
  have hc : algebraMap ℤ_[PD.p] O ((cu⁻¹ : ℤ_[PD.p]ˣ) : ℤ_[PD.p]) * (W.DelF.card : O) = 1 := by
    rw [hcard, ← map_natCast (algebraMap ℤ_[PD.p] O), ← hcu, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨w₁, e₁⟩ := hr₁.2.2.1
  obtain ⟨w₂, e₂⟩ := hr₂.2.2.1
  obtain ⟨c', hc', ec⟩ := exists_invariant_ratio W s' π₂ π₁ hr₂.1 hr₁.1 w₂ w₁ e₂ e₁
  have hm₂' := gamma_sub_mod_change_unit W T₂ π₂ π₁ c' hc' ec hm₂.2
  obtain ⟨t, ht, hγ⟩ := gamma_uniformizer_power_eq W e s' hpos.ne' π₁ E₁ hr₁
  have hu : algebraMap ℤ_[PD.p] O (((z ^ s' : ℤ_[PD.p]ˣ)) : ℤ_[PD.p]) =
      ((uγ W : Oˣ) : O) ^ s' := by
    rw [Units.val_pow_eq_pow_val, map_pow, hz]
    rfl
  rw [← hu] at hγ
  have hval : PadicInt.valuation (((z ^ s' : ℤ_[PD.p]ˣ) : ℤ_[PD.p]) - 1) = 1 := by
    have h := (Formalism.WindowSums.arc_ZpowVal PD.p z 1 le_rfl (fun h => absurd h h2) (by rw [hv, hs])
      (s' : ℤ) (by exact_mod_cast hpos.ne')).2
    rw [zpow_natCast] at h
    rw [h, padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hpos hlt)]
  have hKa := coreWK1a_of W h9 h3 e hK' F Mi hi hS hJ i π₁ w₁ e₁
  set a := ⌈((e * Hmax n Mi hi : ℕ) : ℝ) / ((PD.p : ℝ) - 1)⌉₊ with ha
  have R := lagrange_and_w_all.2.2.1 PD.p ↥W.AΔ _ (DZ PD.p W T₂)
    (wk1Pair W π₁ t hr₁.1 ht (z ^ s') hγ w₁ s' e₁ _ hc F hS.1 hS.2.1 i hm₁.2 hm₂') 1 a le_rfl
    (fun h => absurd h h2) hval
    (fun x hx => ⟨hKa x hx.1 hx.2, ((wk1Sub W T₂ (W.Nl T₂ i)).smul_mem _ hx).2⟩)
  have hE : Formalism.RepresentationBoundsCohomology.N2.eWB PD.p a 1 = 2 * a + padicValNat PD.p (2 * a).factorial := by
    unfold Formalism.RepresentationBoundsCohomology.N2.eWB
    rw [mul_one]
  rw [hE] at R
  obtain ⟨r, b, hb, hgen, -⟩ := hm₂.1
  exact kills_of_kills_invariants W F i r b hb (fun x hx => (hgen x hx).exists) _
    (fun y hy hΔ => (R y ⟨hy, hΔ⟩).1)

theorem coreWK1_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (z : ℤ_[ℓ]ˣ)
    (hz : algebraMap ℤ_[ℓ] O (z : ℤ_[ℓ]) = (W.χΓ W.gam : O))
    (hv : PadicInt.valuation ((z : ℤ_[ℓ]) - 1) = W.s) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeLengthLemma W) : coreWK1 W :=
  fun e hK _ _ F Mi hi hS hJ i =>
    ⟨fun π' u _ hπ => coreWK1a_of W h9 h3 e hK F Mi hi hS hJ i π' u hπ,
      coreWK1b_of W hp z hz hv h9 h3 e hK F Mi hi hS hJ i⟩

theorem JumpsQuot_of (W : LocWach PD LL O v n)
    (hKer : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Sur W F →
      ∃ (T₀ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L), IsSESLat (Qp := Qp) ι F ∧ IsCrys PD T₀.ρ)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) : JumpsQuot W := by
  intro T₁ T₂ F Mi hi hS hJ i τ hτ a ha
  obtain ⟨T₀, ι, hses, c0⟩ := hKer T₁ T₂ F hS
  exact hJ i τ hτ a ((hJmp T₀ T₁ T₂ ι F hses c0 hS.1 hS.2.1 τ a).2 (Or.inr ha))

end WK1

theorem wach_statement_intermediate_fields (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : adm9 D HW F) (h16 : adm16 D HW F) : WachKillsIntermediateField D HW F := by
  intro l _ K s LL hg
  obtain ⟨z, hz, hv⟩ := gam_zl (P := D.loc l) (H := HW l) hg
  exact coreWK1_of _ ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hv) (h9 l K s LL hg)
    (h16 l K s LL hg)

theorem wach_statement_of_literature (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h2 : adm2 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) : ConclusionW D HW F :=
  ⟨wach_first_claim_of_lemma D HW F h16, wach_statement_case_B D HW F h2 h16, wach_statement_case_A D HW F h9 h16, wach_statement_intermediate_fields D HW F h9 h16⟩

theorem wach_statement_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : ConclusionW D HW F := by
  obtain ⟨-, h2, -, -, -, -, -, -, h9, -, -, -, -, -, -, h16, -⟩ := h
  exact wach_statement_of_literature D HW F h2 h9 h16

theorem wach_first_clause_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : WachAnnihilatorAll D HW F := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -, -, -, h16, -⟩ := h
  exact wach_first_clause_of_literature D HW F h9 h16

theorem opnJumpsQuot_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F)
    (hKer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
      (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
      Sur ((HW l).W K s LL h) F → ∃ (T₀ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
        (ι : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) ι F ∧ IsCrys ((D.loc l).PD K) T₀.ρ) :
    opnJumpsQuot D HW F :=
  fun l _ K s LL h _ => JumpsQuot_of _ (hKer l K s LL h) (h23 l K LL)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PhiB

variable {O : Type} [CommRing O]

def phibY (O : Type) [CommRing O] (p : ℕ) : Polynomial O := (Polynomial.X + 1) ^ p - 1

theorem phib_coe (p : ℕ) :
    ((phibY O p : Polynomial O) : PowerSeries O) = (1 + PowerSeries.X) ^ p - 1 := by
  simp [phibY]
  ring

theorem phib_monic [Nontrivial O] (p : ℕ) (hp : p.Prime) :
    (phibY O p).Monic ∧ (phibY O p).natDegree = p := by
  have h1 : ((Polynomial.X + 1 : Polynomial O) ^ p).Monic := by
    have := (Polynomial.monic_X_add_C (1 : O)).pow p
    simpa using this
  have h2 : ((Polynomial.X + 1 : Polynomial O) ^ p).natDegree = p := by
    have := (Polynomial.monic_X_add_C (1 : O)).natDegree_pow p
    rw [Polynomial.natDegree_X_add_C, mul_one] at this
    simpa using this
  have h3 : (1 : Polynomial O).degree < ((Polynomial.X + 1 : Polynomial O) ^ p).degree := by
    rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree h1.ne_zero, h2]
    exact_mod_cast hp.pos
  refine ⟨h1.sub_of_left h3, ?_⟩
  unfold phibY
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, h2]
  rw [h2, Polynomial.natDegree_one]
  exact hp.pos

theorem phib_dist [Nontrivial O] (p : ℕ) (hp : p.Prime) :
    (phibY O p).IsDistinguishedAt (Ideal.span {((p : ℕ) : O)}) := by
  refine ⟨⟨fun {k} hk => ?_⟩, (phib_monic p hp).1⟩
  rw [(phib_monic p hp).2] at hk
  unfold phibY
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_one]
  by_cases h0 : k = 0
  · subst h0
    simp
  · rw [if_neg h0, sub_zero]
    exact Ideal.mem_span_singleton.2 (Nat.cast_dvd_cast (hp.dvd_choose_self h0 hk))

theorem phib_div (p : ℕ) (hp : p.Prime) [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    (f : PowerSeries O) : ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < (p : WithBot ℕ) ∧
      f = ((1 + PowerSeries.X) ^ p - 1) * q + (r : PowerSeries O) := by
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨0, 0, by simp, Subsingleton.elim _ _⟩
  have hI : Ideal.span {((p : ℕ) : O)} ≠ ⊤ := by
    intro h
    have hH : IsHausdorff (Ideal.span {((p : ℕ) : O)}) O := inferInstance
    rw [h] at hH
    exact not_subsingleton O hH.subsingleton
  have H := phib_dist (O := O) p hp
  have hord : (phibY O p).natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map
    (phibY O p : PowerSeries O) 1
    (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  have Hd := (H.isWeierstrassDivisorAt hI).isWeierstrassDivisionAt_div_mod f
  refine ⟨(H.isWeierstrassDivisorAt hI).div f, (H.isWeierstrassDivisorAt hI).mod f, ?_, ?_⟩
  · have := Hd.degree_lt
    rw [← hord, (phib_monic p hp).2] at this
    exact this
  · rw [← phib_coe (O := O) p]
    exact Hd.eq_mul_add

theorem phib_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (x : O) :
    φ (PowerSeries.C x) = PowerSeries.C x := by
  exact φ.commutes x

theorem phib_shift (φ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℕ → O) :
    φ (PowerSeries.mk c) =
      PowerSeries.C (c 0) + φ PowerSeries.X * φ (PowerSeries.mk fun j => c (j + 1)) := by
  have h := PowerSeries.eq_X_mul_shift_add_const (PowerSeries.mk c)
  have h1 : (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (PowerSeries.mk c)) =
      PowerSeries.mk fun j => c (j + 1) := by
    ext
    simp
  have h2 : PowerSeries.constantCoeff (PowerSeries.mk c) = c 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  rw [h1, h2] at h
  conv_lhs => rw [h]
  rw [map_add, map_mul, phib_C]
  ring

theorem phib_poly (r : Polynomial O) (p : ℕ) (h : r.degree < (p : WithBot ℕ)) :
    (r : PowerSeries O) = ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * PowerSeries.C (r.coeff k) := by
  ext m
  rw [Polynomial.coeff_coe, map_sum,
    Fin.sum_univ_eq_sum_range
      (fun k => PowerSeries.coeff m (PowerSeries.X ^ k * PowerSeries.C (r.coeff k))) p]
  simp_rw [mul_comm (PowerSeries.X ^ _) (PowerSeries.C _), PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · apply Polynomial.coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le h ?_
    exact_mod_cast not_lt.1 (fun hlt => hm (Finset.mem_range.2 hlt))

theorem phib_main (p : ℕ) (hp : p.Prime) [IsAdicComplete (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : PowerSeries O) :
    ∃ e : Fin p → PowerSeries O, a = ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (e k) := by
  choose Dv Rm hDR using fun f : PowerSeries O => phib_div p hp f
  set Y : PowerSeries O := (1 + PowerSeries.X) ^ p - 1 with hY
  let qs : ℕ → PowerSeries O := fun m => Dv^[m] a
  let S : ℕ → PowerSeries O := fun m => ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
    φ (PowerSeries.mk fun j => (Rm (qs (j + m))).coeff k)
  have hq : ∀ m, qs m = Y * qs (m + 1) + (Rm (qs m) : PowerSeries O) := by
    intro m
    have := (hDR (qs m)).2
    have e : qs (m + 1) = Dv (qs m) := Function.iterate_succ_apply' Dv m a
    rw [e]
    exact this
  have hS : ∀ m, S m = Y * S (m + 1) + (Rm (qs m) : PowerSeries O) := by
    intro m
    rw [phib_poly _ p (hDR (qs m)).1]
    simp only [S]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phib_shift, hφ, zero_add]
    have : (fun j => (Rm (qs (j + 1 + m))).coeff (k : ℕ)) =
        fun j => (Rm (qs (j + (m + 1)))).coeff (k : ℕ) := by
      funext j
      rw [add_assoc, add_comm 1 m]
    rw [this]
    ring
  have hd : ∀ m, qs 0 - S 0 = Y ^ m * (qs m - S m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [ih, hq m, hS m, pow_succ]
      ring
  have hXY : PowerSeries.X ∣ Y := by
    rw [PowerSeries.X_dvd_iff, hY]
    simp
  refine ⟨fun k => PowerSeries.mk fun j => (Rm (qs j)).coeff k, ?_⟩
  have h0 : qs 0 - S 0 = 0 := by
    ext m
    have h1 : PowerSeries.X ^ (m + 1) ∣ qs 0 - S 0 := by
      rw [hd (m + 1)]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXY _) _
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 h1 m (Nat.lt_succ_self m)
  exact sub_eq_zero.1 h0

end PhiB

section PhiBW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem PhiBasis_of (W : LocWach PD LL O v n)
    [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O] : PhiBasis W := by
  intro a
  have hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
  choose e he using fun i : ZMod n => phib_main PD.p PD.hp W.φ₀ hφ (a i)
  refine ⟨fun k j => e (j + 1) k, ?_⟩
  funext i
  rw [Finset.sum_apply, he i]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = PowerSeries.X ^ (k : ℕ) * W.φ₀ (e (i - 1 + 1) k)
  rw [sub_add_cancel]

end PhiBW

section PhiBC

theorem phib_smodeq {M : Type} [CommRing M] (c x y : M) (k : ℕ) :
    x ≡ y [SMOD ((Ideal.span {c}) ^ k • ⊤ : Submodule M M)] ↔ c ^ k ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem phib_complete {R M : Type} [CommRing R] [CommRing M] [Algebra R M] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] {ι : Type} [Fintype ι] (b : Module.Basis ι R M) :
    IsAdicComplete (Ideal.span {algebraMap R M ϖ}) M := by
  have key : ∀ (x : M) (k : ℕ), (algebraMap R M ϖ) ^ k ∣ x ↔ ∀ j, ϖ ^ k ∣ b.equivFun x j := by
    intro x k
    constructor
    · rintro ⟨z, rfl⟩ j
      refine ⟨b.equivFun z j, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, map_smul]
      rfl
    · intro h
      choose d hd using h
      refine ⟨b.equivFun.symm d, ?_⟩
      rw [← map_pow, ← Algebra.smul_def, ← map_smul]
      apply b.equivFun.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      rw [hd j]
      rfl
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply b.equivFun.injective
    rw [map_zero]
    funext j
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) R)
    intro k
    rw [phib_smodeq, sub_zero]
    have h := hx k
    rw [phib_smodeq, sub_zero] at h
    exact (key x k).1 h j
  · intro f hf
    have hc : ∀ j, ∃ L : R, ∀ k,
        b.equivFun (f k) j ≡ L [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule R R)] := by
      intro j
      apply IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) R)
      intro m k hmk
      rw [phib_smodeq]
      have h := hf hmk
      rw [phib_smodeq] at h
      have h' := (key _ m).1 h j
      rwa [map_sub] at h'
    choose L hL using hc
    refine ⟨b.equivFun.symm L, fun k => ?_⟩
    rw [phib_smodeq, key]
    intro j
    rw [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply]
    exact (phib_smodeq _ _ _ _).1 (hL j k)

theorem phib_OL_complete {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    IsAdicComplete (Ideal.span {((l : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
  have h1 : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ℤ_[l] ↥LL.1) ℤ_[l] ↥LL.1)
  have h3 : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  have h4 : Module.IsTorsionFree ℤ_[l] ↥(OL LL) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (zl_inj_O LL)
  have h5 : Module.Free ℤ_[l] ↥(OL LL) := Module.free_of_finite_type_torsion_free'
  have h6 : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have h7 := phib_complete ((l : ℕ) : ℤ_[l]) (Module.finBasis ℤ_[l] ↥(OL LL))
  rwa [map_natCast] at h7

end PhiBC

theorem opnPhiBasis_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : opnPhiBasis D HW F := by
  intro l _ K s LL h _
  have hc : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p K]
    exact phib_OL_complete LL
  exact PhiBasis_of _

theorem wach_second_clause_of_inj (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h5 : adm5 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) (hJ : opnJumpsQuot D HW F)
    (hI : opnPhiLinInj D HW F) : WachExponentRecursionAll D HW F :=
  wach_second_clause_of_hypotheses D HW F h5 h9 h16 hJ (opnPhiBasis_holds D HW F) hI

theorem wach_result_of_inj (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h5 : adm5 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) (hJ : opnJumpsQuot D HW F)
    (hI : opnPhiLinInj D HW F) : WachResultConstant D HW F 10 :=
  wach_result_of_hypotheses D HW F h5 h9 h16 hJ (opnPhiBasis_holds D HW F) hI

theorem wach_clauses_of_admitted_inj (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) (hJ : opnJumpsQuot D HW F) (hI : opnPhiLinInj D HW F) :
    WachExponentRecursionAll D HW F ∧ WachResultConstant D HW F 10 := by
  obtain ⟨-, -, -, -, h5, -, -, -, h9, -, -, -, -, -, -, h16, -⟩ := h
  exact ⟨wach_second_clause_of_inj D HW F h5 h9 h16 hJ hI, wach_result_of_inj D HW F h5 h9 h16 hJ hI⟩

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section PhiI1

variable {O : Type} [CommRing O]

theorem phii_shift (φ : PowerSeries O →ₐ[O] PowerSeries O) (f : PowerSeries O) :
    φ f = PowerSeries.C (PowerSeries.constantCoeff f) +
      φ PowerSeries.X * φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) f) := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
  rw [map_add, map_mul, phib_C]
  ring

theorem phii_step (p : ℕ) (hp : p.Prime) [IsHausdorff (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : Fin p → PowerSeries O) (h : ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0) :
    (∀ k, PowerSeries.constantCoeff (a k) = 0) ∧
      ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
        φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (a k)) = 0 := by
  rcases subsingleton_or_nontrivial O with hO | hO
  · exact ⟨fun k => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hI : Ideal.span {((p : ℕ) : O)} ≠ ⊤ := by
    intro h'
    have hH : IsHausdorff (Ideal.span {((p : ℕ) : O)}) O := inferInstance
    rw [h'] at hH
    exact not_subsingleton O hH.subsingleton
  have H := phib_dist (O := O) p hp
  have hord : (phibY O p).natDegree = _ := congr(ENat.toNat $(H.coe_natDegree_eq_order_map
    (phibY O p : PowerSeries O) 1
    (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)))
  have hord' := (phib_monic (O := O) p hp).2.symm.trans hord
  set r : Polynomial O := ∑ k : Fin p,
    Polynomial.C (PowerSeries.constantCoeff (a k)) * Polynomial.X ^ (k : ℕ) with hr
  have hrd : r.degree < (p : WithBot ℕ) := Polynomial.degree_sum_fin_lt _
  have hrc : (r : PowerSeries O) = ∑ k : Fin p,
      PowerSeries.X ^ (k : ℕ) * PowerSeries.C (PowerSeries.constantCoeff (a k)) := by
    rw [hr, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, mul_comm]
  have e : (phibY O p : PowerSeries O) * (∑ k : Fin p, PowerSeries.X ^ (k : ℕ) *
      φ (PowerSeries.mk fun j => PowerSeries.coeff (j + 1) (a k))) + (r : PowerSeries O) =
      (phibY O p : PowerSeries O) * 0 + ((0 : Polynomial O) : PowerSeries O) := by
    rw [mul_zero, Polynomial.coe_zero, add_zero, ← h, hrc, phib_coe, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phii_shift φ (a k), hφ]
    ring
  obtain ⟨h1, h2⟩ := (H.isWeierstrassDivisorAt hI).eq_of_mul_add_eq_mul_add
    (by rw [← hord']; exact hrd) (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _) e
  refine ⟨fun k => ?_, h1⟩
  have h3 := congrArg (fun q : Polynomial O => q.coeff (k : ℕ)) h2
  simpa [hr, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using h3

theorem phii_indep (p : ℕ) (hp : p.Prime) [IsHausdorff (Ideal.span {((p : ℕ) : O)}) O]
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ p - 1)
    (a : Fin p → PowerSeries O) (h : ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0) :
    ∀ k, a k = 0 := by
  have key : ∀ (m : ℕ) (a : Fin p → PowerSeries O),
      ∑ k : Fin p, PowerSeries.X ^ (k : ℕ) * φ (a k) = 0 → ∀ k, PowerSeries.coeff m (a k) = 0 := by
    intro m
    induction m with
    | zero =>
      intro a h k
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (phii_step p hp φ hφ a h).1 k
    | succ m ih =>
      intro a h k
      have := ih _ (phii_step p hp φ hφ a h).2 k
      rwa [PowerSeries.coeff_mk] at this
  intro k
  ext m
  rw [map_zero]
  exact key m a h k

end PhiI1

section PhiI2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem phii_A (W : LocWach PD LL O v n) [IsHausdorff (Ideal.span {((PD.p : ℕ) : O)}) O]
    (a : Fin PD.p → LetA O n) (h : ∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k) = 0) :
    ∀ k, a k = 0 := by
  have hφ : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ PD.p - 1 := by rw [W.φ₀_X, W.q₀_def]
  intro k
  funext j
  have hj := congrFun h (j + 1)
  rw [Finset.sum_apply] at hj
  have e : ∀ k : Fin PD.p, ((letπ : LetA O n) ^ (k : ℕ) * W.φA (a k)) (j + 1) =
      PowerSeries.X ^ (k : ℕ) * W.φ₀ (a k j) := by
    intro k
    change PowerSeries.X ^ (k : ℕ) * W.φ₀ (a k (j + 1 - 1)) = _
    rw [add_sub_cancel_right]
  simp_rw [e] at hj
  exact phii_indep PD.p PD.hp W.φ₀ hφ (fun k => a k j) hj k

theorem phii_mod (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (a : Fin PD.p → LetA O n) (j : ℕ) (b : LetA O n)
    (h : ∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k) = ((PD.p : ℕ) : LetA O n) ^ j * b) :
    ∀ k, ∃ a' : LetA O n, a k = ((PD.p : ℕ) : LetA O n) ^ j * a' := by
  obtain ⟨e, he⟩ := PhiBasis_of W b
  have h0 : ∑ k : Fin PD.p, letπ ^ (k : ℕ) *
      W.φA (a k - ((PD.p : ℕ) : LetA O n) ^ j * e k) = 0 := by
    simp_rw [map_sub, map_mul, map_pow, map_natCast, mul_sub]
    rw [Finset.sum_sub_distrib, h, he, Finset.mul_sum]
    apply sub_eq_zero.2
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  intro k
  exact ⟨e k, sub_eq_zero.1 (phii_A W _ h0 k)⟩

theorem phii_EE (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (c : Fin PD.p → W.EE)
    (h : ∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) * W.φE (c k) = 0) :
    ∀ k, c k = 0 := by
  have claim : ∀ (j : ℕ) (k : Fin PD.p), ((PD.p : ℕ) : W.EE) ^ j ∣ c k := by
    intro j
    choose a m hm using fun k => W.EE_dense (c k) j
    set M : ℕ := ∑ k, m k with hM
    have hle : ∀ k, m k ≤ M := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hd : ∀ k, ∃ d : W.EE, c k * algebraMap (LetA O n) W.EE (letπ ^ M) =
        algebraMap (LetA O n) W.EE (a k * letπ ^ (M - m k)) + ((PD.p : ℕ) : W.EE) ^ j * d := by
      intro k
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hm k)
      refine ⟨d * algebraMap (LetA O n) W.EE (letπ ^ (M - m k)), ?_⟩
      have e1 : (letπ : LetA O n) ^ M = letπ ^ (m k) * letπ ^ (M - m k) := by
        rw [← pow_add, Nat.add_sub_cancel' (hle k)]
      rw [e1, map_mul, map_mul]
      linear_combination (algebraMap (LetA O n) W.EE (letπ ^ (M - m k))) * hd
    choose d hd using hd
    have h1 : algebraMap (LetA O n) W.EE
        (∑ k : Fin PD.p, letπ ^ (k : ℕ) * W.φA (a k * letπ ^ (M - m k))) =
        ((PD.p : ℕ) : W.EE) ^ j *
          (-∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) * W.φE (d k)) := by
      have h2 : ∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) *
          W.φE (c k * algebraMap (LetA O n) W.EE (letπ ^ M)) = 0 := by
        simp_rw [map_mul, ← mul_assoc]
        rw [← Finset.sum_mul, h, zero_mul]
      simp_rw [hd, map_add, map_mul, map_pow, map_natCast, mul_add] at h2
      rw [Finset.sum_add_distrib] at h2
      rw [map_sum, mul_neg, Finset.mul_sum]
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hext : ∀ a : LetA O n, algebraMap (LetA O n) W.EE (W.φA a) =
            W.φE (algebraMap (LetA O n) W.EE a) := fun a => (W.φE_ext a).symm
        rw [map_mul, map_pow, hext]
        simp only [map_mul, map_pow]
      · refine Finset.sum_congr rfl fun k _ => ?_
        ring
    obtain ⟨b, hb⟩ := W.EE_sat _ j (by rw [h1]; exact Ideal.mem_span_singleton.2 (Dvd.intro _ rfl))
    intro k
    obtain ⟨a', ha'⟩ := phii_mod W _ j b hb k
    have h3 : ((PD.p : ℕ) : W.EE) ^ j ∣ c k * algebraMap (LetA O n) W.EE (letπ ^ M) := by
      rw [hd k, ha', map_mul, map_pow, map_natCast]
      exact ⟨algebraMap (LetA O n) W.EE a' + d k, by ring⟩
    have hu : IsUnit (algebraMap (LetA O n) W.EE (letπ ^ M)) := by
      rw [map_pow]
      exact W.EE_π.pow M
    exact (hu.dvd_mul_right).1 h3
  intro k
  have hH : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE := W.EE_complete.toIsHausdorff
  apply hH.haus
  intro j
  rw [phib_smodeq, sub_zero]
  exact claim j k

end PhiI2

section PhiI3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem phii_finite (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) :
    Module.Finite W.EE (W.DD T) := by
  obtain ⟨S, hS⟩ := W.N_fg T
  refine ⟨⟨S, top_le_iff.1 fun y _ => ?_⟩⟩
  refine (W.N_base T hT).inductionOn y (fun y => y ∈ Submodule.span W.EE (S : Set (W.DD T)))
    (Submodule.zero_mem _) (fun m => ?_) (fun e y hy => Submodule.smul_mem _ e hy)
    (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  have hm : (m : W.DD T) ∈ Submodule.span (LetA O n) (S : Set (W.DD T)) := by rw [hS]; exact m.2
  exact Submodule.span_le_restrictScalars (LetA O n) W.EE (S : Set (W.DD T)) hm

theorem phii_basis (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    {d : ℕ} (β : Module.Basis (Fin d) W.EE (W.DD T)) (c : Fin d → W.EE)
    (h : ∑ t, c t • W.φD T (β t) = 0) : c = 0 := by
  have hfin := phii_finite W T hT
  let L : (Fin d → W.EE) →ₗ[W.EE] W.DD T := Fintype.linearCombination W.EE fun t => W.φD T (β t)
  have hL : ∀ c, L c = ∑ t, c t • W.φD T (β t) := fun c => Fintype.linearCombination_apply _ _ _
  have hφ : ∀ y, W.φD T y ∈ LinearMap.range L := by
    intro y
    refine ⟨fun t => W.φE (β.equivFun y t), ?_⟩
    rw [hL]
    conv_rhs => rw [← β.sum_equivFun y, map_sum]
    exact Finset.sum_congr rfl fun t _ => (W.φD_smul T _ _).symm
  have hN : ∀ m ∈ W.N T, m ∈ LinearMap.range L := by
    intro m hm
    obtain ⟨k, hk⟩ := W.N_φinv T m hm
    have h1 : Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) ≤
        (LinearMap.range L).restrictScalars (LetA O n) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, _, rfl⟩
      exact hφ y
    have h2 : W.Q ^ k • m ∈ LinearMap.range L := h1 hk
    rw [← algebraMap_smul W.EE, map_pow] at h2
    obtain ⟨u, hu⟩ := (liftb_Q_unit W).pow k
    rw [← hu] at h2
    have h3 := (LinearMap.range L).smul_mem ((u⁻¹ : W.EEˣ) : W.EE) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  have hsurj : Function.Surjective L := by
    intro y
    exact (W.N_base T hT).inductionOn y (fun y => y ∈ LinearMap.range L)
      (Submodule.zero_mem _) (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy)
      (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  have hinj : Function.Injective (L ∘ₗ β.equivFun.toLinearMap) :=
    OrzechProperty.injective_of_surjective_endomorphism _
      (hsurj.comp β.equivFun.surjective)
  have h0 : (L ∘ₗ β.equivFun.toLinearMap) (β.equivFun.symm c) = 0 := by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hL, h]
  have h4 := hinj (h0.trans (map_zero _).symm)
  have h5 := congrArg β.equivFun h4
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

theorem phii_DD (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (x : Fin PD.p → W.DD T)
    (h : ∑ k : Fin PD.p, (letπ : LetA O n) ^ (k : ℕ) • W.φD T (x k) = 0) : ∀ k, x k = 0 := by
  rcases subsingleton_or_nontrivial W.EE with hE | hE
  · have := Module.subsingleton W.EE (W.DD T)
    exact fun k => Subsingleton.elim _ _
  have hfin := phii_finite W T hT
  have hfree := (W.DD_free T).1
  let β := Module.finBasis W.EE (W.DD T)
  have hx : ∀ k, W.φD T (x k) = ∑ t, W.φE (β.equivFun (x k) t) • W.φD T (β t) := by
    intro k
    conv_lhs => rw [← β.sum_equivFun (x k), map_sum]
    exact Finset.sum_congr rfl fun t _ => W.φD_smul T _ _
  have h1 : ∑ t, (∑ k : Fin PD.p, (algebraMap (LetA O n) W.EE letπ) ^ (k : ℕ) *
      W.φE (β.equivFun (x k) t)) • W.φD T (β t) = 0 := by
    rw [← h]
    simp_rw [Finset.sum_smul, hx, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul, ← map_pow, algebraMap_smul]
  have h2 := phii_basis W T hT β _ h1
  intro k
  apply β.equivFun.injective
  rw [map_zero]
  funext t
  exact phii_EE W (fun k => β.equivFun (x k) t) (congrFun h2 t) k

theorem PhiLinInj_of (W : LocWach PD LL O v n) [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : PhiLinInj W T :=
  fun _ x _ h => phii_DD W T hT x h

end PhiI3

theorem opnPhiLinInj_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : opnPhiLinInj D HW F := by
  intro l _ K s LL h _ T hT
  have hc : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p K]
    exact phib_OL_complete LL
  exact PhiLinInj_of _ T hT

theorem wach_second_and_result_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) (hJ : opnJumpsQuot D HW F) : WachExponentRecursionAll D HW F ∧ WachResultConstant D HW F 10 :=
  wach_clauses_of_admitted_inj D HW F Cm h hJ (opnPhiLinInj_holds D HW F)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

end Formalism.MainNotions.LiftingTheory
