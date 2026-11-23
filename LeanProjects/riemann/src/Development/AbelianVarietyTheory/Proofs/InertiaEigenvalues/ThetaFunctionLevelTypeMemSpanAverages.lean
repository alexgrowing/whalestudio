import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAveragesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDetCharacterFunctionConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite.LiftOp
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levChi_datVt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : GA D (Vc D i)) :
    levChi (Vc D i) (R.βV i) (R.datVt i t) κ = levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  have h := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.datVt i t).P (finE (Vc D i) κ)
  have h1 : Formalism.L2.DIV.ext1 (R.datVt i t).P.H (R.datVt i t).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) κ)) = 1 := by
    unfold Formalism.L2.DIV.ext1; split_ifs with hm
    · have : (⟨_, hm⟩ : (R.datVt i t).P.H) = 1 := Subtype.ext (Subgroup.mem_bot.1 hm)
      rw [this, map_one]
    · rfl
  unfold levChi
  rw [show R.datVt i t = withP (R.datVt i t) (R.datVt i t).P from rfl, h, h1, one_mul]
  rfl

theorem chF_mul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ₁ κ₂ : GA D (Vc D i)}
    (h₁ : finE (Vc D i) κ₁ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (h₂ : finE (Vc D i) κ₂ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ₁ * κ₂) =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₁ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ₂ := by
  unfold levChi
  rw [map_mul, levFn_flag_mul h₁ h₂, Units.val_mul]

theorem parLev_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    finE (Vc D i) 1 ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
  rw [map_one]; exact Subgroup.one_mem _

theorem chF_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have h := chF_mul R i t (parLev_one R i t) (parLev_one R i t)
  rw [mul_one] at h
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (1 : GA D (Vc D i))
  have : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 - 1) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem chF_inv (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (h : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ⁻¹ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ := by
  have hi : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ h
  have e := chF_mul R i t h hi
  rw [mul_inv_cancel, chF_one] at e
  have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  field_simp
  rw [mul_comm]; exact e.symm

theorem conj_mem_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ j : GA D (Vc D i)} (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    (hj : j ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) : κ * j * κ⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
  refine ⟨(GfC (Vc D i)).mul_mem ((GfC (Vc D i)).mul_mem hκG hj.1) ((GfC (Vc D i)).inv_mem hκG), ?_⟩
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2
  have hki : (finE (Vc D i) κ)⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) :=
    Subgroup.inv_mem _ hκ
  show finE (Vc D i) (κ * j * κ⁻¹) ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t)
  rw [map_mul, map_mul, map_inv]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hκ hj2.1) hki, ?_⟩
  have h1 : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) j) = 1 := Subgroup.mem_bot.1 hj2.2
  rw [Formalism.L2.DIV.rTup_mul (Subgroup.mul_mem _ hκ hj2.1) hki, Formalism.L2.DIV.rTup_mul hκ hj2.1, h1,
    Formalism.L2.DIV.rTup_inv hκ, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem typeVec_move (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {κ : GA D (Vc D i)}
    (hκG : κ ∈ GfC (Vc D i))
    (hκ : finE (Vc D i) κ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) : TypeVec R i t (R.ωP i t (κ⁻¹, 1) φ) := by
  refine ⟨(hP i t).datum.om_pres _ φ hφ.1, fun j hj => ?_⟩
  have hc := conj_mem_lev R i t hκG hκ hj
  have e : ((j, 1) : GA D (Vc D i) × GA D (Wc D i)) * (κ⁻¹, 1) = (κ⁻¹, 1) * (κ * j * κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hj2 : finE (Vc D i) j ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hj.2.1
  have hki : finE (Vc D i) κ⁻¹ ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [map_inv]; exact Subgroup.inv_mem _ hκ
  have hchi : levChi (Vc D i) (R.βV i) (R.datVt i t) (κ * j * κ⁻¹) = levChi (Vc D i) (R.βV i) (R.datVt i t) j := by
    rw [levChi_datVt, levChi_datVt, chF_mul R i t (by rw [map_mul]; exact Subgroup.mul_mem _ hκ hj2) hki,
      chF_mul R i t hκ hj2, chF_inv R i t hκ]
    have hne := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
    field_simp
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hφ.2 _ hc, map_smul, hchi]

theorem levG_flag1 (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) = levG (Vc D i) (R.βV i) (R.datVt i t) := rfl

theorem pi_lift_indep (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hP : R.FullP) {g0 : Formalism.L2.DIV.G0 (R.datVt i t).Pg (R.datVt i t).r}
    {κ κ' : GA D (Vc D i)} (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ')
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : TypeVec R i t φ) :
    (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ')⁻¹ • R.ωP i t (κ'⁻¹, 1) φ =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.ωP i t (κ⁻¹, 1) φ := by
  have hd : κ⁻¹ * κ' ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := by
    have h0 := lift_div_mem hκ hκ'
    rw [levG_flag1] at h0
    exact h0
  have hdi : (κ⁻¹ * κ')⁻¹ ∈ levG (Vc D i) (R.βV i) (R.datVt i t) := Subgroup.inv_mem _ hd
  have hm := typeVec_move R i t hP hκ.1 hκ.2.1 hφ
  have e : ((κ'⁻¹, 1) : GA D (Vc D i) × GA D (Wc D i)) = ((κ⁻¹ * κ')⁻¹, 1) * (κ⁻¹, 1) := by
    simp only [Prod.mk_mul_mk, mul_one]; congr 1; group
  have hdp : finE (Vc D i) (κ⁻¹ * κ') ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hd.2.1
  have hc : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ' =
      levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ') := by
    rw [← chF_mul R i t hκ.2.1 hdp, mul_inv_cancel_left]
  rw [e, map_mul, Module.End.mul_apply, hm.2 _ hdi, levChi_datVt, chF_inv R i t hdp, hc, smul_smul]
  congr 1
  have h1 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) κ
  have h2 := levChi_ne_zero (β := R.βV i) (flagL (R.datVt i t)) (κ⁻¹ * κ')
  field_simp

end GlobalTheory.DownLift.GenFinite.LiftOp

namespace GlobalTheory.DownLift.GenFinite
open LiftOp

theorem cleanSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ ∧ GlobalTheory.DownLift.GenFinite.Clean R i t φ} ∪ GlobalTheory.DownLift.GenFinite.AvgIm R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hf
  by_cases hex : ∃ κ : G → GA D (Vc D i), IsLifts R i t κ
  swap
  · exact Submodule.subset_span (Or.inl ⟨hf, fun PP a _ tr ε _ κ hκ => absurd ⟨κ, hκ⟩ hex⟩)
  obtain ⟨κ, hκ⟩ := hex
  let S : Submodule ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    { carrier := {φ | TypeVec R i t φ}
      add_mem' := fun {a b} ha hb => ⟨theta_add ha.1 hb.1, fun j hj => by rw [map_add, ha.2 j hj, hb.2 j hj, smul_add]⟩
      zero_mem' := ⟨by simpa using theta_smul (0 : ℂ) hf.1, fun j hj => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c a ha => ⟨theta_smul c ha.1, fun j hj => by
        rw [map_smul, ha.2 j hj, smul_comm]⟩ }
  have hSm : ∀ φ, φ ∈ S ↔ TypeVec R i t φ := fun _ => Iff.rfl
  let π : G → Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1)
  have hπ : ∀ g φ, π g φ = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹ • R.ωP i t ((κ g)⁻¹, 1) φ :=
    fun _ _ => rfl
  have hS : ∀ g, ∀ v ∈ S, π g v ∈ S := by
    intro g v hv
    rw [hπ]; exact S.smul_mem _ ((hSm _).2 (typeVec_move R i t hP (hκ g).1 (hκ g).2.1 ((hSm _).1 hv)))
  have hlift1 : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG 1) 1 :=
    ⟨Subgroup.one_mem _, parLev_one R i t, by rw [map_one, Formalism.L2.DIV.rTup_one, map_one]; rfl⟩
  have h1 : ∀ v ∈ S, π 1 v = v := by
    intro v hv
    rw [hπ, pi_lift_indep R i t hP hlift1 (hκ 1) ((hSm _).1 hv), chF_one, inv_one, one_smul, inv_one,
      ← Prod.one_eq_mk, map_one]
    rfl
  have hmul : ∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v) := by
    intro g h v hv
    have hl : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG (g * h)) (κ g * κ h) := by
      refine ⟨(GfC (Vc D i)).mul_mem (hκ g).1 (hκ h).1, ?_, ?_⟩
      · rw [map_mul]; exact Subgroup.mul_mem _ (hκ g).2.1 (hκ h).2.1
      · rw [map_mul, Formalism.L2.DIV.rTup_mul (hκ g).2.1 (hκ h).2.1, (hκ g).2.2, (hκ h).2.2, map_mul]; rfl
    rw [hπ, pi_lift_indep R i t hP hl (hκ (g * h)) ((hSm _).1 hv), hπ, hπ, map_smul, smul_smul,
      ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, chF_mul R i t (hκ g).2.1 (hκ h).2.1, _root_.mul_inv_rev,
      _root_.mul_inv_rev]
  let C : Set (G → ℂ) := {c | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ),
    (ε = 1 ∨ ε = -1) ∧ c = mirC R i PP a tr ε}
  have hC : ∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C := by
    rintro c ⟨PP, a, ha, tr, ε, hε, rfl⟩ x
    obtain ⟨a', ha', he⟩ := GlobalTheory.T.mirabolicDetCharacterFunction_conj D G Pl0 T A Ks R i PP a ha tr ε x
    exact ⟨PP, a', ha', tr, ε, hε, funext he⟩
  have havg : ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ) (κ' : G → GA D (Vc D i)), IsLifts R i t κ' →
      ∀ w ∈ S, avgW R i t PP a tr ε κ' w = ∑ g, mirC R i PP a tr ε g • π g w := by
    intro PP a tr ε κ' hκ' w hw
    unfold avgW
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hπ, ← pi_lift_indep R i t hP (hκ g) (hκ' g) ((hSm _).1 hw), smul_smul]
  have key := GlobalTheory.T.mem_span_annihilated_union_class_averages S π hS h1 hmul C hC f hf
  refine Submodule.span_mono ?_ key
  rintro w (⟨hwS, hw⟩ | ⟨c, ⟨PP, a, ha, tr, ε, hε, rfl⟩, w', hw'S, rfl⟩)
  · exact Or.inl ⟨hwS, fun PP a ha tr ε hε κ' hκ' => by
      rw [havg PP a tr ε κ' hκ' w hwS]; exact hw _ ⟨PP, a, ha, tr, ε, hε, rfl⟩⟩
  · exact Or.inr ⟨PP, a, ha, tr, ε, hε, κ, hκ, w', hw'S.1, (havg PP a tr ε κ hκ w' hw'S).symm⟩

end GlobalTheory.DownLift.GenFinite
