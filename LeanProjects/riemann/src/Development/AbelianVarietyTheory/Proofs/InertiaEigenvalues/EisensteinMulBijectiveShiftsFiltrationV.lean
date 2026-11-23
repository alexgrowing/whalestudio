import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.PiSys

theorem iD_const_Ehat_eq_tmul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ϖ.iD t K (fun _ => Ehat O K l e) = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
  rw [iD, glue_const, Ehat, iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))

end GlobalTheory.BKReal.PiSys

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime]

theorem ev_eis_assoc_xi {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {ε : Per.Fl l} (hE : GlobalTheory.MemLoc.IsEps ε) :
    (∃ c : Per.Ainf l, c * GlobalTheory.MemLoc.xi ε = ϖ.ev a (eis l a e)) ∧
      ∃ c' : Per.Ainf l, c' * ϖ.ev a (eis l a e) = GlobalTheory.MemLoc.xi ε := by
  have hsp := (ϖ.span_ev_eis a).trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  refine ⟨Ideal.mem_span_singleton'.1 ?_, Ideal.mem_span_singleton'.1 ?_⟩
  · rw [← hsp]; exact Ideal.mem_span_singleton_self _
  · rw [hsp]; exact Ideal.mem_span_singleton_self _

theorem isUnit_and_mem_FilD_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Per.BdR l), x ∈ Per.FilD l j ↔
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ Per.FilD l (j + 1) := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := ev_eis_assoc_xi (a := a) ϖ hE
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hU : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hα : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c) * (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc]
  have hβ : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) = (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc']
  refine ⟨IsUnit.of_mul_eq_one
    (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) ?_, ?_⟩
  · rw [← mul_assoc, mul_comm _ (algebraMap _ _ (GlobalTheory.MemLoc.aDp l c')), hβ, Units.mul_inv]
  intro j x
  rw [GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, ← hUdef]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c * w, ?_⟩
    rw [hα, _root_.zpow_add_one, Units.val_mul, map_mul]
    ring
  · rintro ⟨w, hw⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c' * w, ?_⟩
    have h2 : (U : Per.BdR l) * x = (U : Per.BdR l) * (((U ^ j : (Per.BdR l)ˣ) : Per.BdR l) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c' * w)) := by
      calc (U : Per.BdR l) * x = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x) := by
              rw [← mul_assoc, hβ]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (((U ^ (j + 1) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w) := by rw [hw]
        _ = _ := by rw [_root_.zpow_add_one, Units.val_mul, map_mul]; ring
    exact U.isUnit.mul_left_cancel h2

variable {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

theorem isUnit_and_mem_Fil_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (K : FinExt l) :
    IsUnit (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔
        GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ (Pl.PD K).Fil (j + 1) := by
  obtain ⟨hu, hF⟩ := isUnit_and_mem_FilD_iff (l := l) (a := a) ϖ
  have hc : Td.eD (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) :=
    RingEquiv.apply_symm_apply _ _
  refine ⟨?_, fun j x => ?_⟩
  · have := hu.map (Td.eD.symm : Per.BdR l →+* Pl.R.BdR)
    rw [← hc] at this
    simpa using this
  · rw [Td.fil, Td.fil, map_mul, hc]
    exact hF j _

section Abstract

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K : FinExt l) (j k : ℤ) (g : Pl.R.BdR →ₗ[ℚ_[l]] Pl.R.BdR)
    (hg : ∀ b ∈ (Pl.PD K).Fil j, g b ∈ (Pl.PD K).Fil k) (x : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hx : x ∈ FilV (Pl.PD K) (LL := LL) (V := V) j) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g x ∈ FilV (Pl.PD K) (LL := LL) (V := V) k := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add]; exact Submodule.add_mem _ hy hz

theorem map_mulLeft_comp (r s : Pl.R.BdR) (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] r)
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] s) x) =
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (r * s)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp [mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_mulLeft_one (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (1 : Pl.R.BdR)) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp
  | add y z hy hz => simp only [map_add, hy, hz]

end Abstract

end GlobalTheory.BKReal.EhatShift

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem bijective_and_mem_FilV_iff_of_mul (K : FinExt l) (ξ : Pl.R.BdR) (hu : IsUnit ξ)
    (hF : ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔ ξ * x ∈ (Pl.PD K).Fil (j + 1))
    (f : V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR) (hf : ∀ v c, f (v ⊗ₜ[ℚ_[l]] c) = v ⊗ₜ[ℚ_[l]] (ξ * c)) :
    Function.Bijective f ∧ ∀ (y : V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ),
      y ∈ FilV (Pl.PD K) (LL := LL) (V := V) j ↔ f y ∈ FilV (Pl.PD K) (LL := LL) (V := V) (j + 1) := by
  have hAM : ∀ y, f y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] ξ) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => rw [hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  have hl : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (f y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.val_inv_mul, map_mulLeft_one]
  have hr : ∀ y, f (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.mul_val_inv, map_mulLeft_one]
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨_, hl, hr⟩, fun y j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hAM]
    exact map_mem_FilV K j (j + 1) _ (fun b hb => (hF j b).1 hb) y h
  · have := map_mem_FilV K (j + 1) j
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (fun b hb => by
        rw [hF j, LinearMap.mulLeft_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
        exact hb) _ h
    rwa [hl] at this

end GlobalTheory.BKReal.EhatShift

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  intro l _ a e _ _ ϖ LL _ _ T Pl AI Td A hA
  rw [GlobalTheory.BKReal.PiSys.iD_const_Ehat_eq_tmul l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ]
  obtain ⟨hu, hF⟩ := GlobalTheory.BKReal.EhatShift.isUnit_and_mem_Fil_iff Td (a := a) ϖ (Formalism.MainNotions.ElementDenominator.qlExt l)
  refine GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff_of_mul _ _ hu hF _ fun v c => ?_
  rw [hA]
  simp
