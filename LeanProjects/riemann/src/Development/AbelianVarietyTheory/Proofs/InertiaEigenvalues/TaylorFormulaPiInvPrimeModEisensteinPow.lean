import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HatOfInvariantSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

section Scal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem galOD_crisToOD (g : GQ l) (x : OCr l O) :
    galOD O g (crisToOD l O x) = crisToOD l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.crisP_unique_equivariant l (crisP l) (isCrisP_crisP l)).2.1 g w).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isUnit_natCast_OD {n : ℕ} (hn : n ≠ 0) : IsUnit (n : OD l O) := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (OD l O)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul (isUnit_l_OD.pow _)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

variable (O K) in

theorem dvd_toOD_mu (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) :
    ϖ.iAl O K (EIn l e _) ∣ toOD l O (1 ⊗ₜ ϖ.mu g) := by
  have hξ : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  have hmem : ϖ.mu g ∈ Ideal.span {ϖ.ev 1 (eis l 1 e)} := by
    rw [ϖ.span_ev_eis 1]
    exact ϖ.theta_mu (ϖ.gal_pi a g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨1 ⊗ₜ ainfToBdRp l c, ?_⟩
  rw [hξ, ← hc]
  change (1 : O) ⊗ₜ[ℤ_[l]] ainfToBdRp l (c * _) = _
  rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]

variable (O) in

theorem crisToOD_muDiv (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    crisToOD l O (ϖ.muDiv a O g i) = toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) := by
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  have h2 := congrArg (crisToOD l O) h1
  rw [map_mul, map_natCast, map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, ← toOCr_tmul, crisToOD_toOCr] at h2
  have hu := isUnit_natCast_OD (l := l) (O := O) i.factorial_ne_zero
  rw [← h2, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl

variable (K) in

theorem taylor_S_mod (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (s : S O K e) (R : ℕ) :
    ϖ.iAl O K (EIn l e _) ^ R ∣ galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
  obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ R
  refine GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ R _ fun k => ?_
  obtain ⟨M₀, hM₀⟩ := ϖ.taylor_S a O K g s (N + k)
  obtain ⟨z, hz⟩ := hM₀ (max M₀ R) (le_max_left _ _)
  obtain ⟨y, hy⟩ := hN z
  refine ⟨y, ?_⟩
  have hz' := congrArg (crisToOD l O) hz
  simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, crisToOD_muDiv] at hz'
  rw [← galOD_crisToOD, ← Finset.sum_range_add_sum_Ico _ (le_max_right M₀ R)] at hz'
  have key : galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) - (l : OD l O) ^ k * toOD l O y =
      (l : OD l O) ^ k * ((l : OD l O) ^ N * crisToOD l O z - toOD l O y) +
        ∑ i ∈ Finset.Ico R (max M₀ R), toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    linear_combination hz'
  rw [key]
  refine dvd_add (Dvd.dvd.mul_left hy _) (Finset.dvd_sum fun i hi => ?_)
  have hi' : R ≤ i := (Finset.mem_Ico.1 hi).1
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ hi').trans
    (pow_dvd_pow_of_dvd (dvd_toOD_mu O K ϖ g) i)) _) _

end Scal

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

section Scal2

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] [CompleteSpace K]

theorem taylor_invL_mod (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {f : K⟦X⟧}
    (hf : f ∈ invL l (S O K e)) (R : ℕ) :
    galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i *
      Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f)) ∈
      Ideal.span {ϖ.iAl O K (EIn l e _) ^ R} := by
  have hiHat : ∀ (f' : K⟦X⟧) (hf' : f' ∈ invL l (S O K e)), ϖ.iHat O K (hatR O f') = ϖ.iSD O K ⟨f', hf'⟩ :=
    fun f' hf' => (GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ ⟨f', hf'⟩ (hatR O f') (by
      rw [hatR_of_mem (O := O) (invL_S_le_Rpi l e hf')]
      exact hat_coe_Rpi l e ⟨f', invL_S_le_Rpi l e hf'⟩)).symm
  obtain ⟨n, hn⟩ := hf
  have hC : ((l : S O K e) : K⟦X⟧) ^ n = C ((l : K) ^ n) := by simp
  have hlin : ∀ (i : ℕ) (x : K⟦X⟧), ((l : S O K e) : K⟦X⟧) ^ n * descN K i x =
      descN K i (((l : S O K e) : K⟦X⟧) ^ n * x) := fun i x => by
    rw [hC, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  have hdesc : ∀ i : ℕ, descN K i f ∈ invL l (S O K e) := fun i =>
    ⟨n, by rw [hlin]; exact descN_mem_S e i hn⟩
  set s : S O K e := ⟨_, hn⟩ with hs
  have e0 : (l : OD l O) ^ n * ϖ.iSD O K ⟨f, ⟨n, hn⟩⟩ = crisToOD l O (ϖ.iS O K s) := by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨f, ⟨n, hn⟩⟩ = algebraMap (S O K e) (invL l (S O K e)) s :=
      Subtype.ext (by simp [s])
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K s.2 _
  have ei : ∀ i : ℕ, (l : OD l O) ^ n * ϖ.iSD O K ⟨descN K i f, hdesc i⟩ =
      crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := fun i => by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨descN K i f, hdesc i⟩ =
        algebraMap (S O K e) (invL l (S O K e)) ⟨descN K i s, descN_mem_S e i s.2⟩ :=
      Subtype.ext (by
        change ((l : K⟦X⟧)) ^ n * descN K i f = descN K i (((l : S O K e) : K⟦X⟧) ^ n * f)
        rw [← hlin]
        simp)
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K (descN_mem_S e i s.2) _
  have g0 := congrArg (galOD O g) e0
  rw [map_mul, map_pow, map_natCast] at g0
  have key : (l : OD l O) ^ n * (galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f))) =
      galOD O g (crisToOD l O (ϖ.iS O K s)) -
        ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    rw [hiHat f ⟨n, hn⟩, ← g0, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hiHat _ (hdesc i), ← ei i]
    ring
  have hW := Ideal.mem_span_singleton.2 (taylor_S_mod K ϖ g s R)
  rw [← key] at hW
  exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_l_OD.pow n)).1 hW

theorem galOD_idem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  change galOD O g (toOD l O (constA t _)) = toOD l O (constA t _)
  rw [← crisToOD_toOCr, galOD_crisToOD, galOCr_toOCr, galOA_constA t h]

end Scal2

theorem taylor_iD_mod_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ g hg f hf R
  let g' : ↥(GK (ϖ.field a)) := ⟨g, hg⟩
  have hED : ED K t ϖ = ϖ.iAl O K (EIn l e _) := (glue_const _ _ _).trans (ϖ.iHat_ofAl O K _)
  rw [hED]
  have hfix : ∀ τ, galOD O g (idem (constD t) τ) = idem (constD t) τ := galOD_idem t ϖ g'
  have hsplit : galOD O g (ϖ.iD t K (fun τ => hatR O (f τ))) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) =
      ∑ τ, idem (constD t) τ * (galOD O g (ϖ.iHat O K (hatR O (f τ))) - ∑ i ∈ Finset.range R,
        toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          ϖ.iHat O K (hatR O (descN K i (f τ)))) := by
    simp only [PiSys.iD, glue_apply, map_sum, map_mul, hfix, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (taylor_invL_mod t ϖ g' (hf τ) R)

end GlobalTheory.GalStep
