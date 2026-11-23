import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

instance instTAGWO : IsTopologicalAddGroup (WO S T) := PHeisFC.tagWA T S

theorem eFin_idem : eFin D * eFin D = eFin D :=
  Prod.ext (show (0 : Ainf D.host.F) * 0 = 0 from mul_zero _) (show (1 : Af D.host.F) * 1 = 1 from mul_one _)

theorem symplOH_zero_right (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := symplOH_add_right x (0 : WO S T) 0
  rw [add_zero] at h
  linear_combination -h

theorem cont_dH (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L) {P : WO S T →+ (Fin k → ℝ)} (hPc : Continuous P)
    (hLP : ∀ w, L (P w) = eInf D • w) {n : ℕ} (l : Fin n → Fin k) : Continuous (dH ψ L l f) := by
  obtain ⟨Λ, hΛ, hψΛ⟩ := psi_real ψ hψ
  have hψc : Continuous ψ := hψ.1.1
  obtain ⟨U, hUo, hUf⟩ := hf.level
  rw [continuous_iff_continuousAt]
  intro x0
  set R : (Fin k → ℝ) → ℂ := fun s => dH ψ L l f (x0 + L s)
  have hR : Continuous R := cont_real hΛ hψΛ hL hf x0 l
  set F : WO S T → ℂ := fun y => ψ (-(symplOH S T x0 (eFin D • y))) * R (P y)
  have hLPc : Continuous fun y => L (P y) := hL.1.comp hPc
  have hFc : Continuous F := by
    have he : (fun y : WO S T => eFin D • y) = fun y => y - L (P y) := funext fun y => by
      rw [hLP, eFin_smul_sub]
    have h1 : Continuous fun y : WO S T => symplOH S T x0 (eFin D • y) := by
      have h0 : Continuous fun y : WO S T => eFin D • y := by
        rw [he]; simp_rw [sub_eq_add_neg]; exact continuous_id.add hLPc.neg
      exact (continuous_symplOH_right x0).comp h0
    exact (hψc.comp (continuous_neg.comp h1)).mul (hR.comp hPc)
  have hO : ∀ᶠ y in 𝓝 (0 : WO S T), dH ψ L l f (x0 + y) = F y := by
    have hOo : IsOpen ((U : Set (WO S T)) ∩ (fun y => L (P y)) ⁻¹' U) := hUo.inter (hUo.preimage hLPc)
    have h0 : (0 : WO S T) ∈ (U : Set (WO S T)) ∩ (fun y => L (P y)) ⁻¹' U :=
      ⟨U.zero_mem, by show L (P 0) ∈ U; rw [map_zero, map_zero]; exact U.zero_mem⟩
    filter_upwards [hOo.mem_nhds h0] with y hy
    set u := y - L (P y)
    have huU : u ∈ U := U.sub_mem hy.1 hy.2
    have hue : u = eFin D • y := by simp only [u]; rw [hLP y]; exact eFin_smul_sub y
    have hufin : eFin D • u = u := by rw [hue, smul_smul, eFin_idem]
    have hfu : heisO ψ S T u f = f := hUf u huU ((wo_fin_iff u).mpr hufin)
    have hx : x0 + y = (x0 + L (P y)) + u := by simp only [u]; abel
    rw [hx, dH_smul_const l _ (Gf_fin hL u hufin hfu (x0 + L (P y))) (Gf_smooth hΛ hψΛ hL hf _)]
    have hr : eInf D • L (P y) = L (P y) := (wo_real_iff _).mp (hL.2.1 _)
    simp only [F, R]
    rw [symplOH_add_left, symplOH_real_fin (L (P y)) u hr hufin, add_zero, hue]
  have hF0 : F 0 = dH ψ L l f x0 := by
    simp only [F, R, smul_zero, map_zero, add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have h1 : ContinuousAt (fun y => dH ψ L l f (x0 + y)) 0 :=
    (hFc.continuousAt).congr (hO.mono fun y hy => hy.symm)
  have h2 : ContinuousAt (fun x => x - x0) x0 := by
    simp_rw [sub_eq_add_neg]; exact (continuous_id.add continuous_const).continuousAt
  have h3 := ContinuousAt.comp_of_eq (g := fun y => dH ψ L l f (x0 + y)) h1 h2 (sub_self x0)
  refine h3.congr (Eventually.of_forall fun x => ?_)
  show dH ψ L l f (x0 + (x - x0)) = dH ψ L l f x
  rw [add_sub_cancel]

theorem norm_dH_rat (hψu : ∀ a, ‖ψ a‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {L : (Fin k → ℝ) →+ WO S T} (hs : ∀ x, ContDiff ℝ ∞ (Gf ψ L f x)) {n : ℕ} (l : Fin n → Fin k)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (x : WO S T) :
    ‖dH ψ L l f (ratW T S γ + x)‖ = ‖dH ψ L l f x‖ := by
  rw [dH_smul_const l _ (Gf_rat hf L γ x) (hs x), norm_mul, hψu, one_mul]

end Formalism.IndefR.Eqv

end
