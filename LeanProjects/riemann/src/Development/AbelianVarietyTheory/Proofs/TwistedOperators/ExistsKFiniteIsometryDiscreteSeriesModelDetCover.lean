import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.KFiniteTie

open GlobalTheory.CoverModel GlobalTheory.Chain.RealIt.LocalFromCover
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (toFrame)

section Semi

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {cj : Bool} {U : H → H'}

theorem cjc_ofReal (cj : Bool) (r : ℝ) : cjc cj (r : ℂ) = r := by
  cases cj <;> simp [cjc]

theorem exists_real (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hb : Function.Bijective U) (hn : ∀ x, ‖U x‖ = ‖x‖) : ∃ L : H ≃ₗᵢ[ℝ] H', ∀ x, L x = U x := by
  let L₀ : H →ₗᵢ[ℝ] H' :=
    { toFun := U
      map_add' := hadd
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, hs, cjc_ofReal, Complex.coe_smul, RingHom.id_apply]
      norm_map' := hn }
  exact ⟨LinearIsometryEquiv.ofSurjective L₀ hb.2, fun _ => rfl⟩

theorem inner_map (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hn : ∀ x, ‖U x‖ = ‖x‖) (w x : H) : ⟪U w, U x⟫_ℂ = cjc cj ⟪w, x⟫_ℂ := by
  have hre : ∀ w x : H, (⟪U w, U x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := fun w x => by
    have h1 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) (U w) (U x)
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) w x
    rw [← hadd, hn, hn, hn, ← h2] at h1
    exact h1
  have h1 := hre w x
  have h2 := hre w (Complex.I • x)
  rw [hs, inner_smul_right, inner_smul_right] at h2
  cases cj
  · apply Complex.ext <;> simp_all [cjc]
  · apply Complex.ext
    · simp only [cjc, if_true, Complex.conj_re]
      exact h1
    · simp only [cjc, if_true, Complex.conj_im] at h2 ⊢
      simpa using h2

end Semi

theorem isFormIso_phi {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) :
    IsFormIso ε (phi br e) := by
  cases br
  · exact isFormIso_plainMat h
  · exact isFormIso_barMat h

theorem exists_kTie : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  intro D V S M τ p q T R lam c br cj e m U hpar hord hm hT hhi
  have hφ := isFormIso_phi hord.1 br
  obtain ⟨L, hL⟩ := exists_real hT.add hT.smul hT.bij hT.norm
  have hr : ∀ v : kfin M τ, ∃ y, R.ι y = U v := by
    rintro ⟨v, hv⟩
    change U v ∈ LinearMap.range R.ι
    induction hv using Submodule.span_induction with
    | mem x hx => exact (hT.kfin x).1 hx
    | zero => rw [← hL, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hT.add]; exact add_mem hx hy
    | smul z x _ hx => rw [hT.smul]; exact Submodule.smul_mem _ _ hx
  choose u hu using hr
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast hm
  have hgrp : ∀ (g : T.G) (x : M.H τ), U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) =
      ((T.sq g : ℂˣ) : ℂ) ^ m • R.U.π g (U x) := fun g x => by
    rw [hT.grp, smul_smul, ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
  refine ⟨u, hpar, hord, fun x y => R.ι_inj ?_, fun z x => R.ι_inj ?_, ⟨fun x y h => ?_, fun y => ?_⟩, ?_,
    fun Z hZ v v' => ?_, fun v => hhi _ _ (hu v).symm, fun m' hm' g v w => ?_⟩
  · rw [map_add, hu, hu, hu, Submodule.coe_add, hT.add]
  · rw [map_smul, hu, hu, Submodule.coe_smul, hT.smul]
  · exact Subtype.ext (hT.bij.1 (by rw [← hu, ← hu, h]))
  · obtain ⟨x, hx⟩ := hT.bij.2 (R.ι y)
    exact ⟨⟨x, Submodule.subset_span ((hT.kfin x).2 ⟨y, hx.symm⟩)⟩, R.ι_inj (by rw [hu]; exact hx)⟩
  · change (fun Z => toFrame M τ (phi br e Z)) '' _ = _
    rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) (phi br e)]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := hφ.bij.2 Y
    rw [hφ.bij.1.mem_set_image, ← hφ.mem_lie]
    rfl
  · have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ (u v))
    have h2 : HasDerivAt (fun t : ℝ => L (M.rep τ (NormedSpace.exp (t • phiFr (M.fr τ) br e Z)) (v : M.H τ)))
        (R.ι (R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v)) 0 := by
      convert h1 using 1
      · funext t
        have h3 := rep_exp M τ (phi br e Z) t
        rw [hL, show phiFr (M.fr τ) br e Z = toFrame M τ (phi br e Z) from rfl, h3, hφ.exp,
          ← T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), hgrp, hu]
      · rw [hmC, show 2 * (c : ℂ) * (Z.trace / 2) = c * Z.trace by ring]
        simp [T.expt_zero]
    constructor
    · intro h
      have h3 := L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
      refine R.ι_inj ?_
      rw [hu, ← hL]
      exact h3.unique h2
    · intro h
      rw [← h, hu, ← hL] at h2
      have h3 := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      unfold VecDer
      convert h3 using 1
      · funext t; simp
      · simp
  · obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
    rw [← inner_map hT.add hT.smul hT.norm, hgrp, inner_smul_right, hu, hu]

end GlobalTheory.ArchRec.KFiniteTie

end
