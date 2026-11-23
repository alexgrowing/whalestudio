import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointRepsConjugateHalfModLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateHalfVacuumTranslateSumIsThetaFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumFixedByFlippedLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumConjugateHalfNeZeroStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1600000 in
open MeasureTheory GlobalTheory.VacUnique GlobalTheory.FockCompare in

theorem eq_smul_vacuum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hlat' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') : ∃ a : ℂ, f' = a • f := by
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem moved_vacuum_eq_mean : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → ∃ (lam : ℂ) (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ Y.card = flipIdx V W T m ∧ om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z hT hm hcop hmT hz hmt
  obtain ⟨Y, hY1, hY2, hY3, hYc⟩ := GlobalTheory.T.exists_levelPoint_reps_conjugate_half_mod_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  set G := ∑ y ∈ Y, heisO ψ V W y f₀ with hG
  obtain ⟨hGth, hGf⟩ := GlobalTheory.T.conjugateHalf_vacuum_translate_sum_isThetaFockVacuum D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y fun y hy => (hY1 y hy).1
  obtain ⟨hfix2, hfixh⟩ := GlobalTheory.T.vacuum_translate_sum_fixed_by_flipped_lattice D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hne := GlobalTheory.T.vacuum_translate_sum_conjugateHalf_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hW := hP.1.weil

  have hmove : ∀ u : WO V W, actO V W z 1 (flipElt eT m • u) = u := by
    intro u
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W z 1 u
    have e2 : actO V W z⁻¹ 1⁻¹ u = flipElt eT m • u := by
      simp only [actO, inv_inv, hmt]
      have h1 : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ = 1 := by
        rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
      rw [h1, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [← e2]; exact e
  set H := om (z, 1) G with hH
  have hHth : IsThetaFunO ψ V W H := hW.om_pres _ _ hGth
  have hHh : ∀ u, heisO ψ V W u H = om (z, 1) (heisO ψ V W (flipElt eT m • u) G) := by
    intro u
    rw [hW.om_heis z 1 _ G hGth, hmove]
  have hzf : z ∈ GfC V := hz
  have hHf : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) H := by
    intro τ z'
    have c1 : compAt θ τ (Formalism.L2.Theta.mt W (1 : GA D W)) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ W (one_mem _) τ
    have c2 : compAt θ τ (Formalism.L2.Theta.mt V z⁻¹) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V (inv_mem hzf) τ
    have e1 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ z' hGth
    have e2 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ) z') hGth
    rw [c1, c2, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have h0 := hGf τ z'
    unfold annih at h0 ⊢
    rw [hH, ← e1, ← e2, ← map_smul, ← map_add, h0, map_zero]
  have hHl : IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) H := by
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [hHh, hfix2 u hu]
    · rw [hHh, hfixh e he u hu hh]
  obtain ⟨c, hc⟩ := eq_smul_vacuum hP.2.2.2.2.2.2.2.2.1 hP.1.inf (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hP.1.std τ)
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2 hHth hHl hHf
  have hback : om (z⁻¹, 1) H = G := by
    rw [hH, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hGc : G = c • om (z⁻¹, 1) f₀ := by rw [← hback, hc, map_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hG, hGc, zero_smul])
  refine ⟨c⁻¹, Y, hY1, hY2, hYc, ?_⟩
  rw [← hG, hGc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.LevelSeries
