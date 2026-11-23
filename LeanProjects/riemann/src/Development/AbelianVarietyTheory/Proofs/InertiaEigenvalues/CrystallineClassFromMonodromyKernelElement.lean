import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHomStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelLatticeMapKilledByPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentUnitLatticeDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLiftStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTripleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTripleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionClassEqLPowSmulGaloisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.ExtClass

theorem lift_phi_sub {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]
    [DecidableEq μ] {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    {D₂ : BKDat O K l e a μ η H} (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    {x : Vec K a κ} (hx : x ∈ D₁.Minv) (hG : G.app (D₁.phi x - x) = 0) :
    ∃ y ∈ D₀.Y, F.app y = D₁.phi x - x ∧ D₀.Mon y = 0 := by
  have hL : D₁.phi x ∈ D₁.L := D₁.phi_mem_L hx.1
  have hM : E K l e ^ η • (D₁.phi x - x) ∈ D₁.M := by
    rw [smul_sub]
    exact sub_mem (D₁.upper _ hL) (D₁.M.smul_mem (EIn l e (A O K) ^ η) hx.1)
  have hG0 : G.app (E K l e ^ η • (D₁.phi x - x)) = 0 := by rw [map_smul, hG, smul_zero]
  obtain ⟨w, hw, hFw⟩ := (hex.exact _ hM).1 hG0
  have hu : IsUnit (E K l e ^ η) := (isUnit_E l e).pow η
  set y₀ := Ezpow K l e (-(η : ℤ)) • w with hy₀def
  have hE : E K l e ^ η • y₀ = w := by
    rw [hy₀def, smul_smul, E_pow_mul_Ezpow_neg, one_smul]
  have hFy₀ : F.app y₀ = D₁.phi x - x := by
    refine (hu.smul_left_cancel).1 ?_
    rw [← map_smul, hE]
    exact hFw
  have hy₀ : y₀ ∈ D₀.EM η := by
    rw [mem_divE, hE]
    exact hw
  have hinj : ∀ v ∈ D₀.EM η, F.app v = 0 → v = 0 := fun v hv h =>
    (hu.smul_left_cancel).1 (by
      rw [smul_zero]
      exact hex.inj _ hv (by rw [map_smul, h, smul_zero]))
  have hinv2 : ∀ g, D₁.desc.act g (D₁.phi x - x) = D₁.phi x - x := fun g => by
    rw [map_sub, D₁.desc.act_phi, hx.2 g]
  refine ⟨y₀, ⟨hy₀, fun g => ?_⟩, hFy₀, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (D₀.desc.act_mem_EM g hy₀) hy₀) ?_
    rw [map_sub, F.app_act, hFy₀, hinv2, sub_self]
  · refine (GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι κ μ η H D₀ D₁ D₂ F G hex).2.2.1 ?_
    rw [map_zero, Hom.onPol_Mon, hFy₀, PhiMod.Mon_phi_sub,
      (D₁.cls_eq_zero_iff).2 (D₁.EN_mem_Man (D₁.M_le_Man hx.1)), neg_zero]

end GlobalTheory.BKGal.ExtClass

namespace GlobalTheory.BKGal.ExtClass

theorem xi_red_of_phi_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {u : Vec K a ι} (hu : P.phi u = u) : P.xi (red u) = u := by
  have := P.raises_phi.eq_zero (α := Unit) (σ := id) Function.surjective_id
    (δ := fun _ => u - P.xi (red u)) (fun _ => by rw [mem_uPow_one, map_sub, PhiMod.red_xi, sub_self])
    (fun _ => by rw [map_sub, hu, PhiMod.phi_xi, ← PhiMod.red_phi, hu]) ()
  exact (sub_eq_zero.1 this).symm

set_option maxHeartbeats 4000000 in

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  intro hBS hFB l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hN T hT Pk c hc
  have hl2 : l ≠ 2 := by
    have h1 := hN.large
    have h2 := hN.two_le
    rintro rfl
    have : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left h2 3
    omega
  obtain ⟨hUnit, hExt⟩ := GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps hFB l a e ϖ LL Pl AI hStd Sig U hN.zero_mem_Sig hN.zero_mem_U
  obtain ⟨Tp, f, g, v, hfg, hv, hgv, hcv, hTp⟩ := hExt T hT c hc
  obtain ⟨Pp, hPp⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U Tp hTp
  obtain ⟨Pu, hPu⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U _ hUnit
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T Tp Pk Pp f
  have hG' := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H Tp (unitLat (Gl l) : QLat LL) Pp Pu g
  obtain ⟨G, hG⟩ := hG'
  have hex : IsExactTriple F.toHom G.toHom :=
    GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL _ _ _ Pk.D.toPhiMod Pp.D.toPhiMod Pu.D.toPhiMod T Tp (unitLat (Gl l) : QLat LL) Pk.R.I Pp.R.I Pu.R.I f g
      F.toHom G.toHom hfg hF hG
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hN.frob_mem, hN.zero_mem_Sig, hN.card_Sig, hN.two_le, hN.range_U, hN.zero_mem_U, hN.card_U, hN.one_le,
      hN.lt, hN.large⟩
  have hK := GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) (Fin Pu.n) Sig U N η H hB Pp.D Pu.D hPp
    hPu.chars_subset G hex.finiteLength
  obtain ⟨u, x, hx1, hu, hφu, hux⟩ := GlobalTheory.T.breuilKisinDescent_unitLattice_datum hBS l a e ϖ LL η H Pu
  obtain ⟨x₂, hx₂, hGx₂⟩ := hK.2.2.2.1 u.1 hu
  have hG0 : G.app (Pp.D.phi x₂ - x₂) = 0 := by
    rw [map_sub, G.toHom.app_phi, hGx₂, map_nsmul, hφu, sub_self]
  obtain ⟨y, hy, hFy, hMon⟩ := lift_phi_sub F G hex hx₂ hG0
  refine ⟨y, hy, hMon, ?_⟩
  have hFinj := GlobalTheory.T.injective_of_phiModule_exact_triple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex
  set d := red (Pp.D.phi x₂) with hd
  have hL : Pp.D.phi x₂ ∈ Pp.D.L := Pp.D.phi_mem_L hx₂.1
  have hσp : Pp.D.phi x₂ - Pp.D.xi d ∈ Pp.D.MMl := by
    refine sub_mem (Pp.D.ext_mono ((A_le_S l e).trans (le_away _ _)) hL) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) Pp.D.toPhiMod).2 _).2 ?_
    exact mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _
  have hGσ : G.app (Pp.D.phi x₂ - Pp.D.xi d) = 0 := by
    rw [map_sub, Hom.app_xi, hd, ← Hom.red_app, G.toHom.app_phi, hGx₂, map_nsmul, hφu, map_nsmul, map_nsmul,
      xi_red_of_phi_eq _ hφu, sub_self]
  obtain ⟨σ, hσ, hFσ⟩ := GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex _ hσp hGσ
  have hσinv : σ ∈ Pk.D.desc.inv := fun γ => hFinj (by
    rw [F.app_act, hFσ, map_sub, Pp.D.desc.act_phi, hx₂.2 γ, Descent.act_xi, hd, ← Descent.red_act,
      Pp.D.desc.act_phi, hx₂.2 γ])
  exact GlobalTheory.T.extensionClass_eq_lPow_smul_galois l a e ϖ LL η H T Tp f g hfg Pk Pp Pu F G hF hG hex hFinj u x hx1 hu hφu hux
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) x₂ hx₂ hGx₂ v c hv hgv hcv σ hσ hσinv hFσ y hy hFy

end GlobalTheory.BKGal.ExtClass
