import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfIsVacO
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CartanInverseThetaIdentity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenSubgroupPreservesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalPointsFinitePartSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
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

noncomputable section

namespace GlobalTheory.VacTransFix

theorem nsmul_cancel {D : D7} {V W : HSp D} {M : ℕ} (hM : M ≠ 0) {x x' : WO V W} (h : M • x = M • x') : x = x' := by
  set a : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) ((M : D.host.F)⁻¹)) with ha_def
  have ha : a * (M : AE D) = 1 := by
    have e : (M : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (M : D.host.F)) := by
      simp [map_natCast]
    rw [e, ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, map_one]
  have key : ∀ z : WO V W, a • (M • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ha, one_smul]
  rw [← key x, h, key]

theorem fix_trans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  obtain ⟨hpair, -, -, -, hsdV, hsdW, -, hcart, hvac⟩ := hP
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.VacFixOpen.exists_open_fix_vacO D ψ θ V W χV χW om hpair.weil hpair.sigV hpair.sigW
    (fun _ => 1) sW (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hpair.std τ) hcart ΛV ΛW hsdV hsdW f₀ hvac
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.LatFixMod.exists_open_keep_cong D V W ΛV ΛW hsdV hsdW (2 * M * M)
    (Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hM)) (Nat.pos_of_ne_zero hM))
  refine ⟨J₁ ⊓ J₂, by rw [Subgroup.coe_inf]; exact hJ₁o.inter hJ₂o, fun k hk hkJ y hy => ?_⟩
  have hθ : IsThetaFunO ψ V W f₀ := hvac.2.theta
  rw [hpair.weil.om_heis k 1 y f₀ hθ, hJ₁ k hk hkJ.1]
  obtain ⟨l, hl, e⟩ := (hJ₂ k hk hkJ.2).2 (M • y) hy
  have hlin : actO V W k 1 (M • y) = M • actO V W k 1 y :=
    (AddMonoidHom.mk' (actO V W k 1) (GlobalTheory.LatNhds.actO_add k 1)).map_nsmul M y
  have e2 : M • actO V W k 1 y = M • (y + 2 • (M • l)) := by
    rw [← hlin, e, smul_add, smul_smul, smul_smul, show 2 * M * M = M * 2 * M by ring]
  rw [nsmul_cancel hM e2]
  refine GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hvac.2.lat.1 _ (AddSubgroup.nsmul_mem _ hl M)) ?_
  rw [GlobalTheory.RatSelfDual.symplO_nsmul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hvac.1 hsdV hsdW hy hl

end GlobalTheory.VacTransFix

end
