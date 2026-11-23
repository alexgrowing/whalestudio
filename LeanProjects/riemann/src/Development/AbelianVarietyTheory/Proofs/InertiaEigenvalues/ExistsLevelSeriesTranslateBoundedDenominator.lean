import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPartDenominatorBoundedByPrimePowerStatement
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

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1600000 in

theorem exists_move_denomAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl s hs
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hP.2.2.1, hP.2.2.2.2.2.2.1]
  obtain ⟨c, hc⟩ := GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power D V hstd l hl s
  refine ⟨c, fun z hz hOne M bad hM hbad hlb => ?_⟩
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard D V hstd
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  have hJo : IsOpen ((J₁ ⊓ J₂ : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := hJ₁o.inter hJ₂o
  obtain ⟨γ, h, kJ, hsp, e⟩ := GlobalTheory.SplitRepsOpen.exists_rep_splitOffBad D V (J₁ ⊓ J₂) bad hbad hJo (fin V (s * z))
  obtain ⟨k', hk', ek⟩ := Formalism.IndefR.TopMult.exists_lift (kJ : Bridge.Gf V)
  obtain ⟨a, ha_def⟩ : ∃ a : GA D V, a = h⁻¹ * ((γ : GA D V)⁻¹ * (s * z) * k'⁻¹) := ⟨_, rfl⟩
  have hfa : finHom V a = 1 := by
    have e' := congrArg Subtype.val e
    have ek' := congrArg Subtype.val ek
    simp only [MonoidHom.coe_rangeRestrict, Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul] at e' ek'
    rw [ha_def, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, ek', e']
    group
  have ha : a ∈ GinfC V := hfa
  have hγa : (γ : GA D V) * a ∈ GfC V := by
    have h1 : infHom V h = 1 := hsp.1
    have h2 : infHom V (s * z) = 1 := mul_mem hs hz
    have h3 : infHom V k' = 1 := hk'
    show infHom V ((γ : GA D V) * a) = 1
    rw [ha_def, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, h3]
    group
  have hs' : s * z = (γ : GA D V) * (h * a) * k' := by
    rw [ha_def]; group
  obtain ⟨γ', -, hγ'⟩ := γ.2
  have hrat : GlobalTheory.Member.IsRat V (γ : GA D V) γ' := hγ'.symm
  have hkJ : (kJ : Bridge.Gf V) ∈ J₁ := (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).1
  have hkJ' : ((kJ : Bridge.Gf V))⁻¹ ∈ J₁ := inv_mem hkJ
  have hden : DenomAt l c γ' := hc z hOne (γ : GA D V) h γ' kJ bad hrat hlb hsp (hJ₁ _ hkJ) (hJ₁ _ hkJ') e
  refine ⟨γ, h, a, γ', γ.2, hrat, ha, hγa, hsp, hden, fun e O f hf BW Q g => ?_⟩
  have hω := hP.1.weil
  have hθ : IsInfFam θ := hP.1.inf
  have hfix : om (k', 1) f = f := by
    have hk2 : fin V k' ∈ J₂ := by
      have ek2 : fin V k' = kJ := ek
      rw [ek2]; exact (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).2
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, hy, rfl⟩ := hx
      exact hJ₂ k' hk' hk2 y hy
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul r x _ hx =>
      change om (k', 1) ((r : ℂ) • x) = (r : ℂ) • x
      rw [map_smul, hx]
  have hthf : IsThetaFunO ψ V W f := GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hT : ∀ P, IsThetaFunO ψ V W (stdF ψ θ V W sW BW f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ hthf P
  have hk1 : om (k', 1) (stdF ψ θ V W sW BW f Q) = stdF ψ θ V W sW BW f Q := by
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χV χW om hθ hω (fun _ => 1) sW (fun _ => 1) BW f hT k' hk' 1
      (one_mem _) 1 (by rw [one_smul]; exact hfix) Q
    rw [one_smul] at this
    exact this
  have hp : ((s * z, g) : GA D V × GA D W) = ((γ : GA D V), 1) * ((h, g) * (a, 1)) * (k', 1) := by
    rw [hs']; simp [Prod.mk_mul_mk]
  have e1 : om (s * z, g) = om ((γ : GA D V), 1) * (om (h, g) * om (a, 1)) * om (k', 1) := by
    rw [hp, map_mul, map_mul, map_mul]
  have hth := hω.om_pres ((h, g) : GA D V × GA D W) _ (hω.om_pres ((a, 1) : GA D V × GA D W) _ (hT Q))
  show om (s * z, g) (stdF ψ θ V W sW BW f Q) 0 = om (h, g) (om (a, 1) (stdF ψ θ V W sW BW f Q)) 0
  rw [e1, Module.End.mul_apply, Module.End.mul_apply, hk1, Module.End.mul_apply,
    hω.om_aut _ γ.2 1 (one_mem _) _ hth]

end GlobalTheory.LevelSeries

end
