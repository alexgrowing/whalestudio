import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelTwistPlaceInThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.UpQProof

theorem isGen_of_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B₀ : Type} [Fintype A] [DecidableEq A] [Fintype B₀] [DecidableEq B₀]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (A ⊕ B₀) k) X} {ρ' : Representation ℂ (GL (A ⊕ B₀) k) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {ξ : kˣ →* ℂˣ} {ϖ : kˣ} {B : Multiset ℂˣ} {x : X}
    (h : GlobalTheory.ParHecke.IsGen ρ' ξ ϖ B (f x)) : GlobalTheory.ParHecke.IsGen ρ ξ ϖ B x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, fun s R d hR => hi ?_⟩
  · intro g hg d hd
    apply hi
    rw [hf, h1 g hg d hd, map_smul]
  · rw [map_smul, map_sum, h3 s R d hR]
    simp only [map_smul, hf]

open ValuativeRel in

theorem seg_eq_segL {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    {ϖ : (Fv D.host.F v)ˣ} (hϖ : valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = uniformizer (Fv D.host.F v))
    (z : ℂˣ) (t : ℕ) : GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  have hq := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  rw [Finset.range_val]
  refine Multiset.map_congr rfl fun n _ => ?_
  ext
  simp only [Units.val_mul, GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
  congr 1
  rw [Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem isUnram_of_lifts {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    (a : (kP PP)ˣ →* ℂˣ) (μ μ' : (Fv D.host.F v)ˣ →* ℂˣ) (h : LiftsChar φ PP μ a) (h' : LiftsChar φ PP μ' a) :
    GlobalTheory.SplitWeil.IsUnram (μ * μ'⁻¹) := by
  intro y hy
  have hy1 : Valued.v (y : Fv D.host.F v) = 1 := (GlobalTheory.TameLiftChar.val_eq_one_iff _).1 hy
  obtain ⟨a0, ha0⟩ := ReciprocityTheory.Aut.adic_exists_approx v (y : Fv D.host.F v) hy1.le
  let x0 : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a0
  have hx0 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) = algebraMap (𝓞 D.host.F) (Fv D.host.F v) a0 := by
    have h1 : ((x0 : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a0) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [h1, GlobalTheory.PlaceRed.rdQ_alg]
    rfl
  have hr1 : Valued.v ((y : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := by rw [hx0]; exact ha0
  have hnot : x0 ∉ PP.asIdeal := by
    intro hm
    have h2 := (hP x0).1 hm
    have : Valued.v (y : Fv D.host.F v) < 1 := by
      have := Valuation.map_add_lt Valued.v hr1 h2
      simpa using this
    rw [hy1] at this
    exact lt_irrefl _ this
  have hne : (Ideal.Quotient.mk PP.asIdeal x0 : kP PP) ≠ 0 := fun h0 => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let κ : (kP PP)ˣ := Units.mk0 _ hne
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (y : Fv D.host.F v) (κ : kP PP) := ⟨x0, rfl, hr1⟩
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h y κ hR, h' y κ hR, mul_inv_cancel]

end GlobalTheory.ChainTw.UpQProof

open GlobalTheory.ChainTw.UpQProof in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ChainTw.upQ_holds : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpQ D := by
  classical
  intro hP D hN c w hw k hk s s' hs hs' p hp u φ hu v₀ _
  intro PP hPP v φv hφv x ϖ hx ξl hξl ι' hι'
  obtain ⟨-, hch⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw k hk.le s hs PP hPP
  obtain ⟨-, -, ⟨ι, hι⟩, hμ⟩ := hch v φv hφv
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨μT, -, hμT⟩ := hμ (c.chT (k + 1))
  obtain ⟨W, hW, hΦ, T, hT0, hTθ, hTω⟩ :=
    GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions D hN c w hw k hk s s' hs hs' p hp PP hPP v φv hφv ι ι' hι hι' μS μT ξl hμS hμT hξl φ
  have hsrc := hu v₀ PP hPP v φv hφv x ϖ hx ξl hξl ι hι
  obtain ⟨e, he, hx1, hx2, hϖ⟩ := hx
  have hSϖ : μS ϖ = Circle.toUnits (c.chS (k + 1) x) := hμS x ϖ ⟨e, he, hx1, hx2⟩
  have hTϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x) := hμT x ϖ ⟨e, he, hx1, hx2⟩
  have htame := (GlobalTheory.tameLift_isTame_not_isUnram D v φv PP (w.ξ PP) hφv (hw.ne PP hPP) ξl hξl).1
  obtain ⟨hres, -, -⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  have hQ := hres PP (hw.union ▸ Finset.mem_union_right _ hPP)
  rw [hw.chiQ (k + 1) PP hPP, inv_inv] at hQ
  have hunS : GlobalTheory.SplitWeil.IsUnram (μS * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μS ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.1 v φv hφv μS hμS) hξl
  have hunT : GlobalTheory.SplitWeil.IsUnram (μT * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μT ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.2 v φv hφv μT hμT) hξl
  have hcard : Fintype.card (Blocks (k + 1) D.R.t) = Fintype.card (Blocks k D.R.t) + D.R.t := by
    simp [Blocks, Fintype.card_sigma]
    ring
  obtain ⟨hr, -, hfl⟩ := hs
  have hHaar : s.ν.IsHaarMeasure := hfl.haar
  have hFund : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hθ : IsInfFam c.θ := hw.com.inf
  set F : GA D s.V → ℂ := PiLocalization₂.val u v₀ with hF
  have hFa := PiLocalization₂.val_autCusp c s u v₀
  let ρ0 : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) (GA D s.V → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι
  let cy : GA D s.V → ℂ := fun g => conj (F g)
  let X : Submodule ℂ (GA D s.V → ℂ) := Submodule.span ℂ (Set.range fun a => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u', IsThetaFunO c.ψ s.V s'.V u' → ∀ y, IntegrableOn (fun g => thetaKO p.ω g y u' * z g) s.fd s.ν) ∧
      (∀ γ ∈ GQ s.V, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u' hu' y => GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn hP D c.ψ s.V s'.V (c.chS (k + 1))
        (c.chT (k + 1)) p.ω hp.weil c.θ hθ s.ν s.fd hHaar hFund u' F hu' hFa.1 hFa.2 (ι a) y, fun γ hγ g => ?_⟩
      show conj (F (γ * g * ι a)) = conj (F (g * ι a))
      rw [mul_assoc]
      exact congrArg conj (hFa.1.left γ hγ _)
    | zero => exact ⟨fun u' _ y => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (z + z') g) = fun g => thetaKO p.ω g y u' * z g + thetaKO p.ω g y u' * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u' hu' y).add (h2.1 u' hu' y)
    | smul a z _ h1 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (a • z) g) = fun g => a * (thetaKO p.ω g y u' * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u' hu' y).const_mul a
  let bf : W → X → GA D s'.V → ℂ := fun u' z y => ∫ g in s.fd, thetaKO p.ω g y (T u') * (z : GA D s.V → ℂ) g ∂s.ν
  let b : W →ₗ[ℂ] X →ₗ[ℂ] (GA D s'.V → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u₁ u₂ z => by
      funext y
      show _ = bf u₁ z y + bf u₂ z y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z z.2).1 _ (hTθ u₂) y)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u₁ z z' => by
      funext y
      show _ = bf u₁ z y + bf u₁ z' y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z' z'.2).1 _ (hTθ u₁) y)]
      congr 1; funext g
      simp [mul_add])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ g h (u₁ : W) (z : X), b ⟨GlobalTheory.ParHecke.omTwo μS μT g h u₁, hW g h u₁ u₁.2⟩ (ρ g z) =
      (GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι' h (b u₁ z) := by
    intro a a' u₁ z
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.ParHecke.omTwo μS μT a a' u₁, hW a a' u₁ u₁.2⟩) * (z : GA D s.V → ℂ) (g * ι a) ∂s.ν =
      ∫ g in s.fd, thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g ∂s.ν
    rw [← hTω a a' u₁]
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D s.V s.ν s.fd hHaar hFund
      (fun g => thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hp.weil (hTθ u₁) γ hγ, (hXp z z.2).2 γ hγ]) (ι a)
  have hx0 : GlobalTheory.ParHecke.IsGen ρ ξl ϖ (qPar c PP x k) ⟨cy, hcy⟩ :=
    isGen_of_injective X.subtype (fun _ _ => rfl) Subtype.val_injective hsrc
  have key := GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing (Fv D.host.F v) (Fin D.R.r) (Blocks k D.R.t) (Blocks (k + 1) D.R.t) ϖ hϖ D.R.t hcard ξl μS μT
    htame hunS hunT W hW hΦ X ρ ⟨cy, hcy⟩ (qPar c PP x k) hx0 (GA D s'.V → ℂ) ((GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι') b hb
  have hval : b ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩ ⟨cy, hcy⟩ = fun y => conj (p.up φ F y) := by
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩) * conj (F g) ∂s.ν =
      conj (∫ g in s.fd, conj (thetaKO p.ω g y (p.pt φ)) * F g ∂s.ν)
    rw [hT0, ← integral_conj]
    congr 1; funext g; simp
  rw [hval, hSϖ, hTϖ, ← seg_eq_segL φv PP hφv hϖ] at key
  exact key

end
