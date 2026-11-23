import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealInvariantSesquilinearFormEqSmulInnerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.Core.Rk.RealCoef

open scoped ComplexConjugate ComplexOrder

theorem petersson_conj {D : D7} {V : HSp D} (m : Measure (GA D V)) (φ ψ : GA D V → ℂ) :
    GlobalTheory.Cusp.petersson V m φ ψ = conj (GlobalTheory.Cusp.petersson V m ψ φ) := by
  simp only [GlobalTheory.Cusp.petersson, GlobalTheory.AutomorphicL2Unitary.pet]
  rw [← integral_conj]
  congr 1
  funext q
  simp [mul_comm]

theorem rcoef_of_fun {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (m : Measure (GA D V)) (hm : m.IsHaarMeasure)
    (Y : GA D V → c.W) (hYc : Continuous Y) (hYi : ∀ γ ∈ GQ V, ∀ h, Y (γ * h) = Y h) {K : Set (GA D V)}
    (hK : IsCompact K) (hKc : ∀ h, ∃ γ ∈ GQ V, ∃ k ∈ K, h = γ * k)
    (hsh : ∀ b ∈ GinfC V, ∀ g, Y (g * b) = c.ρ b⁻¹ (Y g)) :
    ∃ z : ℂ, (∀ w : c.W, ∀ b ∈ GinfC V,
      GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, Y g⟫_ℂ) (fun g => ⟪w, Y g⟫_ℂ) b = z * ⟪c.ρ b w, w⟫_ℂ) ∧ (Y ≠ 0 → z ≠ 0) := by
  haveI := hm
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds V m hm
  let φ : c.W → GA D V → ℂ := fun x g => ⟪x, Y g⟫_ℂ
  have hφL : ∀ x, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (φ x) := fun x γ hγ g => by
    simp only [φ, hYi γ hγ g]
  have hφc : ∀ x, Continuous (φ x) := fun x => continuous_const.inner hYc
  have hφ2 : ∀ x, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) m (φ x) := fun x => by
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn (hφc x).continuousOn
    refine GlobalTheory.Cusp.memL2_of_bounded_continuous_invariant (hφL x) (hφc x) (C := C) fun h => ?_
    obtain ⟨γ, hγ, k, hk, e⟩ := hKc h
    rw [e, hφL x γ hγ k]
    exact hCb k hk
  have hshift : ∀ b ∈ GinfC V, ∀ x, rTr V b (φ x) = φ (c.ρ b x) := by
    intro b hb x
    funext g
    show ⟪x, Y (g * b)⟫_ℂ = ⟪c.ρ b x, Y g⟫_ℂ
    rw [hsh b hb g, ← hc.2.1 b x (c.ρ b⁻¹ (Y g)), GlobalTheory.DefiniteEnd.rho_inv_cancel]
  have hadd : ∀ x x', φ (x + x') = φ x + φ x' := fun x x' => funext fun g => inner_add_left _ _ _
  have hsmul : ∀ (a : ℂ) x, φ (a • x) = (starRingEnd ℂ a) • φ x := fun a x => funext fun g => inner_smul_left _ _ _
  let B : c.W →ₗ⋆[ℂ] c.W →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x x' => GlobalTheory.Cusp.petersson V m (φ x) (φ x'))
    (fun x x' y => by rw [hadd]; exact GlobalTheory.Cusp.petersson_add_left (hφ2 x) (hφ2 x') (hφ2 y))
    (fun a x y => by rw [hsmul]; exact GlobalTheory.Cusp.petersson_smul_left _ _ _)
    (fun x y y' => by
      rw [petersson_conj m (φ x) (φ (y + y')), hadd, GlobalTheory.Cusp.petersson_add_left (hφ2 y) (hφ2 y') (hφ2 x), map_add,
        ← petersson_conj m (φ x) (φ y), ← petersson_conj m (φ x) (φ y')])
    (fun a x y => by
      rw [petersson_conj m (φ x) (φ (a • y)), hsmul, GlobalTheory.Cusp.petersson_smul_left, map_mul,
        ← petersson_conj m (φ x) (φ y), Complex.conj_conj, RingHom.id_apply, smul_eq_mul])
  have hB : ∀ x x', B x x' = GlobalTheory.Cusp.petersson V m (φ x) (φ x') := fun _ _ => rfl
  have hinv : ∀ u ∈ GinfC V, ∀ x x', B (c.ρ u x) (c.ρ u x') = B x x' := by
    intro u hu x x'
    rw [hB, hB, ← hshift u hu, ← hshift u hu]
    exact GlobalTheory.Cusp.petersson_rTr (hφ2 x) (hφ2 x') u
  obtain ⟨z, hz⟩ := GlobalTheory.T.real_invariant_sesquilinear_form_eq_smul_inner D V c hc B hinv
  refine ⟨z, fun w b hb => ?_, fun hY hz0 => ?_⟩
  · show GlobalTheory.Cusp.petersson V m (rTr V b (φ w)) (φ w) = _
    rw [hshift b hb, ← hB]
    exact hz _ _
  · apply hY
    have h0 : ∀ x, φ x = 0 := by
      intro x
      by_contra hne
      have hpos := GlobalTheory.Cusp.petersson_self_pos (hφ2 x) (hφc x) hne
      have h1 : GlobalTheory.Cusp.petersson V m (φ x) (φ x) = 0 := by
        rw [← hB, hz x x, hz0, zero_mul]
      rw [h1, Complex.zero_re] at hpos
      exact lt_irrefl _ hpos
    funext g
    exact inner_self_eq_zero.1 (congrFun (h0 (Y g)) g)

set_option maxHeartbeats 1000000 in

theorem rcoef_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (m : Measure (GA D (Vc D i))), m.IsHaarMeasure → ∃ z : ℂ, (∀ (w : (R.cV i).W), ∀ b ∈ GinfC (Vc D i), GlobalTheory.Core.Rk.IP.rcoef m (fun g => ⟪w, R.extV i t y g⟫_ℂ) (fun g => ⟪w, R.extV i t y g⟫_ℂ) b = z * ⟪(R.cV i).ρ b w, w⟫_ℂ) ∧ (y ≠ 0 → z ≠ 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t y m hm
  have hmod := hC.models
  have hc : (R.cV i).Is := hmod.cV i
  have hx := (hmod.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hp : (Vc D i).IsPosDef := hmod.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hYc : Continuous (R.extV i t y) := GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) hc (R.βV i) (R.datVt i t) hx
  have hYi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h := GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hsh : ∀ b ∈ GinfC (Vc D i), ∀ g, R.extV i t y (g * b) = (R.cV i).ρ b⁻¹ (R.extV i t y g) :=
    fun b hb g => GlobalTheory.DownLift.DefiniteComp.extV_mul_inf R i t y hb g
  have key := rcoef_of_fun (R.cV i) hc m hm (R.extV i t y) hYc hYi hK hKc hsh
  refine ⟨key.choose, key.choose_spec.1, fun hy => key.choose_spec.2 fun hY0 => hy ?_⟩
  have hf0 : (R.HV i t).e y = 0 := by
    funext k
    obtain ⟨g, rfl⟩ := (finHom (Vc D i)).rangeRestrict_surjective k
    have e : (R.cV i).ρ g⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict g)) = 0 := congrFun hY0 g
    have e2 := congrArg ((R.cV i).ρ g) e
    rw [GlobalTheory.DefiniteEnd.rho_inv_cancel] at e2
    exact e2.trans (LinearMap.map_zero _)
  exact (hmod.HV i t).1 (hf0.trans ((R.HV i t).e.map_zero).symm)

end GlobalTheory.Core.Rk.RealCoef
