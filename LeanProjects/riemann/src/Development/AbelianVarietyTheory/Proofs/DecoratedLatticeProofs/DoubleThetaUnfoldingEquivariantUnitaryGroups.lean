import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutomStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairedThetaKernelContinuousAndRationallyInvarianStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiHandOffAutomorphicStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.Comm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem integral_right {V : HSp D} (v : Vol V) {F : GA D V → ℂ} (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) (a : GA D V) :
    ∫ g in v.𝓕, F (g * a) ∂v.μ = ∫ g in v.𝓕, F g ∂v.μ := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  have := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V v.μ v.haar).1
  exact GlobalTheory.Mem.IntByParts.setIntegral_mul_right (GQ V) v.μ v.fund hF a

theorem IsContAut.integrableOn {V : HSp D} (hV : CoCpt V) (v : Vol V) {F : GA D V → ℂ} (hF : IsContAut V F) :
    IntegrableOn F v.𝓕 v.μ :=
  (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D V hV v Unit (fun g _ => F g) (hF.2.comp continuous_fst) (fun γ hγ g _ => hF.1 γ hγ g)).1 ()

section BF

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
  (l : Link B L' ζ')

theorem contAut_kerBF {φ : GA D B.A → ℂ} {Ξ : WO B.V₀ J.W₀ → ℂ} (hφ : IsContAut B.A φ)
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (h : GA D J.W₀) (u : WO B.L J.W₀) :
    IsContAut B.A fun a => φ a * s.om₀ (B.o.emb (a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((s.weil₀.om_cont Ξ hΞ _).comp
    ((B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ s.weil₀ Ξ hΞ _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (B.o.emb (a, 1)) h
    ((B.o.resS J.W₀).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem handBF_left {φ φ' : GA D B.A → ℂ} {Ξ : WO B.V₀ J.W₀ → ℂ} (hφ : IsContAut B.A φ) (hφ' : IsContAut B.A φ')
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (c : ℂ) :
    handBF s l (c • φ + φ') Ξ = star c • handBF s l φ Ξ + handBF s l φ' Ξ := by
  funext h w
  simp only [handBF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add ((IsContAut.integrableOn B.cpt B.vA (contAut_kerBF s hφ hΞ h _)).const_mul c)
    (IsContAut.integrableOn B.cpt B.vA (contAut_kerBF s hφ' hΞ h _)), integral_const_mul, star_add, star_mul']

theorem handBF_right {φ : GA D B.A → ℂ} {Ξ Ξ' : WO B.V₀ J.W₀ → ℂ} (hφ : IsContAut B.A φ)
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (hΞ' : IsThetaFunO ψ B.V₀ J.W₀ Ξ') (c : ℂ) :
    handBF s l φ (c • Ξ + Ξ') = star c • handBF s l φ Ξ + handBF s l φ Ξ' := by
  funext h w
  simp only [handBF, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, mul_left_comm _ c]
  rw [integral_add ((IsContAut.integrableOn B.cpt B.vA (contAut_kerBF s hφ hΞ h _)).const_mul c)
    (IsContAut.integrableOn B.cpt B.vA (contAut_kerBF s hφ hΞ' h _)), integral_const_mul, star_add, star_mul']

theorem handBF_equiv {φ : GA D B.A → ℂ} {Ξ : WO B.V₀ J.W₀ → ℂ} (hφ : IsContAut B.A φ)
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (a : GA D B.A) (g : GA D J.W₀) :
    handBF s l (fun x => φ (x * a)) (s.om₀ (B.o.emb (a, 1), g) Ξ) = fun h => handBF s l φ Ξ (h * g) := by
  funext h w
  simp only [handBF]
  refine congrArg star (Eq.trans ?_ (integral_right B.vA (contAut_kerBF s hφ hΞ (h * g) (l.κ J.W₀ w)).1 a))
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul]

end BF

section FB

variable {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank)

include s in
theorem integrableOn_pair {Y : GA D J.W₀ → WO J.W₀ B.L → ℂ} {F : WO J.W₀ B.V₀ → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    (hF : IsThetaFunO ψ J.W₀ B.V₀ F) (h : GA D J.W₀) :
    IntegrableOn (fun v => F ((B.o.resT J.W₀).symm (0, v)) * star (Y h v)) vL.𝓕 vL.μ := by
  refine covolOne_integrableOn vL.covol _ ?_ ?_
  · exact (hF.cont.comp ((B.o.continuous_resT_symm _).comp (continuous_const.prodMk continuous_id))).mul
      (hY.cont.comp (continuous_const.prodMk continuous_id)).star
  · rintro _ ⟨γ, rfl⟩ v
    obtain ⟨δ, hδ⟩ : (B.o.resT J.W₀).symm (0, ratW B.L J.W₀ γ) ∈ ratL B.V₀ J.W₀ :=
      (B.o.mem_ratL_resT _ _).2 (by rw [AddEquiv.apply_symm_apply]; exact ⟨zero_mem _, γ, rfl⟩)
    replace hδ : ratW B.V₀ J.W₀ δ = (B.o.resT J.W₀).symm (0, ratW B.L J.W₀ γ) := hδ
    have e1 := hF.quasi δ ((B.o.resT J.W₀).symm (0, v))
    rw [hδ, ← map_add, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      symplOH_zero_left, zero_add] at e1
    have e2 := hY.quasi h γ v
    change F ((B.o.resT J.W₀).symm (0, ratW B.L J.W₀ γ + v)) * star (Y h (ratW B.L J.W₀ γ + v)) = _
    have e3 : ∀ x, ψ x * star (ψ x) = 1 := fun x => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, s.weil₀.std.1.2.1 x]
      simp
    rw [e1, e2, star_mul', mul_mul_mul_comm, e3, one_mul]

theorem contAut_pairKer {Y : GA D J.W₀ → WO J.W₀ B.L → ℂ} {Ξ : WO J.W₀ B.V₀ → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (h₁ : GA D B.A) : IsContAut J.W₀ fun h₀ => pairKer s vL Y Ξ h₀ h₁ :=
  have H := GlobalTheory.T.pairedThetaKernel_continuous_and_rationally_invariant D ψ σ J B s vL Y Ξ hY hΞ
  ⟨fun γ hγ h₀ => H.2.1 γ hγ h₀ h₁, H.1.comp (continuous_id.prodMk continuous_const)⟩

theorem handFB_left {Y Y' : GA D J.W₀ → WO J.W₀ B.L → ℂ} {Ξ : WO J.W₀ B.V₀ → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    (hY' : IsQuasiFam ψ J.W₀ B.L Y') (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (c : ℂ) :
    handFB s vL (star c • Y + Y') Ξ = c • handFB s vL Y Ξ + handFB s vL Y' Ξ := by
  funext h₁
  have e : ∀ h₀, pairKer s vL (star c • Y + Y') Ξ h₀ h₁ = c * pairKer s vL Y Ξ h₀ h₁ + pairKer s vL Y' Ξ h₀ h₁ := by
    intro h₀
    simp only [pairKer, contractT, thPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', star_star,
      mul_add, mul_left_comm _ c]
    rw [integral_add ((integrableOn_pair s vL hY (s.weil₀.om_pres _ _ hΞ) h₀).const_mul c)
      (integrableOn_pair s vL hY' (s.weil₀.om_pres _ _ hΞ) h₀), integral_const_mul]
  simp only [handFB, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add ((IsContAut.integrableOn J.cpt J.v0 (contAut_pairKer s vL hY hΞ h₁)).const_mul c)
    (IsContAut.integrableOn J.cpt J.v0 (contAut_pairKer s vL hY' hΞ h₁)), integral_const_mul]

theorem handFB_right {Y : GA D J.W₀ → WO J.W₀ B.L → ℂ} {Ξ Ξ' : WO J.W₀ B.V₀ → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (hΞ' : IsThetaFunO ψ J.W₀ B.V₀ Ξ') (c : ℂ) :
    handFB s vL Y (c • Ξ + Ξ') = c • handFB s vL Y Ξ + handFB s vL Y Ξ' := by
  funext h₁
  have e : ∀ h₀, pairKer s vL Y (c • Ξ + Ξ') h₀ h₁ = c * pairKer s vL Y Ξ h₀ h₁ + pairKer s vL Y Ξ' h₀ h₁ := by
    intro h₀
    simp only [pairKer, contractT, thPair, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      mul_assoc]
    rw [integral_add ((integrableOn_pair s vL hY (s.weil₀.om_pres _ _ hΞ) h₀).const_mul c)
      (integrableOn_pair s vL hY (s.weil₀.om_pres _ _ hΞ') h₀), integral_const_mul]
  simp only [handFB, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add ((IsContAut.integrableOn J.cpt J.v0 (contAut_pairKer s vL hY hΞ h₁)).const_mul c)
    (IsContAut.integrableOn J.cpt J.v0 (contAut_pairKer s vL hY hΞ' h₁)), integral_const_mul]

theorem handFB_equiv {Y : GA D J.W₀ → WO J.W₀ B.L → ℂ} {Ξ : WO J.W₀ B.V₀ → ℂ} (hY : IsQuasiFam ψ J.W₀ B.L Y)
    (hΞ : IsThetaFunO ψ J.W₀ B.V₀ Ξ) (g : GA D J.W₀) (h : GA D B.A) :
    handFB s vL (fun x => Y (x * g)) (s.om₀ (g, B.o.emb (h, 1)) Ξ) = fun x => handFB s vL Y Ξ (x * h) := by
  funext h₁
  simp only [handFB]
  refine Eq.trans ?_ (integral_right J.v0 (contAut_pairKer s vL hY hΞ (h₁ * h)).1 g)
  congr 1
  funext x
  simp only [pairKer]
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul]

end FB

section Double

variable {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
  (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {φ φ' : GA D B.A → ℂ} {Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ}
  {Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ}

theorem quasi_handBF (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) :
    IsQuasiFam ψ J.W₀ B'.L (handBF s₁ l φ Ξ₁) :=
  GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic D ψ _ B J s₁ B'.L B'.ζ B'.line l φ Ξ₁ hφ h₁

theorem contAut_hand0 (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) :
    IsContAut B'.A (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂) :=
  GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B' s₂ vL _ Ξ₂ (quasi_handBF s₁ l hφ h₁) h₂

theorem doubleThetaUnfolding_linear_function (hφ : IsContAut B.A φ) (hφ' : IsContAut B.A φ') (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁)
    (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) (c : ℂ) :
    hand0 s₁ s₂ l vL (c • φ + φ') Ξ₁ Ξ₂ = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ + hand0 s₁ s₂ l vL φ' Ξ₁ Ξ₂ := by
  rw [hand0, handBF_left s₁ l hφ hφ' h₁, handFB_left s₂ vL (quasi_handBF s₁ l hφ h₁) (quasi_handBF s₁ l hφ' h₁) h₂]
  rfl

theorem doubleThetaUnfolding_linear_first_datum (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) (h₁' : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁')
    (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) (c : ℂ) :
    hand0 s₁ s₂ l vL φ (c • Ξ₁ + Ξ₁') Ξ₂ = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ + hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂ := by
  rw [hand0, handBF_right s₁ l hφ h₁ h₁', handFB_left s₂ vL (quasi_handBF s₁ l hφ h₁) (quasi_handBF s₁ l hφ h₁') h₂]
  rfl

theorem doubleThetaUnfolding_linear_second_datum (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂)
    (h₂' : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂') (c : ℂ) :
    hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂ + Ξ₂') = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ + hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂' :=
  handFB_right s₂ vL (quasi_handBF s₁ l hφ h₁) h₂ h₂' c

theorem doubleThetaUnfolding_equivariant_unitaryGroups (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂)
    (a : GA D B.A) (g : GA D J.W₀) (h : GA D B'.A) :
    hand0 s₁ s₂ l vL (fun x => φ (x * a)) (s₁.om₀ (B.o.emb (a, 1), g) Ξ₁) (s₂.om₀ (g, B'.o.emb (h, 1)) Ξ₂) =
      fun x => hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ (x * h) := by
  rw [hand0, handBF_equiv s₁ l hφ h₁, handFB_equiv s₂ vL (quasi_handBF s₁ l hφ h₁) h₂]
  rfl

end Double

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem eq_of_map_pr {S : HSp D} {g g' : GA D S} (hg : SuppAt p.e S g) (hg' : SuppAt p.e S g')
    (h : (mt S g).map p.pr = (mt S g').map p.pr) : g = g' := by
  have key : ∀ {m n : ℕ} (x y : Mx D m n), x.map p.pr = y.map p.pr → p.e • x = p.e • y := fun x y hxy => by
    ext i j
    change p.e * x i j = p.e * y i j
    rw [← p.sec_pr, ← p.sec_pr]
    exact congrArg p.sec (congrFun (congrFun hxy i) j)
  have hinv : (mt S g⁻¹).map p.pr = (mt S g'⁻¹).map p.pr := by
    have a1 : (mt S g⁻¹).map p.pr * (mt S g).map p.pr = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have a2 : (mt S g').map p.pr * (mt S g'⁻¹).map p.pr = 1 := by
      rw [← Matrix.map_mul, mt_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.mul_one ((mt S g⁻¹).map p.pr), ← a2, ← h, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have h1 := key _ _ h
  have h2 := key _ _ hinv
  have h3 : ∀ x : GA D S, cA D p.e • mt S x = giA S * (adj (p.e • mt S x⁻¹) * gA S) := fun x => by
    rw [adj_smul, Matrix.smul_mul, Matrix.mul_smul, ← mt_inv, inv_inv]
  have h4 : cA D p.e • mt S g = cA D p.e • mt S g' := by rw [h3, h3, h2]
  apply mt_injective S
  ext i j
  have b1 := hg i j
  have b2 := hg' i j
  have b3 : p.e * mt S g i j = p.e * mt S g' i j := congrFun (congrFun h1 i) j
  have b4 : cA D p.e * mt S g i j = cA D p.e * mt S g' i j := congrFun (congrFun h4 i) j
  rw [Matrix.sub_apply] at b1 b2
  linear_combination b2 - b1 + b3 + b4

theorem suppAt_emb {S₀ A L : HSp D} (o : OrthDec S₀ A L) {e : AE D} {a : GA D A} (ha : SuppAt e A a) :
    SuppAt e S₀ (o.emb (a, 1)) := by
  have e1 : mt S₀ (o.emb (a, 1)) - 1 = o.jA ⬝ (mt A a - 1) ⬝ o.pA := by
    rw [o.mt_emb, mt_one, Matrix.mul_one, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  have e2 : (e + cA D e) • (mt A a - 1) = mt A a - 1 := by
    ext i j; exact ha i j
  intro i j
  have : (e + cA D e) • (mt S₀ (o.emb (a, 1)) - 1) = mt S₀ (o.emb (a, 1)) - 1 := by
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, e2]
  exact congrFun (congrFun this i) j

theorem emb_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (a : GA D A) :
    mt S₀ (o.emb (a, 1)) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
  have : (ratV (vecB o ζ) : Fin S₀.rank → AE D) = o.jB *ᵥ ratV ζ := by
    funext i
    exact RingHom.map_mulVec (incA D) o.iB ζ i
  rw [this, mulVec_mulVec, o.emb_jB, mt_one, Matrix.mul_one]

theorem block_calc {R K m r n : Type} [CommRing R] [CommRing K] [Fintype m] [Fintype r] [Fintype n] [DecidableEq n]
    (f : R →+* K) (M : Matrix m m R) (N : Matrix r r R) (j : Matrix m r R) (z : m → R) (b : Matrix r n K)
    (b' : Matrix n r K) (g : Matrix n n K) (h1 : M * j = j * N) (h2 : M *ᵥ z = z) (h3 : N.map f = b * g * b')
    (h4 : b' * b = 1) :
    M.map f * fromCols (j.map f * b) (replicateCol (Fin 1) fun i => f (z i)) =
      fromCols (j.map f * b) (replicateCol (Fin 1) fun i => f (z i)) *
        (fromBlocks g 0 0 1 : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) K) := by
  rw [mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
  congr 1
  · rw [← Matrix.mul_assoc, ← Matrix.map_mul, h1, Matrix.map_mul, h3]
    simp only [Matrix.mul_assoc, h4, Matrix.mul_one]
  · ext i j
    have := RingHom.map_mulVec f M z i
    rw [h2] at this
    exact this.symm

theorem emb_gl {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E} {n : Type} [Fintype n] [DecidableEq n]
    {β : Frame p A n} {β₀ : Frame p S₀ (n ⊕ Fin 1)} (h : IsSumFrame o ζ β β₀) (g : GL n k) :
    o.emb (β.gl g, 1) = β₀.gl (RootEx.embX 1 g) := by
  refine eq_of_map_pr (p := p) (suppAt_emb o (β.gl_supp g)) (β₀.gl_supp _) ?_
  have e := block_calc p.pr _ _ _ _ _ _ _ (o.emb_jA (β.gl g) 1) (emb_vecB o ζ (β.gl g)) (β.gl_mat g) β.b'b
  rw [← h] at e
  rw [β₀.gl_mat, show (RootEx.embX 1 g).val = fromBlocks g.val 0 0 1 from rfl, ← e, Matrix.mul_assoc, β₀.bb',
    Matrix.mul_one]

end Frames

end GlobalTheory.FinPl.Comm

end
