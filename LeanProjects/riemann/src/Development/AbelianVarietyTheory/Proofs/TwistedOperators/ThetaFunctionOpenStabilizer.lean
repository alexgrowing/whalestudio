import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionProdConjEqOfHeisenbergFixedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilLevel

theorem stab : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary
theorem prodId : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (M f) = M f) → (∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → ∀ x, M f x * star (M g x) = f x * star (g x) := GlobalTheory.T.thetaFunction_prod_conj_eq_of_heisenbergFixed
theorem openKer : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints

theorem scalar_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (N : AddSubgroup (WO S T)) (M : Module.End ℂ (WO S T → ℂ))
    (hAR : ∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1)
    (hM : ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T (M f))
    (hc : ∀ w f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      M (heisO ψ S T w f) = heisO ψ S T w (M f))
    (hp : ∀ f g, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      ∀ x, M f x * star (M g x) = f x * star (g x)) :
    ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f) → M f = c • f := by
  obtain ⟨hth, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  obtain ⟨l1, l2, l3, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hunit : ∀ a, ψ a * star (ψ a) = 1 := fun a => by
    have h : ‖ψ a‖ = 1 := hψ.1.2.1 a
    rw [Complex.star_def, Complex.mul_conj', h]; simp
  have skew : ∀ x y : WO S T, symplOH S T y x = -symplOH S T x y := fun x y => by
    have := l3 (x + y)
    rw [l1, l2, l2, l3, l3] at this
    linear_combination this

  have hfix : ∀ w g, (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T w g) = (heisO ψ S T w g)) := by
    intro w g hg hw u hu hu0
    have e1 := hcomp u w g
    have e2 := hcomp w u g
    rw [hg u hu hu0] at e2
    rw [e1, add_comm u w]
    have hs : ψ (symplOH S T u w) = ψ (symplOH S T w u) := by
      have h1 := hw u hu hu0
      rw [← l4] at h1
      have h2 : ψ (symplOH S T w u) * ψ (symplOH S T w u) = 1 := by
        rw [← AddChar.map_add_eq_mul]; exact h1
      rw [skew w u, AddChar.map_neg_eq_inv]
      exact inv_eq_of_mul_eq_one_right h2
    rw [hs, e2]
  by_cases h0 : ∃ f₀ x₀, IsThetaFunO ψ S T f₀ ∧ (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f₀ = f₀) ∧ f₀ x₀ ≠ 0
  · obtain ⟨f₀, x₀, hf₀, hf₀N, hx₀⟩ := h0
    have h1 := hp f₀ f₀ hf₀ hf₀N hf₀ hf₀N x₀
    have hn1 : ‖M f₀ x₀‖ = ‖f₀ x₀‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ x₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]; exact norm_ne_zero_iff.2 hx₀
    have hs : star (M f₀ x₀) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ x₀) / star (M f₀ x₀), fun f hf hfN => funext fun x => ?_⟩
    obtain ⟨γ, hγ, hA⟩ := hAR (x₀ - x)
    set w := x₀ - x - γ with hw
    have hg := hth w f₀ hf₀
    have hgN := hfix w f₀ hf₀N hA
    have h2 := hp f (heisO ψ S T w f₀) hf hfN hg hgN x
    rw [hc w f₀ hf₀ hf₀N hA] at h2
    obtain ⟨δ, hδ⟩ := (ratL T S).neg_mem hγ
    have hxw : x + w = ratW T S δ + x₀ := by
      have hδ' : ratW T S δ = -γ := hδ
      rw [hδ', hw]; abel
    simp only [heisO, hxw] at h2
    rw [hf₀.quasi δ x₀, (hM f₀ hf₀ hf₀N).quasi δ x₀] at h2
    rw [star_mul', star_mul', star_mul', star_mul'] at h2
    have h3 : M f x * star (M f₀ x₀) = f x * star (f₀ x₀) := by
      linear_combination (ψ (symplOH S T x w) * ψ (-symplOH S T (ratW T S δ) x₀)) * h2
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * hunit (symplOH S T x w)
        - (M f x * star (M f₀ x₀) - f x * star (f₀ x₀)) * ψ (symplOH S T x w) * star (ψ (symplOH S T x w))
          * hunit (-symplOH S T (ratW T S δ) x₀)
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h3, mul_comm]
  · refine ⟨0, fun f hf hfN => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hfN, hy⟩
    rw [this, map_zero, smul_zero]

theorem weil_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  intro D ψ S T χS χT om f _ hW hf
  have hψ := hW.std
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨N, K, hNU, hKo, hAR, hKN, hKA⟩ := stab ψ S T hψ U hUo
  have hfN : ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u f = f := fun u hu h0 => hU u (hNU hu) h0
  obtain ⟨-, hcomp, -⟩ := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T
  have hMV : ∀ k ∈ K, k ∈ GfC T → ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      IsThetaFunO ψ S T (om (1, k) g) ∧ ∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u (om (1, k) g) = om (1, k) g := by
    intro k hk hkf g hg hgN
    refine ⟨hW.om_pres _ g hg, fun u hu hu0 => ?_⟩
    obtain ⟨h1, h2⟩ := hKN k⁻¹ (K.inv_mem hk) ((GfC T).inv_mem hkf) u hu hu0
    have e := hW.om_heis 1 k (actO S T 1 k⁻¹ u) g hg
    have e2 := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 k u
    rw [inv_one] at e2
    rw [e2, hgN _ h1 h2] at e
    exact e.symm
  have hMC : ∀ k ∈ K, k ∈ GfC T → ∀ w g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) →
      (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) →
      om (1, k) (heisO ψ S T w g) = heisO ψ S T w (om (1, k) g) := by
    intro k hk hkf w g hg hgN hw
    obtain ⟨d1, d2, d3⟩ := hKA k hk hkf w hw
    have e := hcomp w (actO S T 1 k w - w) (om (1, k) g)
    rw [(hMV k hk hkf g hg hgN).2 _ d1 d2, d3, one_smul, add_sub_cancel] at e
    rw [hW.om_heis 1 k w g hg, e]
  have hsc : ∀ k ∈ K, k ∈ GfC T → ∃ c : ℂ, ∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g := by
    intro k hk hkf
    exact scalar_of_prod hψ N (om (1, k)) hAR (fun g hg hgN => (hMV k hk hkf g hg hgN).1) (hMC k hk hkf)
      (prodId ψ S T hψ N (om (1, k)) (hMV k hk hkf) (hMC k hk hkf)
        (fun μ 𝓕 hμ h𝓕 g hg _ => hW.om_unit μ 𝓕 hμ h𝓕 (1, k) g hg))
  by_cases hf0 : ∃ x₀, f x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hf0
    let F : GA D T → ℂ := fun k => om (1, k) f x₀ / f x₀
    have hFc : Continuous F :=
      ((hW.om_cont f hf x₀).comp (continuous_const.prodMk continuous_id)).div_const _
    have hF1 : F 1 = 1 := by
      show om (1, 1) f x₀ / f x₀ = 1
      rw [show ((1, 1) : GA D S × GA D T) = 1 from rfl, map_one, Module.End.one_apply, div_self hx₀]
    have hFc' : ∀ k ∈ K, k ∈ GfC T → ∀ c : ℂ, (∀ g, IsThetaFunO ψ S T g → (∀ u ∈ N, u.map (infPart D) = 0 → heisO ψ S T u g = g) → om (1, k) g = c • g) →
        F k = c := by
      intro k hk hkf c hc
      show om (1, k) f x₀ / f x₀ = c
      rw [hc f hf hfN, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀, mul_one]
    have hFm : ∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b := by
      intro a ha haf b hb hbf
      obtain ⟨ca, hca⟩ := hsc a ha haf
      obtain ⟨cb, hcb⟩ := hsc b hb hbf
      rw [hFc' a ha haf ca hca, hFc' b hb hbf cb hcb]
      show om (1, a * b) f x₀ / f x₀ = ca * cb
      rw [show ((1, a * b) : GA D S × GA D T) = (1, a) * (1, b) by simp, map_mul, Module.End.mul_apply,
        hcb f hf hfN, map_smul, hca f hf hfN, smul_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hx₀,
        mul_one, mul_comm]
    obtain ⟨V, hVo, hV⟩ := openKer T K hKo F hFc hF1 hFm
    refine ⟨V ⊓ K, hVo.inter hKo, fun k hk hkf => ?_⟩
    obtain ⟨c, hc⟩ := hsc k hk.2 hkf
    have h1 : c = 1 := by rw [← hFc' k hk.2 hkf c hc]; exact hV k hk.1 hkf
    rw [hc f hf hfN, h1, one_smul]
  · push_neg at hf0
    have : f = 0 := funext hf0
    refine ⟨⊤, isOpen_univ, fun k _ _ => ?_⟩
    rw [this, map_zero]

end GlobalTheory.WeilLevel
