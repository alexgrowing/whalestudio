import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionOpenStabilizerStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.WeilLevel
theorem weil_representation_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
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
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_weil_level_eq_conductor : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsThetaFunO ψ S T f → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → om (1, k) f = f := by
  first | exact @_root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | exact _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor | (intros; apply _root_.GlobalTheory.WeilLevel.weil_representation_level_eq_conductor <;> assumption)
end
