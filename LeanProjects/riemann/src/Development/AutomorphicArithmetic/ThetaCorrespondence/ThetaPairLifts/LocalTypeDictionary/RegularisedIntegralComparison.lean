import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRegulariserIsGood

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.RegCompare
variable {D : D7}
section Lin
variable {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M))
variable {ω ν 𝓕}
variable (ω ν 𝓕)
variable {ω ν 𝓕}
end Lin
theorem regularisedIntegral_of_const : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ c₀ : ℂ, (∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ algF ψ θ false A₁ B,
        Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) ∧ ModInt θ ωB ν₁ 𝓕₁ Φ₀ ∧
        ∀ Φ ∈ algF ψ θ true A B, p Φ = p' Φ₀ → thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ Φ₀) →
    ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c₀ H ΦB hΦB
  set S := algF ψ θ false A₁ B with hSdef
  have hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ S, ωB (g, 1) Φ ∈ S := hm.mapB.stabM.1
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B α (α / β) ωB hm.weilB
  obtain ⟨Φ₀, h0S, hrel, hmod0, hI⟩ := H ΦB hΦB
  have hp : p' ΦB = p' Φ₀ := by
    have h1 : finRel ωB S ≤ LinearMap.ker p' := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
      show p' _ = 0
      rw [map_sub, hm.mapB.invf u hu Ψ hΨ, sub_self]
    have := h1 hrel
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψ hΨ hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := _root_.GlobalTheory.T.twist_regulariser_isGood hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hm.weilB (n + 1)
    (Fin.cons ΦB Ψ) (Fin.cons 1 u) (Fin.cases hΦB hΨ) (Fin.cases (one_mem _) hu)
  have hB : ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) := (hz 0).1
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψ i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψ i)) = ωB (u', 1) (wop ωB z (Ψ i)) := fun i => hz i.succ
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψ i) ∈ S := fun i => wop_mem hstab hzG (hΨ i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have h0 := thetaInt_wop hν₁ (hL _ h0S) hmod0 z
  have eB : ΦB = Φ₀ + ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by simp only [hg]
    rw [← e, hsum]; abel
  have eW : wop ωB z ΦB = wop ωB z Φ₀ + ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i)) := by
    rw [eB, map_add, map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) = GlobalTheory.FunObj.zdeg z • thetaInt ωB ν₁ 𝓕₁ Φ₀ := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_add h0.1 (Intg.sum _ hi), thetaInt_sum _ hi, h0.2]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨z, hzG, hz0, wop_mem hstab hzG hΦB, hB, fun Φ hΦ hpΦ => ?_⟩
  have hΦ₁ : (GlobalTheory.FunObj.zdeg z)⁻¹ • Φ ∈ algF ψ θ true A B := Submodule.smul_mem _ _ hΦ
  have hp₁ : p ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) = p' Φ₀ := by
    rw [map_smul, hpΦ, smul_smul, inv_mul_cancel₀ hz0, one_smul, hp]
  have e1 := hI _ hΦ₁ hp₁
  have e2 : Φ = GlobalTheory.FunObj.zdeg z • ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) := by rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
  rw [e2, thetaInt_smul, e1, hJ, smul_comm]
theorem regularised_integral_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧
      GlobalTheory.FunObj.zdeg z ≠ 0 ∧ wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  obtain ⟨c, hc, H⟩ := hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  exact ⟨c, hc, _root_.GlobalTheory.RegCompare.regularisedIntegral_of_const hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c H⟩
end GlobalTheory.RegCompare
end
end
