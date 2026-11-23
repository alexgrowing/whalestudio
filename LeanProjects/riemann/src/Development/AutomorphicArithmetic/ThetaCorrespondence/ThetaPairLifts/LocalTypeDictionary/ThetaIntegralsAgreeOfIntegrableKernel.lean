import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRegulariserIsGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentityStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
namespace GlobalTheory.ThetaAgreeConv
section Reg
open MeasureTheory GlobalTheory.SquareComm GlobalTheory.RegCompare
variable {D : D7}
theorem thetaIntegral_eq_zero_of_finiteRelation (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A₁ : GlobalTheory.ChainFr.Fr W₁}
    {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ν₁ : Measure (GA D W₁)}
    {𝓕₁ : Set (GA D W₁)} (hν₁ : IsHaarFD W₁ ν₁ 𝓕₁) {ωB : GlobalTheory.Grid.WRep W₁ X}
    (hw : GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB)
    (hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ algF ψ θ false A₁ B, ωB (g, 1) Φ ∈ algF ψ θ false A₁ B)
    {Ψ : WO W₁ X → ℂ} (hΨ : Ψ ∈ finRel ωB (algF ψ θ false A₁ B)) (hint : Intg ωB ν₁ 𝓕₁ Ψ) :
    thetaInt ωB ν₁ 𝓕₁ Ψ = 0 := by
  set S := algF ψ θ false A₁ B with hSdef
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B α (α / β) ωB hw
  have hle : finRel ωB S ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Φ, hΦ, rfl⟩
    exact S.sub_mem (hstab u hu Φ hΦ) hΦ
  have hΨS : Ψ ∈ S := hle hΨ
  have hrel := hΨ
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψi hΨi hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := _root_.GlobalTheory.T.twist_regulariser_isGood hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hw n Ψi u hΨi hu
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψi i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψi i)) = ωB (u', 1) (wop ωB z (Ψi i)) := fun i => hz i
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψi i) ∈ S := fun i => wop_mem hstab hzG (hΨi i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have eΨ : Ψ = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψi i) - Ψi i) := by simp only [hg]
    rw [← e, hsum]
  have eW : wop ωB z Ψ = ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i)) := by
    rw [eΨ, map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z Ψ) = 0 := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψi i)) - wop ωB z (Ψi i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_sum _ hi]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero]
  rw [thetaInt_wop_of_intg hν₁ (hL Ψ hΨS) hint z] at hJ
  exact (smul_eq_zero.1 hJ).resolve_left hz0
end Reg
theorem thetaIntegrals_agree_of_integrable_kernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hM
  obtain ⟨c, hc0, hc⟩ := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hL D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁
    ωA ωB Pi rf rl p p' hM
  refine ⟨c, hc0, fun Φ hΦ Φ' hΦ' hint hp => ?_⟩
  obtain ⟨Φ₀, -, hrel, ⟨N, C, hmod⟩, hI⟩ := hc Φ' hΦ'
  have hp0 : p' Φ' = p' Φ₀ := by
    have := map_finRel_eq_zero hM hrel
    rwa [map_sub, sub_eq_zero] at this
  rw [hI Φ hΦ (hp.trans hp0)]
  congr 1
  have hlin : ∀ g h, thetaKO ωB g h (Φ' - Φ₀) = thetaKO ωB g h Φ' - thetaKO ωB g h Φ₀ := fun g h => by
    simp only [thetaKO, map_sub, _root_.Pi.sub_apply]
  have hint' : ∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h (Φ' - Φ₀)) 𝓕₁ ν₁ := fun h => by
    simp only [hlin]; exact (hint h).sub (hmod h).1
  have h0 := _root_.GlobalTheory.ThetaAgreeConv.thetaIntegral_eq_zero_of_finiteRelation hP hK hθ hT hν₁ hM.weilB hM.mapB.stabM.1 hrel hint'
  funext h
  have e := congrFun h0 h
  simp only [GlobalTheory.SquareComm.thetaInt, hlin, _root_.Pi.zero_apply] at e ⊢
  rw [MeasureTheory.integral_sub (hint h) (hmod h).1] at e
  exact (sub_eq_zero.1 e).symm
end GlobalTheory.ThetaAgreeConv
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegrals_agree_of_convergence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  first | exact @_root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel | exact _root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel | (intros; apply _root_.GlobalTheory.ThetaAgreeConv.thetaIntegrals_agree_of_integrable_kernel <;> assumption)
end
