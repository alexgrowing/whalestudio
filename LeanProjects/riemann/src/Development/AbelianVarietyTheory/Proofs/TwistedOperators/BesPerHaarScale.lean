import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.Per

theorem besPer_haar_scale : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {A B : HSp D} {c : ℕ} {ε : D.host.E} (a : HermitianOrthogonalExtensionData A B c ε) (dd : BesDat A B a.ι), GlobalTheory.Unf.CoCpt A → ∀ (μ μ' : Measure (GA D A)) (𝓕 𝓕' : Set (GA D A)) (ν ν' : Measure (NFlag B dd.e)) (𝓝 𝓝' : Set (NFlag B dd.e)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → μ'.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕' μ' → GlobalTheory.Per.IsUnitN B dd.e ν 𝓝 → GlobalTheory.Per.IsUnitN B dd.e ν' 𝓝' → ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), (∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ B, ∀ g, F (γ * g) = F g) → ∃ r : ℝ, 0 < r ∧ GlobalTheory.Per.besPer ψ dd μ 𝓕 ν 𝓝 (stabilizerEmbedding a) φ F = r * GlobalTheory.Per.besPer ψ dd μ' 𝓕' ν' 𝓝' (stabilizerEmbedding a) φ F := by
  intro D ψ hψ A B c ε a dd _ μ μ' 𝓕 𝓕' ν ν' 𝓝 𝓝' hμ h𝓕 hμ' h𝓕' hN hN' φ F hφ hF
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B dd.e_iso
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A a.ι a.isom
  have hsa : stabilizerEmbedding a = s := funext fun h => ((embRel_iff a h _).1 ((hs _ _).2 rfl)).symm

  have hl : ∀ h, ∀ γ ∈ NFlagQ B dd.e, ∀ n : NFlag B dd.e,
      besFun ψ dd (stabilizerEmbedding a) φ F h (γ * n) = besFun ψ dd (stabilizerEmbedding a) φ F h n := by
    intro h γ hγ n
    simp only [besFun, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul ψ dd γ n γ.2 n.2, GlobalTheory.BesselChar.besChar_rat ψ hψ.1 dd γ γ.2 hγ, one_mul,
      mul_assoc (γ : GA D B), mul_assoc (γ : GA D B), hF (γ : GA D B) hγ]

  have e1 : ∀ h, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν = ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' :=
    fun h => GlobalTheory.Mem.TrueRecord.integral_unit _ hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 _ (hl h)

  have e2 : ∀ γ ∈ GQ A, ∀ g, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F (γ * g) n ∂ν =
      ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F g n ∂ν := by
    intro γ hγ g
    have r2 : EmbRel B A a.ι (s γ)⁻¹ γ⁻¹ := (hs _ _).2 (map_inv s _).symm
    have r1 : EmbRel B A a.ι (s γ) γ := (hs _ _).2 rfl
    let k : NFlag B dd.e ≃ₜ* NFlag B dd.e :=
      { toFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).1⟩
        invFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r1 n n.2).1⟩
        left_inv := fun n => Subtype.ext (by simp [mul_assoc])
        right_inv := fun n => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc])
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have hk : ∀ n, k n ∈ NFlagQ B dd.e ↔ n ∈ NFlagQ B dd.e := fun n => by
      change (s γ)⁻¹ * (n : GA D B) * (s γ)⁻¹⁻¹ ∈ GQ B ↔ (n : GA D B) ∈ GQ B
      rw [Subgroup.mul_mem_cancel_right _ (inv_mem (inv_mem (hq _ hγ))),
        Subgroup.mul_mem_cancel_left _ (inv_mem (hq _ hγ))]
    refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ hN.1 hN.2.1 hN.2.2 k hk _ (hl g))
    congr 1
    funext n
    have hc := (GlobalTheory.BesselChar.besChar_conj ψ dd _ _ r2 n n.2).2
    simp only [besFun, k, ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    rw [hc, hsa, hφ γ hγ, map_mul, ← hF _ (inv_mem (hq γ hγ)) ((n : GA D B) * (s γ * s g) * (dd.y : GA D B))]
    simp only [mul_assoc, inv_inv]

  have hc := Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ'
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  have hac : μ' ≪ μ := by
    intro t ht
    rw [e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left (by simpa using hc.ne')
  have h𝓕₁ : IsFundamentalDomain (GQ A) 𝓕 μ' := h𝓕.mono hac
  refine ⟨(μ.haarScalarFactor μ' : ℝ), by exact_mod_cast hc, ?_⟩
  show ∫ h in 𝓕, ∫ n in 𝓝, besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν ∂μ =
    _ * ∫ h in 𝓕', ∫ n in 𝓝', besFun ψ dd (stabilizerEmbedding a) φ F h n ∂ν' ∂μ'
  simp_rw [← e1]
  rw [← h𝓕₁.setIntegral_eq h𝓕' (fun γ g => e2 γ γ.2 g)]
  conv_lhs => rw [e]
  rw [Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end GlobalTheory.Per
