import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalCompactInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataThetaLinearStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKAutBoth

theorem I_mul_right' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (h k : UA σ W.J) : M.I om Φ (h * k) = M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1
  funext g
  rw [show ((g, h * k) : UA σ X.J × UA σ W.J) = (g, h) * (1, k) by simp, map_mul, Module.End.mul_apply]

theorem so_stable_kinf (hK : GlobalTheory.ThK.KP) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') {k : UA σ G.W.J} (hk : k ∈ KInf σ G.W B.emb)
    {Φ : GlobalTheory.ThK.Fn F a' (a + a')} (hΦ : Φ ∈ G.M'.So B.ψ B.τ₁) : om' (1, k) Φ ∈ G.M'.So B.ψ B.τ₁ := by
  have h1 : At (evI F) (mat (1 : UA σ G.V'.J) - 1) := by
    intro u _
    simp [mat]
  have hloc := GlobalTheory.T.archimedean_theta_local_action hK.base F E σ B a a' G X om om' hT 1 k h1 hk.1
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hSB, hvac, hv₁, rfl⟩ := hx
    obtain ⟨f₂, e⟩ := hloc f φ hSB hvac
    rw [e]
    exact Submodule.subset_span ⟨f₂, φ, hSB, hvac, hv₁, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GlobalTheory.ThKAutBoth

namespace GlobalTheory.ThKAutBoth

theorem isAut_both : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Φ' ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) ∧
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ' ((toGAd hσ G.W.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ Φ' hΦ'
  obtain ⟨K, hK, hKin⟩ := GlobalTheory.T.maximal_compact_of_skew_hermitian_twist F E σ hσ B _ _ _ G.W hT.base hT.geo.hW c hc hcs
  obtain ⟨K₁, -, hA⟩ := GlobalTheory.T.exists_maximal_compact_invariant F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  obtain ⟨K₂, -, hA'⟩ := GlobalTheory.T.exists_maximal_compact_invariant_dual F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ' hΦ'
  refine ⟨K, hK, ⟨hA.mod, ?_, hA.zfin⟩, ⟨hA'.mod, ?_, hA'.zfin⟩⟩
  · obtain ⟨S, hSf, hSle, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hKP
      (GlobalTheory.ThK.Inhab.pairV hT) Φ hΦ
    obtain ⟨L, hL⟩ := GlobalTheory.T.theta_integral_linear_in_polynomial F E σ B a a' G X om om' hKP hT
    let P := GlobalTheory.ThK.PolData B G.M
    let S' : Submodule ℂ P := S.comap P.subtype
    haveI : FiniteDimensional ℂ S := hSf
    haveI : FiniteDimensional ℂ S' :=
      FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((P.subtype.domRestrict S').codRestrict S fun x => x.2)
        fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : GlobalTheory.ThK.Fn F a (a + a'))) e))
    let T : P →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
      LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L
    refine Submodule.finiteDimensional_of_le (S₂ := S'.map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk := hS _ (hKin k k.2)
    refine ⟨⟨om (1, (toGAd hσ G.W.J hc).symm k) Φ, hSle hk⟩, hk, ?_⟩
    funext g
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, hL, map_mul, I_mul_right']
  · obtain ⟨S, hSf, hSle, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hKP
      (GlobalTheory.ThK.Inhab.pairV' hT) Φ' (Submodule.mem_inf.1 hΦ').1
    obtain ⟨L, hL⟩ := GlobalTheory.T.pol_data_theta_linear F E σ B a a' G X om om' hKP hT
    let P := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁
    let S' : Submodule ℂ P := S.comap P.subtype
    haveI : FiniteDimensional ℂ S := hSf
    haveI : FiniteDimensional ℂ S' :=
      FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((P.subtype.domRestrict S').codRestrict S fun x => x.2)
        fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : GlobalTheory.ThK.Fn F a' (a + a'))) e))
    let T : P →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
      LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L
    refine Submodule.finiteDimensional_of_le (S₂ := S'.map T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have hk := hS _ (hKin k k.2)
    have hso := so_stable_kinf hKP hT (hKin k k.2) (Submodule.mem_inf.1 hΦ').2
    refine ⟨⟨om' (1, (toGAd hσ G.W.J hc).symm k) Φ', Submodule.mem_inf.2 ⟨hSle hk, hso⟩⟩, hk, ?_⟩
    funext g
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, hL, map_mul, I_mul_right']

end GlobalTheory.ThKAutBoth
