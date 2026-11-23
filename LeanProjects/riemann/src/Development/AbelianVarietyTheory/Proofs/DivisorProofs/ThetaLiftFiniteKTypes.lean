import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearInPolynomialStatement

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKAutV.KFin

theorem I_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (h k : UA σ W.J) : M.I om Φ (h * k) = M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1
  funext g
  rw [show ((g, h * k) : UA σ X.J × UA σ W.J) = (g, h) * (1, k) by simp, map_mul, Module.End.mul_apply]

theorem kfin_thetaIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => G.M.I om Φ ((toGAd hσ G.W.J hc).symm (g * k)))) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  obtain ⟨K, hK, hKin⟩ := GlobalTheory.T.maximal_compact_of_skew_hermitian_twist F E σ hσ B _ _ _ G.W hT.base hT.geo.hW c hc hcs
  obtain ⟨S, hSf, hSle, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hKP
    (GlobalTheory.ThK.Inhab.pairV hT) Φ hΦ
  obtain ⟨L, hL⟩ := GlobalTheory.T.theta_integral_linear_in_polynomial F E σ B a a' G X om om' hKP hT
  refine ⟨K, hK, ?_⟩
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
  simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, hL, map_mul, I_mul_right]

end GlobalTheory.ThKAutV.KFin
