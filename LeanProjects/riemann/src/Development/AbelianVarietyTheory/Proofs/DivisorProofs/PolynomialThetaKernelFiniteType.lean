import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThKAutSmallKFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem I_mul_right {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h k : UA σ W.J) : M.I om Φ (h * k) = M.I om (om (1, k) Φ) h := by
  unfold Model.I theta
  congr 1
  funext g
  rw [show ((g, h * k) : UA σ Y.J × UA σ W.J) = (g, h) * (1, k) by simp, map_mul, Module.End.mul_apply]

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem conv_so (hP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (hΨ : Ψ ∈ G.M'.So B.ψ B.τ₁) : G.M'.Conv om' Ψ := by
  intro h
  have hPair := GlobalTheory.ThKContSmall.isPair_small hT
  have hS : Ψ ∈ GlobalTheory.WeilM.schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ hΨ
  have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Ψ hS
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Ψ hΨ 0
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
  refine Measure.integrableOn_of_bounded (M := C * (ht h : ℝ) ^ k) hv.ne
    (hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  have h1 := hC g h
  rwa [pow_zero, mul_one] at h1

theorem I_add_so (hP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {Ψ₁ Ψ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ}
    (h₁ : Ψ₁ ∈ G.M'.So B.ψ B.τ₁) (h₂ : Ψ₂ ∈ G.M'.So B.ψ B.τ₁) :
    G.M'.I om' (Ψ₁ + Ψ₂) = G.M'.I om' Ψ₁ + G.M'.I om' Ψ₂ := by
  funext h
  have s₁ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ h₁
  have s₂ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ h₂
  have e : ∀ g, theta om' (Ψ₁ + Ψ₂) g h = theta om' Ψ₁ g h + theta om' Ψ₂ g h := fun g => by
    simp only [theta, map_add]
    exact GlobalTheory.WeilM.thetaSum_add F (hT.weil'.isUSplitting.pres _ _ s₁) (hT.weil'.isUSplitting.pres _ _ s₂)
  simp only [Model.I, e, Pi.add_apply]
  exact integral_add (conv_so hP hT h₁ h) (conv_so hP hT h₂ h)

theorem I_smul {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (om : Rep σ Y W)
    (t : ℂ) (Ψ : (Fin n × Fin d → AF F) → ℂ) : M.I om (t • Ψ) = t • M.I om Ψ := by
  funext h
  simp only [Model.I, theta, map_smul, GlobalTheory.WeilM.thetaSum_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]

theorem kfin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun g => (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) (g * k))) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ
  obtain ⟨K, hK, hKin⟩ := GlobalTheory.T.maximal_compact_of_skew_hermitian_twist F E σ hσ B _ _ _ G.W hT.base hT.geo.hW c hc hcs
  have hΦS : Φ ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ).2
  obtain ⟨S, hSf, -, hS⟩ := GlobalTheory.T.polynomial_datum_finite_dimensional_orbit F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hKP
    (GlobalTheory.ThKContSmall.isPair_small hT) Φ (Submodule.mem_inf.1 hΦ).1
  let P := G.M'.So B.ψ B.τ₁
  let L : P →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Ψ => G.M'.I om' Ψ
      map_add' := fun Ψ₁ Ψ₂ => I_add_so hKP hT Ψ₁.2 Ψ₂.2
      map_smul' := fun t Ψ => I_smul G.M' om' t Ψ }
  let S' : Submodule ℂ P := S.comap P.subtype
  haveI : FiniteDimensional ℂ S := hSf
  haveI : FiniteDimensional ℂ S' :=
    FiniteDimensional.of_injective (K := ℂ) (V₂ := S) ((P.subtype.domRestrict S').codRestrict S fun x => x.2)
      fun x y e => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : GlobalTheory.ThK.Fn F a' (a + a'))) e))
  let T : P →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    LinearMap.funLeft ℂ ℂ (toGAd hσ G.W.J hc).symm ∘ₗ L
  refine ⟨K, hK, Submodule.finiteDimensional_of_le (S₂ := S'.map T) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  have hk := hS _ (hKin k k.2)
  refine ⟨⟨om' (1, (toGAd hσ G.W.J hc).symm k) Φ, GlobalTheory.T.weil_representation_preserves_space hKP.base F E σ B a a' G X om om' hT _ Φ hΦS⟩, hk, ?_⟩
  funext g
  simp only [T, L, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, I_mul_right]

end GlobalTheory.ThKAutSmallKFin

end
