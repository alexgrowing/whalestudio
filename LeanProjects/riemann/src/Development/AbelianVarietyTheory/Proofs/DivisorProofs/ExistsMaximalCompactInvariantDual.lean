import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubgroupFixesPolynomialDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialThetaKernelCenterFiniteStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ThAutSmall

open GlobalTheory.WeilM GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_small {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem so_le_schA {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ)
    {v : Pl F} (t : E →ₐ[F] Fv F v) : M.So ψ t ≤ schA F _ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  have h3 := (h2.and hM.std).mono fun w hw => hw.1.trans hw.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

end GlobalTheory.ThAutSmall

namespace GlobalTheory.ThAutSmall

open GlobalTheory.ThK

theorem left_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ γ ∈ ratPts σ (c • G.W.J.map σ), ∀ g, (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) (γ * g) = (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) g := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ γ hγ g
  have hr : (toGAd hσ G.W.J hc).symm γ ∈ ratU σ G.W.J := by
    have h1 : γ.1 ∈ HFin (AF F) σ (c • G.W.J.map σ) := hγ
    obtain ⟨y, -, e⟩ := Subgroup.mem_map.1 h1
    exact ⟨y, e⟩
  have hb := ((GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _
    (GlobalTheory.ThAutSmall.isPair_small hT)).1 Φ (GlobalTheory.ThAutSmall.so_le_schA hT.geo.hM' _ (Submodule.mem_inf.1 hΦ).2)).2.1
  simp only [map_mul]
  unfold Model.I
  congr 1
  funext g'
  simpa using hb 1 (one_mem _) _ hr g' ((toGAd hσ G.W.J hc).symm g)

theorem isAut_theta_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧
        IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ
  obtain ⟨K, hK1, hK2⟩ := GlobalTheory.T.polynomial_theta_kernel_finite_type F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ
  exact ⟨K, hK1, ⟨left_inv F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ, GlobalTheory.T.open_subgroup_fixes_polynomial_datum F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ,
    GlobalTheory.T.polynomial_theta_kernel_continuous F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ, GlobalTheory.T.polynomial_theta_kernel_smooth F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ,
    GlobalTheory.T.polynomial_theta_kernel_moderate_growth F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ⟩, hK2, GlobalTheory.T.polynomial_theta_kernel_center_finite F E σ hσ B a a' G X om om' hK hT c hc hcs Φ hΦ⟩

end GlobalTheory.ThAutSmall
