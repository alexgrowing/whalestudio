import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoThetaContinuousStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem theta_one_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (Φ : Fn F n d) (g : UA σ X.J)
    (h : UA σ W.J) : theta om Φ g h = theta om (om (1, h) Φ) g 1 := by
  simp only [theta]
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem continuous_I_of_weil (hKP : KP) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s')
    (hdim : d + 2 * min r s < 2 * n ∨ min r s = 0) (Φ : Fn F n d) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    Continuous (M.I om Φ) := by
  have hW := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B n d X W M χX χW om r s r' s' hP hdim
  have pres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) := fun x Ψ hΨ =>
    (IsUWeilPair.isUSplitting hP.weil).pres x Ψ hΨ
  have thAdd : ∀ Ψ₁ ∈ schA F (Fin n × Fin d), ∀ Ψ₂ ∈ schA F (Fin n × Fin d), ∀ g h,
      theta om (Ψ₁ + Ψ₂) g h = theta om Ψ₁ g h + theta om Ψ₂ g h := fun Ψ₁ h₁ Ψ₂ h₂ g h => by
    simp only [theta, map_add]
    exact thetaSum_add F (pres _ Ψ₁ h₁) (pres _ Ψ₂ h₂)
  have thSmul : ∀ (z : ℂ) Ψ g h, theta om (z • Ψ) g h = z * theta om Ψ g h := fun z Ψ g h => by
    simp only [theta, map_smul]
    exact thetaSum_smul F z _
  let L0 : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => M.I om Ψ.1 1
      map_add' := fun Ψ₁ Ψ₂ => by
        simp only [Submodule.coe_add, Model.I, thAdd _ Ψ₁.2 _ Ψ₂.2]
        exact integral_add ((hW.1 _ Ψ₁.2).1 1) ((hW.1 _ Ψ₂.2).1 1)
      map_smul' := fun z Ψ => by
        simp only [Submodule.coe_smul, Model.I, thSmul, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul z _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L0
  have hl' : ∀ Ψ (hΨ : Ψ ∈ schA F (Fin n × Fin d)), l Ψ = M.I om Ψ 1 := fun Ψ hΨ => by
    have := LinearMap.congr_fun hl ⟨Ψ, hΨ⟩
    simpa [L0] using this
  have hadm : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g hg
    have memA : ∀ f : SInf F (Fin n × Fin d), pureA F f g ∈ schA F (Fin n × Fin d) := fun f =>
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    let P : SInf F (Fin n × Fin d) →ₗ[ℂ] Fn F n d :=
      { toFun := fun f => pureA F f g
        map_add' := fun f₁ f₂ => funext fun x => by simp [pureA, add_mul]
        map_smul' := fun z f₁ => funext fun x => by simp [pureA, mul_assoc] }
    have hc : Continuous (l.comp P) := by
      have e : (l.comp P : SInf F (Fin n × Fin d) → ℂ) = fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f g) 1 :=
        funext fun f => hl' _ (memA f)
      rw [e]
      exact hW.2 g hg 1
    exact ⟨⟨l.comp P, hc⟩, fun f => rfl⟩
  have hc : Continuous fun p : UA σ X.J × UA σ W.J => l (om p Φ) := hP.weil.2.2 l hadm Φ hΦ
  have e : M.I om Φ = fun h => l (om (1, h) Φ) := funext fun h => by
    rw [hl' _ (pres _ _ hΦ)]
    simp only [Model.I]
    congr 1
    funext g
    exact theta_one_right om Φ g h
  rw [e]
  exact hc.comp (continuous_const.prodMk continuous_id)

theorem thCont : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → (∀ Φ ∈ PolData B G.M, Continuous (G.M.I om Φ) ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Continuous (G.M'.I om' Φ') ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M'.I om' Φ' (γ * h) = G.M'.I om' Φ' h := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT
  have hTB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hV : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV, skew := hT.geo.hW, good := hT.geo.hM, hX := hT.chars.heckeβ,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα, resX := hT.chars.resβ,
      resW := GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα, weil := hT.weil }
  have hV' : IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    { base := hT.base, herm := hT.geo.hV', skew := hT.geo.hW, good := hT.geo.hM', hX := hT.chars.heckeα,
      hW := GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeα hT.chars.heckeβ, resX := hT.chars.resα,
      resW := by rw [add_comm a a']; exact GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resα hT.chars.resβ, weil := hT.weil' }
  have hdim : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    have h3 := min_le_right (a - G.p) G.p
    omega
  refine ⟨fun Φ hΦ => ⟨continuous_I_of_weil hK B G.M hV (Or.inl hdim) Φ
      (GlobalTheory.ThKRatInv.polData_le_schA B G.M hT.geo.hM hΦ), GlobalTheory.ThKRatInv.I_rat_inv hTB B G.M hV Φ hΦ⟩,
    fun Φ' hΦ' => ⟨GlobalTheory.T.pol_data_so_theta_continuous hK F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hV' Φ' hΦ',
      GlobalTheory.ThKRatInv.I_rat_inv hTB B G.M' hV' Φ' (Submodule.mem_inf.1 hΦ').1⟩⟩

end GlobalTheory.ThKCont

end
