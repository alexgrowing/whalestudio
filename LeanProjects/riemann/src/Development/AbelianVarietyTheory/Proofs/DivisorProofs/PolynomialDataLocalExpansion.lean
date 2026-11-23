import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLinearStableRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThKGlobLoc

open Classical in

theorem exists_sum_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∃ (m : ℕ) (φ : Fin m → (Fin a × Fin (a + a') → Fv F B.v₁) → ℂ)
      (L : Fin m → ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (UA σ G.W.J → ℂ)),
      (∀ j, φ j ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁)) ∧ (∀ j, augAt om B.v₁ ≤ LinearMap.ker (L j)) ∧
      (∀ j, ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ ψ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁),
        ∀ ψ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om (1, h)) ψ ψ₁ →
          ∀ y, L j ψ₁ y = L j ψ (y * h)) ∧
      G.M.I om Φ = ∑ j, L j (φ j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT Φ hΦ
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hG := hT.geo.hM
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    left
    have h1 := hT.geo.eBig
    have h3 := hT.geo.lt
    omega
  have hlin := GlobalTheory.ThKLin.I_linear (GlobalTheory.T.weil_convergence_of_kernel hKP) F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond
  have hzero : ∀ h, G.M.I om 0 h = 0 := fun h => by simp [Model.I, theta, GlobalTheory.WeilM.thetaSum]
  let I₀ : GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) →ₗ[ℂ] (UA σ G.W.J → ℂ) :=
    { toFun := fun Ψ => G.M.I om Ψ.1
      map_add' := fun Ψ Ψ' => funext fun h => by
        have := hlin h _ Ψ.2 _ Ψ'.2 1
        rw [one_smul, one_mul] at this
        exact this
      map_smul' := fun c Ψ => funext fun h => by
        have := hlin h _ Ψ.2 _ (Submodule.zero_mem _) c
        rw [add_zero, hzero, add_zero] at this
        exact this }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend I₀
  have hl' : ∀ Ψ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), l Ψ = G.M.I om Ψ := fun Ψ hΨ =>
    LinearMap.congr_fun hl ⟨Ψ, hΨ⟩
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf φ h1 h2 h3 using fun i => (g i).2
  have hF : ∀ i, GlobalTheory.BigNZ.Fam G.M (φ i) := fun i => ⟨h1 i, h2 i⟩
  choose r hr er using fun i => GlobalTheory.PureFactor.exists_rest_factor B.v₁ (f i) (φ i) ((hF i).std hG)
  let TL : Fin m → ((Fin a × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] ((Fin a × Fin (a + a') → AF F) → ℂ) := fun i =>
    { toFun := fun χ => tens (evFin F B.v₁) χ (r i)
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }
  have hTL : ∀ i χ, TL i χ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (Function.update (φ i) B.v₁ χ) := fun i χ => er i χ
  have hmem : ∀ i, ∀ χ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁),
      TL i χ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := fun i χ hχ => by
    rw [hTL]; exact ((hF i).update _ hχ).mem hG _
  have hact : ∀ i Op, ∀ χ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F B.v₁), ∀ χ₁, Acts (evFin F B.v₁) Op χ χ₁ →
      TL i χ₁ = Op (TL i χ) := fun i Op χ hχ χ₁ ha => by
    rw [hTL, hTL, (hF i).acts hG (f i) hχ ha]
  refine ⟨m, fun i => φ i B.v₁, fun i => c i • (l ∘ₗ TL i), fun i => h1 i _, fun i => ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, -, χ, hχ, χ₁, hχ₁, ha, rfl⟩
    have e : l (TL i χ₁) = l (TL i χ) := by
      rw [hl' _ (hmem i χ₁ hχ₁), hl' _ (hmem i χ hχ), hact i _ χ hχ χ₁ ha]
      exact GlobalTheory.ThetaIntegralInv.integral_translate hKP.base hP u _ (hmem i χ hχ)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.comp_apply, map_sub, e, sub_self]
  · intro i h _ χ hχ χ₁ hχ₁ ha y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply]
    rw [hl' _ (hmem i χ₁ hχ₁), hl' _ (hmem i χ hχ), hact i _ χ hχ χ₁ ha, GlobalTheory.BigNZ.I_om]
  · have hS : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
      rw [← hg]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (by rw [h3]; exact (hF i).mem hG _)
    rw [← hl' _ hS, ← hg, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
    rw [hTL, Function.update_eq_self, h3]

end GlobalTheory.ThKGlobLoc

end
