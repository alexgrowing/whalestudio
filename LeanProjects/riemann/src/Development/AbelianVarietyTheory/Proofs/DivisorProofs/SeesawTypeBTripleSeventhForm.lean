import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMapsSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdCommOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinVac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorNeZeroStatement

noncomputable section

namespace GlobalTheory.ConeNonAug

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open scoped Classical

theorem exists_soLoc_coneFin_not_mem_augAt : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μKv : Measure (KAt K (evFin F B.v₁))) (μv : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μKv → IsNormE E B.v₁ μv →
    ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁, coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∉ augAt om₁' B.v₁ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hpure K hK μKv μv hμK hμ
  have hPr := hKP.base
  have hv : B.v₁ ∉ X.T := hT.chars.good.1
  have hloc : LemF.IsLocPart G.M' G₁.M' e' ei ev := ⟨hei, hev, hpure⟩
  have hA := GlobalTheory.T.theta_action_exists hPr
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) → (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ,
      Λ = coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) := ⟨_, rfl⟩
  rw [← hΛ]

  have hlin : ∀ (c d : ℂ), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      ∀ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), Λ (c • φ + d • φ') = c • Λ φ + d • Λ φ' := by
    intro c d φ hφ φ' hφ'
    obtain ⟨N, f, cc, -, h1, h2, h3⟩ := GlobalTheory.T.config_b_local_part_stabilizer hPr F E σ B a b G G₁ H H' hC e' he' ei ev hloc K hK X om om' om₁ om₁'
      hT hT₁ B.v₁ μKv μv hμK.1 hμ.1 ((a - (b + 2)) / 2 + 1) (Nat.le_add_left 1 _) φ hφ
    obtain ⟨N', f', cc', -, h1', h2', h3'⟩ := GlobalTheory.T.config_b_local_part_stabilizer hPr F E σ B a b G G₁ H H' hC e' he' ei ev hloc K hK X om om' om₁
      om₁' hT hT₁ B.v₁ μKv μv hμK.1 hμ.1 ((a - (b + 2)) / 2 + 1) (Nat.le_add_left 1 _) φ' hφ'
    subst hΛ
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine coneFin_lin hT.base.std.1 (fun k hk ψ hψ =>
      ((hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP' B.v₁).1 k (mem_KAt.1 hk).2 1 (LemF.one_mem_UAt _ _) ψ hψ).exists)
      c d hφ hφ' y (fun k => ?_) (fun k => ?_) ?_ ?_
    · exact (integrable_finsetSum _ fun i _ => (h1 i k).mul_const (f i y)).congr
        (Eventually.of_forall fun l => by simp only []; rw [h3 k l y])
    · exact (integrable_finsetSum _ fun i _ => (h1' i k).mul_const (f' i y)).congr
        (Eventually.of_forall fun l => by simp only []; rw [h3' k l y])
    · have e : ∀ k, ∫ l, coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y ∂μv =
          ∑ i, (∫ l, cc i k l ∂μv) * f i y := fun k => by
        have hc : (∫ l, coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ k.1 l.1 y ∂μv) =
            ∫ l, ∑ i, cc i k l * f i y ∂μv :=
          integral_congr_ae (Eventually.of_forall fun l => by simp only []; rw [h3 k l y])
        rw [hc, integral_finsetSum _ fun i _ => (h1 i k).mul_const _]
        exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
      exact (integrable_finsetSum _ fun i _ => (h2 i).mul_const (f i y)).congr
        (Eventually.of_forall fun k => by simp only []; rw [e k])
    · have e : ∀ k, ∫ l, coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ' k.1 l.1 y ∂μv =
          ∑ i, (∫ l, cc' i k l ∂μv) * f' i y := fun k => by
        have hc : (∫ l, coneFinInt B G.M' om' B.v₁ (ev B.v₁) (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ' k.1 l.1 y ∂μv) =
            ∫ l, ∑ i, cc' i k l * f' i y ∂μv :=
          integral_congr_ae (Eventually.of_forall fun l => by simp only []; rw [h3' k l y])
        rw [hc, integral_finsetSum _ fun i _ => (h1' i k).mul_const _]
        exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
      exact (integrable_finsetSum _ fun i _ => (h2' i).mul_const (f' i y)).congr
        (Eventually.of_forall fun k => by simp only []; rw [e k])
  have hSBaug : augAt om' B.v₁ ≤ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) :=
    Submodule.span_le.2 (by rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩; exact sub_mem hφ₁ hφ)
  have hzero : Λ 0 = 0 := by
    have := hlin 0 0 0 (zero_mem _) 0 (zero_mem _)
    simpa using this

  have hF := (GlobalTheory.ThK.LemF.lemF hPr).2.2.2.2.2.2.2.2.2.2.2.2.1 F E σ B a b G G₁ H H' hC e' he' ei ev hloc K hK X om om'
    om₁ om₁' hT hT₁ B.v₁ μKv μv hμK.1 hμ.1
  have haug : ∀ z ∈ augAt om' B.v₁, Λ z ∈ augAt om₁' B.v₁ := by
    intro z hz
    unfold augAt at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, φ, hφ, φ₁, hφ₁, hact, rfl⟩ := hx
      have e1 : φ₁ = locOp B.v₁ (om' (g, 1)) φ := (locOp_eq hφ hφ₁ hact).symm
      have hq := hF.2.2 _ (augAt om₁' B.v₁).mkQ (by rw [Submodule.ker_mkQ]) g hg 1 (LemF.one_mem_UAt _ _) φ hφ
      rw [LemF.locOp_one om' B.v₁ (locOp_mem _ _ _), LemF.locOp_one om' B.v₁ hφ, ← e1, ← hΛ] at hq
      have hs : φ₁ - φ = (1 : ℂ) • φ₁ + (-1 : ℂ) • φ := by simp [sub_eq_add_neg]
      rw [hs, hlin 1 (-1) φ₁ hφ₁ φ hφ]
      have := (Submodule.Quotient.eq _).1 hq
      simpa [sub_eq_add_neg] using this
    | zero => rw [hzero]; exact zero_mem _
    | add x y hx hy ihx ihy =>
      have := hlin 1 1 x (hSBaug hx) y (hSBaug hy)
      simp only [one_smul] at this
      rw [this]
      exact add_mem ihx ihy
    | smul c x hx ih =>
      have := hlin c 0 x (hSBaug hx) 0 (zero_mem _)
      simp only [zero_smul, add_zero, smul_zero] at this
      rw [this]
      exact Submodule.smul_mem _ c ih

  have hvacSB := (hT.geo.hM'.vac B.v₁).1
  obtain ⟨φ₀, hφ₀, hdiff⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hPr F E σ B a (b + 2) G X om om' hT B.v₁ hT.chars.good
    (GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a (b + 2) G X om om' hT B.v₁ hT.chars.good) B.τ₁ (G.M'.vac B.v₁) hvacSB
  refine ⟨φ₀, hφ₀, fun hmem => ?_⟩
  have hφ₀SB : φ₀ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) := by
    have := sub_mem hvacSB (hSBaug hdiff)
    simpa using this
  have h1 := haug _ hdiff
  have hs : G.M'.vac B.v₁ - φ₀ = (1 : ℂ) • G.M'.vac B.v₁ + (-1 : ℂ) • φ₀ := by simp [sub_eq_add_neg]
  rw [hs, hlin 1 (-1) _ hvacSB φ₀ hφ₀SB] at h1
  have h2 : Λ (G.M'.vac B.v₁) ∈ augAt om₁' B.v₁ := by
    have := add_mem h1 hmem
    simpa using this

  rw [hΛ, GlobalTheory.LemUB.coneFin_vac B hC hT hT₁.geo he' hei hev hpure hK hv hμK hμ] at h2
  have hc := GlobalTheory.T.unramified_factor_ne_zero F E B X a (b + 2) hT.chars (H.𝔟⁻¹ * conjI σ H'.𝔟) ((a - (b + 2)) / 2 + 1)
    (Nat.le_add_left 1 _) B.v₁ hv
  have h3 := (Submodule.smul_mem_iff _ hc).1 h2

  obtain ⟨R, -, -, -, hp', -, -, -, hsph, -⟩ := GlobalTheory.T.exists_finite_maps_split_place hPr (GlobalTheory.T.howe_duality_of_minguez hKP.minguezThetaGL) F E σ B a b G₁ X om₁ om₁'
    hT₁ B.v₁ ⟨B.τ₁⟩
  obtain ⟨he, hne⟩ := hsph hv
  apply hne
  rw [he]
  exact hp' h3

end GlobalTheory.ConeNonAug

end
