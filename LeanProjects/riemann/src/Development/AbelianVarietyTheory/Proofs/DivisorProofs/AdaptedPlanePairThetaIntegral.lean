import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairConverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreservesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixXUnip

theorem unip_trivial : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ u ∈ unip σ X H, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (u, 1) Φ) = e Φ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he u hu
  have hS := IsUWeilPair.isUSplitting hP.weil
  have pres : ∀ g Φ, Φ ∈ schA F (Fin n × Fin d) → om g Φ ∈ schA F (Fin n × Fin d) := fun g Φ h => hS.pres g Φ h
  have omul : ∀ g h : UA σ X.J, ∀ Φ, om (g * h, 1) Φ = om (g, 1) (om (h, 1) Φ) := fun g h Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have om1 : ∀ Φ, om (1, 1) Φ = Φ := fun Φ => by
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  have twist : ∀ (g : UA σ X.J) (a : AE F E), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ b : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ := by
    intro g a ha hb
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitian_adapted_pair_of_pair F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a ha hb
    refine GlobalTheory.T.hermitian_adapted_plane_local hPr F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he
      (e ∘ₗ om (g, 1)) h1 h2 fun y => ?_
    have := hS.adm (g, 1) _ (GlobalTheory.T.hermitian_adapted_pair_converse F E σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he y)
    rwa [LinearMap.comp_assoc] at this
  by_cases h0 : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = 0
  · intro Φ hΦ
    rw [h0 _ (pres _ _ hΦ), h0 _ hΦ]
  push_neg at h0
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  let Q : UA σ X.J → ℂ → Prop := fun g c => ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) Φ) = c • e Φ
  have Quniq : ∀ g c c', Q g c → Q g c' → c = c' := fun g c c' h h' =>
    smul_left_injective ℂ hne ((h Φ₀ hΦ₀).symm.trans (h' Φ₀ hΦ₀))
  have Qmul : ∀ g h c c', Q g c → Q h c' → Q (g * h) (c * c') := fun g h c c' hg hh Φ hΦ => by
    rw [omul, hg _ (pres _ _ hΦ), hh _ hΦ, smul_smul]
  have Qone : Q 1 1 := fun Φ _ => by rw [om1, one_smul]
  have Qinv : ∀ g c, Q g c → c ≠ 0 ∧ Q g⁻¹ c⁻¹ := by
    intro g c hg
    have key : ∀ Φ ∈ schA F (Fin n × Fin d), e Φ = c • e (om (g⁻¹, 1) Φ) := fun Φ hΦ => by
      rw [← hg _ (pres _ _ hΦ), ← omul, mul_inv_cancel, om1]
    have hc : c ≠ 0 := fun h => hne (by rw [key _ hΦ₀, h, zero_smul])
    exact ⟨hc, fun Φ hΦ => by rw [key Φ hΦ, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have Qpow : ∀ g c, Q g c → ∀ k : ℕ, Q (g ^ k) (c ^ k) := by
    intro g c hg k
    induction k with
    | zero => simpa using Qone
    | succ k ih => rw [pow_succ, pow_succ]; exact Qmul _ _ _ _ ih hg

  have gen : ∀ g : UA σ X.J, mat g *ᵥ incV F H.x = incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) → Q g 1 := by
    intro g hgx hgz
    obtain ⟨cu, hcu⟩ := twist g 1 (by rw [one_smul]; exact hgx) hgz
    have scl : ∀ t : ℕ, t ≠ 0 → ∃ m : UA σ X.J, (mat m *ᵥ incV F H.x = (t : AE F E) • incV F H.x ∧
        (t : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y ∧ ∀ z : Fin n₁ → AE F E, mat m *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z) ∧
        ∃ c, Q m c := by
      intro t ht
      obtain ⟨m, h1, h2, h3⟩ := GlobalTheory.T.exists_unitary_scaling_vector F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hH hP.herm hP₁.herm
        (GlobalTheory.PlaneLevi.invol_of_good hP.base) t ht
      exact ⟨m, ⟨h1, h2, h3⟩, twist m _ h1 fun z => ⟨0, by rw [zero_smul, add_zero, h3]⟩⟩
    obtain ⟨m, ⟨hm1, hm2, hm3⟩, cm, hcm⟩ := scl 2 two_ne_zero
    have hm1' : mat m *ᵥ incV F H.x = (2 : AE F E) • incV F H.x := by exact_mod_cast hm1
    have hm2' : (2 : AE F E) • (mat m *ᵥ incV F H.y) = incV F H.y := by exact_mod_cast hm2
    obtain ⟨hcm0, hcmi⟩ := Qinv _ _ hcm
    obtain ⟨hcu0, hcui⟩ := Qinv _ _ hcu
    set v := g⁻¹ * g⁻¹ * (m * g * m⁻¹) with hv
    have hQv : Q v (cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹)) :=
      Qmul _ _ _ _ (Qmul _ _ _ _ hcui hcui) (Qmul _ _ _ _ (Qmul _ _ _ _ hcm hcu) hcmi)
    set cv := cu⁻¹ * cu⁻¹ * (cm * cu * cm⁻¹) with hcv
    have hcv' : cv = cu⁻¹ := by rw [hcv]; field_simp
    have step : ∀ t : ℕ, t ≠ 0 → cv ^ (t ^ 2) = cv := by
      intro t ht
      obtain ⟨m', ⟨h1, h2, h3⟩, cm', hcm'⟩ := scl t ht
      obtain ⟨hcm0', hcmi'⟩ := Qinv _ _ hcm'
      have e1 := Qmul _ _ _ _ (Qmul _ _ _ _ hcm' hQv) hcmi'
      rw [GlobalTheory.T.unitary_fixing_vector_preserves F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hH hP.herm hP₁.herm g hgx hgz m m' t hm1' hm2' hm3 h1 h2 h3] at e1
      have := Quniq _ _ _ (Qpow _ _ hQv (t ^ 2)) e1
      rw [this]; field_simp
    have hcv0 : cv ≠ 0 := by rw [hcv']; exact inv_ne_zero hcu0
    have s2 := step 2 two_ne_zero
    have s3 := step 3 three_ne_zero
    norm_num at s2 s3
    have c3 : cv ^ 3 = 1 := by
      have : cv * (cv ^ 3 - 1) = 0 := by linear_combination s2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hcv0)
    have c1 : cv = 1 := by rw [← s3, show 9 = 3 * 3 from rfl, pow_mul, c3, one_pow]
    have : cu = 1 := by rw [hcv', inv_eq_one] at c1; exact c1
    rw [← this]; exact hcu

  have hcl : ∀ g ∈ unip σ X H, Q g 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact gen g hg.1 hg.2
    | one => exact Qone
    | mul g h _ _ ihg ihh => simpa using Qmul _ _ _ _ ihg ihh
    | inv g _ ih => simpa using (Qinv _ _ ih).2
  intro Φ hΦ
  simpa using hcl u hu Φ hΦ

end GlobalTheory.MixXUnip
