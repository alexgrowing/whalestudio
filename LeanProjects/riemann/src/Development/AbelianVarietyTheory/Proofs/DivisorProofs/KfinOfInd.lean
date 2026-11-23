import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.ThK.CuspTransfer

theorem kfin_of_ind : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) Kc) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ k ∈ Kc, a i k = ∑ j, c j * b j k) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ k ∈ Kc, b j (k * k') = ∑ l, c l * b l k) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun g => Ψ (g * k))) := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H _ _ _ _ _ _ _ c₀ hc₀ _ _ M _ _ _ r Xf Yf _ X' Y' _ _ _ _ S' χ _ _ K₁ _ K' _ Kc d ψs a Ψ hInd _ hKc hb
  obtain ⟨_, _, hKK⟩ := hKc
  obtain ⟨e, b, -, ha, hbt⟩ := hb
  choose ca hca using ha
  let S : Submodule ℂ ((GAd σ (c₀ • W.J.map σ) → ℂ) × (Fin d → Fin e → ℂ)) :=
    { carrier := {p | ∀ u ∈ GlobalTheory.StdPar.unip σ (c₀ • W.J.map σ) X' {0}, ∀ t m y, ∀ k ∈ Kc, IsLevi (W₁ := W₁) H t 1 m →
        p.1 (u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * emb hσ W W₁ hc₀ M y * k) =
          (χ t : ℂ) * ∑ i, ∑ l, p.2 i l * ψs i y * b l k}
      add_mem' := by
        intro p q hp hq u hu t m y k hk hL
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hp u hu t m y k hk hL, hq u hu t m y k hk hL]
        simp only [add_mul, Finset.sum_add_distrib, mul_add]
      zero_mem' := by
        intro u hu t m y k hk hL
        simp
      smul_mem' := by
        intro z p hp u hu t m y k hk hL
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hp u hu t m y k hk hL]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        ring }
  have hinj : Function.Injective ((LinearMap.snd ℂ _ _).comp S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨f, C⟩, hp⟩ h0
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.snd_apply] at h0
    subst h0
    ext g
    · obtain ⟨u, hu, t, m, y, k, hk, hL, rfl⟩ := hInd.1 g
      have := hp u hu t m y k hk hL
      simpa using this
    · rfl
  haveI : FiniteDimensional ℂ S := Module.Finite.of_injective _ hinj
  let V := S.map (LinearMap.fst ℂ _ _)
  haveI : FiniteDimensional ℂ V := inferInstance
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ : _ ≤ V)
  rintro _ ⟨⟨k', hk'⟩, rfl⟩
  choose D hD using hbt
  refine ⟨(fun g => Ψ (g * k'), fun i l => ∑ j, ca i j * D j k' hk' l), ?_, rfl⟩
  intro u hu t m y k hk hL
  show Ψ (_ * k') = _
  have hkk := hKK k hk k' hk'
  rw [mul_assoc _ k k', hInd.2 u hu t m y (k * k') hkk hL]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hca i (k * k') hkk]
  simp only [fun j => hD j k' hk' k hk, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ThK.CuspTransfer
