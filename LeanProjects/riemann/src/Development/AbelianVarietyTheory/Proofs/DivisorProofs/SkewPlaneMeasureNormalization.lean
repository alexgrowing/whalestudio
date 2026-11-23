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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConjMaxCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneUnitaryStabiliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalBasisExtensionStatement

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons

theorem exists_induced : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
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
      ∀ ψ : GAd σ (c₀ • W₁.J.map σ) → ℂ, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ ψ →
      ∃ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' ∧
      ∃ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin (d + 1) → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin (d + 1) → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ ∧
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) ∧ ψs 0 = ψ ∧ (∀ i, a i 1 = if i = 0 then 1 else 0) ∧
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) ∧ (∃ U : Subgroup (GAd σ (c₀ • W.J.map σ)), IsOpen (U : Set (GAd σ (c₀ • W.J.map σ))) ∧ ∀ u ∈ U, u ∈ finPts σ (c₀ • W.J.map σ) → ∀ k ∈ Kc, k * u ∈ Kc ∧ ∀ i, a i (k * u) = a i k) ∧ (∀ i, ContinuousOn (a i) Kc) ∧ (∀ i, ∀ k ∈ Kc, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * (List.ofFn fun j => γ j (t j)).prod)) ∧ (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) Kc) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ k ∈ Kc, a i k = ∑ j, c j * b j k) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ k ∈ Kc, b j (k * k') = ∑ l, c l * b l k) := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0
    hXs S' χ hχ hχc K₁ hK₁ ψ hψ
  obtain ⟨hmul, hinv⟩ := GlobalTheory.T.isParDec_mul_and_inv F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs
  obtain ⟨K', hK', hemb, hyK, Kf, hKfc, hKff, ⟨U, hUo, hUK⟩, hdec⟩ := GlobalTheory.T.hyperbolic_plane_unitary_stabiliser F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' χ hχ hχc K₁ hK₁ ψ hψ
  obtain ⟨d, ψs, a, hψs, hψ0, ha1, hTL, ⟨U', hU'o, hU'⟩, hacont, hasm, hb⟩ :=
    GlobalTheory.T.hyperbolic_plane_orthogonal_basis_extension F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hιJ c₀ hc₀ hH1 hH M hMc hML hMr r Xf Yf hWf X' Y' hW' hX0 hY0 hXs S' χ hχ hχc K₁ hK₁ ψ hψ K' hK' hemb hyK Kf hKfc hKff U hUo hUK
  choose t y p hp k hk k₂ hk₂ hg using hdec
  refine ⟨K', hK', {g | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂}, d, ψs, a,
    fun g => (χ (t g) : ℂ) * ∑ i, ψs i (y g) * a i (k g * k₂ g), ⟨fun g => ?_, ?_⟩, hψs, hψ0, ha1, ⟨?_, ?_, ?_⟩, ?_, hacont, ?_, hb⟩
  · obtain ⟨u, hu, m, hm, he⟩ := hp g
    exact ⟨u, hu, t g, m, y g, _, ⟨k g, hk g, k₂ g, hk₂ g, rfl⟩, hm, by rw [← he]; exact hg g⟩
  · intro u hu t' m y' kk hkk hm
    obtain ⟨k0, hk0, k20, hk20, rfl⟩ := hkk
    have hP' : GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t' y'
        (u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y') := ⟨u, hu, m, hm, rfl⟩
    set g := u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y' * (k0 * k20) with hgdef
    have hq := hmul _ _ _ _ _ _ (hinv _ _ _ (hp g)) hP'
    have heq : (p g)⁻¹ * (u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y') * (k0 * k20) = k g * k₂ g := by
      rw [mul_assoc, ← hgdef, inv_mul_eq_iff_eq_mul]
      exact hg g
    have h := hTL _ _ _ hq k0 hk0 k20 hk20 (k g) (hk g) (k₂ g) (hk₂ g) heq (y g)
    show (χ (t g) : ℂ) * ∑ i, ψs i (y g) * a i (k g * k₂ g) = (χ t' : ℂ) * ∑ i, ψs i y' * a i (k0 * k20)
    rw [h, mul_inv_cancel_left, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]
  · have e : {g | ∃ k ∈ K', ∃ k₂ ∈ Kf, g = k * k₂} =
        (fun x : (GAd σ (c₀ • W.J.map σ)) × (GAd σ (c₀ • W.J.map σ)) => x.1 * x.2) '' ((K' : Set (GAd σ (c₀ • W.J.map σ))) ×ˢ (Kf : Set (GAd σ (c₀ • W.J.map σ)))) := by
      ext g
      constructor
      · rintro ⟨k, hk, k2, hk2, rfl⟩
        exact ⟨(k, k2), ⟨hk, hk2⟩, rfl⟩
      · rintro ⟨⟨k, k2⟩, ⟨hk, hk2⟩, rfl⟩
        exact ⟨k, hk, k2, hk2, rfl⟩
    rw [e]
    exact (hK'.1.2.prod hKfc).image continuous_mul
  · exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  · rintro _ ⟨k, hk, k2, hk2, rfl⟩ k' hk'
    refine ⟨k * k', mul_mem hk hk', k2, hk2, ?_⟩
    rw [mul_assoc, ← (GlobalTheory.StdPar.RealConj.commute_real_fin (hK'.1.1 hk') (hKff hk2)).eq, ← mul_assoc]
  · refine ⟨U' ⊓ U, by rw [Subgroup.coe_inf]; exact hU'o.inter hUo, ?_⟩
    rintro u hu hfin _ ⟨k, hk, k2, hk2, rfl⟩
    refine ⟨⟨k, hk, k2 * u, mul_mem hk2 (hUK ⟨hu.2, hfin⟩), mul_assoc _ _ _⟩, fun i => ?_⟩
    exact hU' u hu.1 hfin k hk k2 hk2 i
  · rintro i _ ⟨k, hk, k2, hk2, rfl⟩ e γ hγ hγK
    exact hasm i k hk k2 hk2 e γ hγ hγK

end GlobalTheory.ThK.InducedCons

end
