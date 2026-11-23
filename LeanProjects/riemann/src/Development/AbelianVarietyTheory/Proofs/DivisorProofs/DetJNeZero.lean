import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.LeviGenZFin

theorem det_ne_zero_of_cartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have hs : star v ≠ 0 := fun e => hv (by simpa using congrArg star e)
  have := h.2.2 (star v) hs
  simp [star_star, hMv] at this

theorem det_J_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (B : Base F E) {n : ℕ} (Y : Spc F E n) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) :
    Y.J.det ≠ 0 := by
  intro hd
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_cartan (h w)
  have e : (Y.J.map (B.emb w).1).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]
  rw [Matrix.det_smul, e, mul_zero]

theorem isHermND_smul {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) {c : E} (hc : c ≠ 0)
    (hcs : σ c = -c) : IsHermND σ (c • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hcs]
    have := congrArg σ (hJ i j)
    rw [hσ, map_neg] at this
    rw [this]; ring
  · rw [Matrix.det_smul, ← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hc) (by simpa using fun e => hd (by simpa [hσ] using congrArg σ e))

end GlobalTheory.LeviGenZFin

namespace GlobalTheory.LeviGenZFin

theorem zfin_of_hc (hHC : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ →
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y.J.det ≠ 0 →
    Y₁.J.det ≠ 0 → ∀ ψ : UA σ Y.J → ℂ, (∀ u ∈ unip σ Y H, ∀ x, ψ (u * x) = ψ x) →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    (∀ φ : GAd σ (c • Y.J.map σ) → ℂ, (∀ (g : UA σ Y.J) (g' : GAd σ (c • Y.J.map σ)), g.1 = g'.1 → φ g' = ψ g) →
      GlobalTheory.UAut.IsSm σ (c • Y.J.map σ) φ ∧
        FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ})) →
    ∀ (h : UA σ Y.J) (g : UA σ Y₁.J → ℂ), (∀ h₁ m, IsLevi (W₁ := Y₁) H 1 h₁ m → g h₁ = ψ (m * h)) →
    ∀ φ₁ : GAd σ (c • Y₁.J.map σ) → ℂ, (∀ (g₁ : UA σ Y₁.J) (g' : GAd σ (c • Y₁.J.map σ)), g₁.1 = g'.1 → φ₁ g' = g g₁) →
      FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, GlobalTheory.UAut.IsCentral σ (c • Y₁.J.map σ) z ∧ u = GlobalTheory.UAut.dop z φ₁})) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      FiniteDimensional ℂ (Submodule.span ℂ {φ | ∃ z, IsCentral σ (c • Y₁.J.map σ) z ∧ φ = dop z (fun x => g ((toGAd hσ Y₁.J hc).symm x))}) := by
  intro F E _ _ _ _ _ σ hσ B hB n n₁ Y Y₁ P hY hP c hc hcs fa hfa h hh hlev g hg
  obtain ⟨hn, hxx, hyy, hxy, hort, hι, hcY, hcY₁⟩ := hP
  have hdY : Y.J.det ≠ 0 := det_J_ne_zero B Y hcY
  have hdY₁ : Y₁.J.det ≠ 0 := det_J_ne_zero B Y₁ fun w => hcY₁ w
  have hY₁ : ∀ i j, σ (Y₁.J j i) = -Y₁.J i j := by
    intro i j
    rw [← hι]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    simp only [map_sum, map_mul, hσ, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hY]; ring
  have hA := hfa ⊥ fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]
    exact ⟨by simp [UAt, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At], fun w => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat]⟩
  refine hHC Y Y₁ P hB.cm hY hn hxx hyy hxy hort hι hdY hdY₁ fa (fun u hu x => ?_) c hc
    (isHermND_smul hσ hY hdY hc hcs) (isHermND_smul hσ hY₁ hdY₁ hc hcs) (fun φ hφ => ?_) h g hg _ (fun g₁ g' e => ?_)
  · have := hA.left (toGAd hσ Y.J hc u) ⟨u, hu, rfl⟩ (toGAd hσ Y.J hc x)
    simpa only [← map_mul, MulEquiv.symm_apply_apply] using this
  · have e : φ = fun x => fa ((toGAd hσ Y.J hc).symm x) := funext fun x => hφ _ x rfl
    subst e
    exact ⟨hA.smooth, hA.zfin⟩
  · show g ((toGAd hσ Y₁.J hc).symm g') = g g₁
    congr 1
    exact Subtype.ext e.symm

theorem zfin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      FiniteDimensional ℂ (Submodule.span ℂ {φ | ∃ z, IsCentral σ (c • Y₁.J.map σ) z ∧ φ = dop z (fun x => g ((toGAd hσ Y₁.J hc).symm x))}) :=
  fun hK => zfin_of_hc hK.leviCentreFiniteUnitary

end GlobalTheory.LeviGenZFin
