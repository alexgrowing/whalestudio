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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons

theorem mem_infPts_iff_map {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) :
    g ∈ infPts σ J ↔ (g.1.1 : Matrix (Fin n) (Fin n) (AE F E)).map
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom = 1 := by
  rw [infPts, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

theorem levi_map_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {R : Type} [CommRing R] (φ : AE F E →+* R) {h₁ : UA σ W₁.J} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H 1 h₁ m)
    (h1 : (mat h₁).map φ = 1) : (mat m).map φ = 1 := by
  obtain ⟨ax, ay, aι⟩ := hm
  simp only [inv_one, Units.val_one, map_one, one_smul] at ax ay
  ext i j
  obtain ⟨α, β, z, e⟩ := h.decompA hσ hsk hd (Pi.single j 1)
  have e1 : mat m i j = (mat m *ᵥ (Pi.single j 1 : Fin n → AE F E)) i := by
    simp
  have e2 : (1 : Matrix (Fin n) (Fin n) R) i j = φ ((Pi.single j 1 : Fin n → AE F E) i) := by
    simp [Matrix.one_apply, Pi.single_apply, apply_ite φ]
  have e3 : ∀ k, φ ((mat h₁ *ᵥ z) k) = φ (z k) := fun k => by
    rw [RingHom.map_mulVec, h1, Matrix.one_mulVec]; rfl
  have e4 : φ ((incM F H.ι *ᵥ (mat h₁ *ᵥ z)) i) = φ ((incM F H.ι *ᵥ z) i) := by
    rw [RingHom.map_mulVec, RingHom.map_mulVec]
    congr 1
    funext k
    exact e3 k
  rw [Matrix.map_apply, e1, e2, e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, ax, ay, Matrix.mulVec_mulVec, aι]
  rw [← Matrix.mulVec_mulVec]
  simp only [Pi.add_apply, map_add, e4]

theorem exists_compact_emb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), K₁ ≤ infPts σ (c₀ • W₁.J.map σ) → IsCompact (K₁ : Set (GAd σ (c₀ • W₁.J.map σ))) →
      ∃ K : Subgroup (GAd σ (c₀ • W.J.map σ)), K ≤ infPts σ (c₀ • W.J.map σ) ∧ IsCompact (K : Set (GAd σ (c₀ • W.J.map σ))) ∧
        ∀ y ∈ K₁, GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc₀ M y ∈ K := by
  intro F E _ _ _ _ _ σ _ hσ n n₁ W W₁ H hsk hn hxx hyy hxy hperp hgram c₀ hc₀ hW₁ _ M hMc hM K₁ hK₁ hK₁c
  have h : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, hperp, hgram⟩
  have hd : W₁.J.det ≠ 0 := fun h0 => hW₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨M', hM'c, hM', -⟩ := h.exists_leviHom hσ hsk hd
  have hMM : ∀ a, M a = M' a := fun a => h.levi_unique hσ hsk hd (hM a) (hM' a)
  let ψ : GAd σ (c₀ • W₁.J.map σ) →* GAd σ (c₀ • W.J.map σ) :=
    (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀).toMonoidHom.comp
      (M'.comp (GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm.toMonoidHom)
  have hψ : ∀ y, ψ y = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M' ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc₀).symm y)) :=
    fun _ => rfl
  have hψc : Continuous ψ :=
    (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W.J hc₀).1.comp
      (hM'c.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W₁.J hc₀).2)
  refine ⟨K₁.map ψ, ?_, ?_, fun y hy => ⟨y, hy, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_infPts_iff_map, hψ]
    exact levi_map_eq_one hσ h hsk hd _ (hM' _) ((mem_infPts_iff_map σ _ y).1 (hK₁ hy))
  · rw [Subgroup.coe_map]
    exact hK₁c.image hψc
  · rw [hψ, ← hMM]; rfl

end GlobalTheory.ThK.InducedCons

end
