import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.ThK.DescB.GenLevel
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private abbrev phiInf : AE F E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

private theorem mat_fin (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) (b : UA σ J)
    (hb : toGAd hσ J hc b ∈ finPts σ (c • J.map σ)) : (mat b).map (phiInf (F := F) (E := E)) = 1 := by
  first
  | exact congrArg Units.val hb
  | exact congrArg (fun u => u.1.1) hb
  | exact congrArg (fun u => u.1) hb

private theorem fin_of_mat (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) (b : UA σ J)
    (hb : (mat b).map (phiInf (F := F) (E := E)) = 1) : toGAd hσ J hc b ∈ finPts σ (c • J.map σ) :=
  Units.ext hb

private theorem levi_fin (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hd : W₁.J.det ≠ 0)
    {b : UA σ W₁.J} {m : UA σ W.J} (hm : IsLevi (W₁ := W₁) H 1 b m)
    (hb : (mat b).map (phiInf (F := F) (E := E)) = 1) : (mat m).map (phiInf (F := F) (E := E)) = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  obtain ⟨α, β, z, e⟩ := h.decompA hσ hsk hd (Pi.single j 1)
  obtain ⟨h1, h2, h3⟩ := hm
  simp only [Units.val_one, one_smul, inv_one, map_one] at h1 h2
  have hv : mat m *ᵥ (Pi.single j 1 : Fin n → AE F E) =
      Pi.single j 1 + incM F H.ι *ᵥ ((mat b - 1) *ᵥ z) := by
    rw [e]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h1, h2, h3, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub]
    abel
  have hs : (Pi.single j (1 : Ainf F ⊗[F] E) : Fin n → Ainf F ⊗[F] E) =
      (phiInf (F := F) (E := E)) ∘ (Pi.single j (1 : AE F E)) := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  have hz : (phiInf (F := F) (E := E)) ∘ ((mat b - 1) *ᵥ z) = 0 := by
    funext i
    rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_sub _ (map_sub _), hb,
      Matrix.map_one _ (map_zero _) (map_one _), sub_self, Matrix.zero_mulVec]
  rw [Matrix.one_mulVec, hs]
  funext i
  rw [← RingHom.map_mulVec, hv, Pi.add_apply, map_add, RingHom.map_mulVec, hz, Matrix.mulVec_zero, Pi.zero_apply,
    add_zero]
  rfl

private theorem det_ne_zero_of_cartan' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : E →+* ℂ) {θ : Matrix (Fin n) (Fin n) ℂ}
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  have h0 : (J.map e).det = 0 := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, map_zero]
  obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hx : star z ≠ 0 := fun h' => hz0 (by simpa using congrArg star h')
  have := h.2.2 (star z) hx
  rw [star_star, Matrix.smul_mulVec, hz, smul_zero, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

private theorem one_mem_KInf {n : ℕ} (Y : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    (1 : UA σ Y.J) ∈ KInf σ Y τ := by
  have h1 : mat (1 : UA σ Y.J) = 1 := rfl
  refine ⟨?_, fun w => ?_⟩
  · show At (evI F) (mat (1 : UA σ Y.J) - 1)
    rw [h1, sub_self]
    unfold At
    simp
  · rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

private theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∃ U : Subgroup (GAd σ (c • Y₁.J.map σ)), IsOpen (U : Set (GAd σ (c • Y₁.J.map σ))) ∧ ∀ k ∈ U, k ∈ finPts σ (c • Y₁.J.map σ) → ∀ x, (fun x => g ((toGAd hσ Y₁.J hc).symm x)) (x * k) = (fun x => g ((toGAd hσ Y₁.J hc).symm x)) x := by
  intro F E _ _ _ _ _ σ hσ B _ n n₁ Y Y₁ P hsk hP c hc _ fa hfa h _ _ g hg
  have hd : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact det_ne_zero_of_cartan' _ (hP.2.2.2.2.2.2.2.cartan w)
  have hH := GlobalTheory.ThK.GLTwo.IsIsoPlane.isHypPlane hP
  obtain ⟨M, hMc, hM, -⟩ := hH.exists_leviHom hσ hsk hd
  have hA := hfa ⊥ fun x hx => by
    rw [Subgroup.mem_bot.1 hx, map_one]; exact one_mem_KInf Y B.emb
  obtain ⟨U₀, hU₀, hl⟩ := hA.level
  let e := toGAd hσ Y.J hc
  let e₁ := toGAd hσ Y₁.J hc
  have he := GlobalTheory.ThK.GLTwo.continuous_toGAd hσ Y.J hc
  have he₁ := GlobalTheory.ThK.GLTwo.continuous_toGAd hσ Y₁.J hc
  let ψ : GAd σ (c • Y₁.J.map σ) →* GAd σ (c • Y.J.map σ) :=
    (MulAut.conj (e h)⁻¹).toMonoidHom.comp (e.toMonoidHom.comp (M.comp e₁.symm.toMonoidHom))
  have hψ : ∀ k, ψ k = (e h)⁻¹ * e (M (e₁.symm k)) * (e h)⁻¹⁻¹ := fun _ => rfl
  have hψc : Continuous ψ :=
    ((continuous_const.mul (he.1.comp (hMc.comp he₁.2))).mul continuous_const).congr fun k => (hψ k).symm
  refine ⟨U₀.comap ψ, hU₀.preimage hψc, fun k hk hkf x => ?_⟩
  have hfin : ψ k ∈ finPts σ (c • Y.J.map σ) := by
    have hb : (mat (e₁.symm k)).map (phiInf (F := F) (E := E)) = 1 :=
      mat_fin hσ Y₁.J hc _ (by simpa [e₁] using hkf)
    have h0 : e (M (e₁.symm k)) ∈ finPts σ (c • Y.J.map σ) :=
      fin_of_mat hσ Y.J hc _ (levi_fin hσ hH hsk hd (hM _) hb)
    rw [mem_finPts] at h0 ⊢
    rw [hψ, map_mul, map_mul, h0, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have key := hl (ψ k) hk hfin (e (M (e₁.symm x) * h))
  have e1 : e (M (e₁.symm x) * h) * ψ k = e (M (e₁.symm (x * k)) * h) := by
    rw [hψ, map_mul e₁.symm, map_mul M]
    simp only [map_mul, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [e1] at key
  simp only [e, MulEquiv.symm_apply_apply] at key
  show g (e₁.symm (x * k)) = g (e₁.symm x)
  rw [hg _ _ (hM _), hg _ _ (hM _)]
  exact key

end GlobalTheory.ThK.DescB.GenLevel

end

theorem _root_.GlobalTheory.T.isotropic_plane_constant_term_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (P : Plane E n n₁), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      IsIsoPlane σ B P Y Y₁ →
      ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∀ fa : UA σ Y.J → ℂ, (∀ K : Subgroup (GAd σ (c • Y.J.map σ)), (∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb) →
        IsAutOn σ (c • Y.J.map σ) ((unip σ Y P).map (toGAd hσ Y.J hc).toMonoidHom) K (fun x => fa ((toGAd hσ Y.J hc).symm x))) →
      ∀ h ∈ finK σ Y B.emb, (∀ h₁ : UA σ Y₁.J, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) P 1 h₁ m) →
      ∀ g : UA σ Y₁.J → ℂ, (∀ h₁ m, IsLevi (W₁ := Y₁) P 1 h₁ m → g h₁ = fa (m * h)) →
      ∃ U : Subgroup (GAd σ (c • Y₁.J.map σ)), IsOpen (U : Set (GAd σ (c • Y₁.J.map σ))) ∧ ∀ k ∈ U, k ∈ finPts σ (c • Y₁.J.map σ) → ∀ x, (fun x => g ((toGAd hσ Y₁.J hc).symm x)) (x * k) = (fun x => g ((toGAd hσ Y₁.J hc).symm x)) x :=
  GlobalTheory.ThK.DescB.GenLevel.main
