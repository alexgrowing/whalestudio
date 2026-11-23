import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementUnitaryMatrixIdentity
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.IwaSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

private theorem isHermND_skew {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {W : Spc F E n} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {c : E} (hc : c ≠ 0) (hσc : σ c = -c) : IsHermND σ (c • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [hσc, hW.skew i j, map_neg, hW.skew j i]
    ring
  · rw [Matrix.det_smul]
    have hmap : (W.J.map σ).det = σ W.J.det := ((σ : E →+* E).map_det W.J).symm
    rw [hmap]
    refine mul_ne_zero (pow_ne_zero _ hc) ?_
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hM := det_ne_zero_of_hasSig (hW.sig w)
    have hJ : W.J.det = 0 := σ.toRingHom.injective (by simpa using h0)
    apply hM
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]

private theorem exists_imag {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ c : E, c ≠ 0 ∧ σ c = -c := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : ∀ x, τ (σ x) = star (τ x) := h.2.2.2 τ
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push Not at hall
    have hTC := h.2.1
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hconj x
    rw [hall x] at this
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, GlobalTheory.SiegelSet.sigma_sigma h, neg_sub]

omit [NumberField F] [NumberField E] in
private theorem hE_eq {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E)
    (u v : Fin n → E) : hE σ (c • J.map σ) u v = c * σ (form σ J u v) := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, RingHom.coe_coe, hσ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
private theorem gram_eq {σ : E →ₐ[F] E} {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (U V : Matrix (Fin n) (Fin q) E) (i j : Fin q) :
    (Formalism.UG.cT (σ : E →+* E) U * J * V) i j = hE σ J (fun k => U k i) (fun k => V k j) := by
  simp only [hE, Formalism.UG.hform, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

open GlobalTheory.TorusTranslate in

private theorem torus_eig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Xf Yf : Matrix (Fin n) (Fin q) E) (t : Fin q → ℝ) (a : GAd σ J) (ha : GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a)
    (i : Fin q) (hi : t i ≠ 0) :
    ∃ u : (AE F E)ˣ, (HA.mat (AF F) σ J a).1 *ᵥ incV F (fun k => Xf k i) = u.1 • incV F (fun k => Xf k i) := by
  have hf : ∀ s : ℝ, finPart F E (1 + realAd F (s - 1) • (1 : AE F E)) = 1 := fun s => by
    rw [map_add, finPart_realAd_smul, map_one, add_zero]
  have hi' : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : ℝ),
      infEmb τ (compInf F E w (1 + realAd F (s - 1) • (1 : AE F E))) = s := fun w τ s => by
    rw [map_add, map_add, infEmb_realAd_smul h]
    simp
  have hu : (1 + realAd F (t i - 1) • (1 : AE F E)) * (1 + realAd F ((t i)⁻¹ - 1) • (1 : AE F E)) = 1 := by
    refine ae_ext h ?_ fun w τ => ?_
    · rw [map_mul, hf, hf, map_one, mul_one]
    · rw [map_mul, map_mul, hi', hi', map_one, map_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hi, Complex.ofReal_one]
  refine ⟨Units.mkOfMulEqOne _ _ hu, funext fun k => ae_ext h ?_ fun w τ => ?_⟩
  · rw [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Units.val_mkOfMulEqOne, hf, one_mul]
    have h0 : (HA.mat (AF F) σ J a).1.map (finPart F E) = 1 := Matrix.ext fun i j => by
      have := congrArg (fun g : GL (Fin n) (Af F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
        (MonoidHom.mem_ker.1 ha.1)
      exact this
    rw [h0, Matrix.one_mulVec]
    rfl
  · have h0 : ∀ (x : E), infEmb τ (compInf F E w (inclR (F := F) (AF F) x)) = τ.1 x := fun x => by
      change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
      simp
    have e : ((infEmb τ).comp (compInf F E w)) (((HA.mat (AF F) σ J a).1 *ᵥ incV F (fun k => Xf k i)) k) = _ :=
      RingHom.map_mulVec _ _ _ _
    refine e.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, Units.val_mkOfMulEqOne, hi']
    have hc := congrFun (mulVec_col (ha.2 w τ).1 i) k
    have e2 : ((infEmb τ).comp (compInf F E w)) ∘ incV F (fun k => Xf k i) = fun k => Xf.map τ.1 k i :=
      funext fun k => h0 _
    rw [e2]
    refine hc.trans ?_
    simp only [incV, h0, Matrix.map_apply]
    ring

private theorem par_eig {σ : E →ₐ[F] E} {n q : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Xf : Matrix (Fin n) (Fin (q + 1)) E) (p : GAd σ J) (hp : p ∈ GlobalTheory.SiegelSet.minParOne σ J Xf) :
    ∃ u : (AE F E)ˣ, (HA.mat (AF F) σ J p).1 *ᵥ incV F (fun k => Xf k 0) = u.1 • incV F (fun k => Xf k 0) := by
  obtain ⟨Bm, hB, hp, hu⟩ := hp
  obtain ⟨u, hu, -⟩ := hu 0
  refine ⟨u, funext fun k => ?_⟩
  have e := congrFun (congrFun hp k) 0
  have hz : ∑ j : Fin q, GlobalTheory.SiegelSet.adMat F Xf k j.succ * Bm j.succ 0 = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [hB (show id 0 < id (Fin.succ j) from Fin.succ_pos j), mul_zero])
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, hz, add_zero, hu] at e
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  exact e

end UpperTheory.IwaSkew

end

open UpperTheory.IwaSkew in
theorem UpperTheory.skew_witt_compact_decomposition :
    GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
                 ∀ x : Fin n → E, x ≠ 0 → form σ W.J x x = 0 → ∀ γ, IsWitt (σ := σ) (J := W.J) x γ →
                 ∃ C : Set (UA σ W.J), IsCompact C ∧ ∀ g : UA σ W.J, ∃ (p κ : UA σ W.J) (t : (AE F E)ˣ),
                   κ ∈ C ∧ mat p *ᵥ incV F x = t.1 • incV F x ∧ g = p * κ := by
  intro hP F E _ _ _ _ _ σ B n W r s hB hWs x hx0 hxx γ hγ
  have hcm := hB.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := exists_imag hcm
  have hJ' : IsHermND σ (c • W.J.map σ) := isHermND_skew hWs hc hcs
  let e : UA σ W.J ≃* GAd σ (c • W.J.map σ) :=
    MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := W.J) hσ hc)
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨q, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame hcm hJ'
  obtain ⟨K, Ω, c', hK, -, -, -, hIw, -⟩ := hP F E σ hcm n _ hJ' q Xf Yf hW
  obtain _ | q := q
  · exact absurd (hW.aniso x (funext fun i => i.elim0) (funext fun i => i.elim0)
      (by rw [hE_eq hσ, hxx, map_zero, mul_zero])) hx0
  have h1 : (fun k => Xf k 0) ≠ 0 := fun h0 => by
    have := congrFun (congrFun hW.xy 0) 0
    rw [gram_eq, h0] at this
    simp [hE, Formalism.UG.hform] at this
  have h2 : form σ W.J (fun k => Xf k 0) (fun k => Xf k 0) = 0 := by
    have := congrFun (congrFun hW.xx 0) 0
    rw [gram_eq, hE_eq hσ, Matrix.zero_apply] at this
    exact (map_eq_zero σ).1 ((mul_eq_zero.1 this).resolve_left hc)
  obtain ⟨δ, hδ⟩ : ∃ δ : UA σ W.J, mat δ *ᵥ incV F (fun k => Xf k 0) = incV F x := ⟨γ ⟨_, h1, h2⟩, (hγ ⟨_, h1, h2⟩).2⟩
  have hδ' : mat δ⁻¹ *ᵥ incV F x = incV F (fun k => Xf k 0) := by
    have h3 : mat δ⁻¹ * mat δ = 1 := by simp [mat]
    rw [← hδ, Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  have hcont : Continuous fun k : GAd σ (c • W.J.map σ) => e.symm (e δ * k) :=
    he'.comp (continuous_const.mul continuous_id)
  refine ⟨_, hK.image hcont, fun g => ?_⟩
  obtain ⟨p, hp, t, a, ht, ha, k, hk, hg⟩ := hIw (e (δ⁻¹ * g))
  obtain ⟨u, hu⟩ := par_eig _ Xf p hp
  obtain ⟨v, hv⟩ := torus_eig hcm _ Xf Yf t a ha 0 (ht 0).ne'
  refine ⟨δ * e.symm p * e.symm a * δ⁻¹, e.symm (e δ * k), v * u, ⟨k, hk, rfl⟩, ?_, ?_⟩
  · have h3 : mat (δ * e.symm p * e.symm a * δ⁻¹) =
        mat δ * (HA.mat (AF F) σ _ p).1 * (HA.mat (AF F) σ _ a).1 * mat δ⁻¹ := rfl
    rw [h3, ← Matrix.mulVec_mulVec, hδ', ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hu,
      Matrix.mulVec_smul, hδ, smul_smul, Units.val_mul]
  · apply e.injective
    rw [map_mul, map_inv] at hg
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    calc e g = e δ * ((e δ)⁻¹ * e g) := by group
      _ = _ := by rw [hg]; group
