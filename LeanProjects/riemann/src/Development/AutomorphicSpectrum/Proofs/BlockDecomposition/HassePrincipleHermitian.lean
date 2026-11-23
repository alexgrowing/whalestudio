import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseHasse

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem invol (hCM : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2]; simp)

theorem exists_pure (hCM : IsCMExt F E σ) : ∃ e : E, e ≠ 0 ∧ σ e = -e := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ x : E, σ x = x := fun x => by
    by_contra hx
    refine hcon (x - σ x) (sub_ne_zero.2 (Ne.symm hx)) ?_
    rw [map_sub, invol hCM]
    ring
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    ext x
    have h := hCM.2.2.2 τ x
    rw [hfix] at h
    simpa using h.symm
  haveI : IsTotallyComplex E := hCM.2.1
  have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hreal)

theorem coord_E (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (z : E) :
    ∃ c d : F, z = algebraMap F E c + algebraMap F E d * e := by
  obtain ⟨c, hc⟩ := GoodMass.fixed_mem hCM ((z + σ z) / 2) (by
    rw [map_div₀, map_add, invol hCM, map_ofNat]
    ring)
  obtain ⟨d, hd⟩ := GoodMass.fixed_mem hCM ((z - σ z) / (2 * e)) (by
    rw [map_div₀, map_sub, invol hCM, map_mul, map_ofNat, hσ]
    field_simp
    ring)
  refine ⟨c, d, ?_⟩
  rw [hc, hd]
  field_simp
  ring

variable (R : Type) [CommRing R] [Algebra F R]

theorem coord_R (hCM : IsCMExt F E σ) {e : E} (he : e ≠ 0) (hσ : σ e = -e) (y : R ⊗[F] E) :
    ∃ a b : R, y = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] e := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r z =>
    obtain ⟨c, d, rfl⟩ := coord_E hCM he hσ z
    refine ⟨algebraMap F R c * r, algebraMap F R d * r, ?_⟩
    have key : ∀ (c : F) (w : E), r ⊗ₜ[F] (algebraMap F E c * w) = (algebraMap F R c * r) ⊗ₜ[F] w := by
      intro c w
      rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_add, ← key, ← key, mul_one]
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩

theorem tmul_one_injective {r s : R} (h : r ⊗ₜ[F] (1 : E) = s ⊗ₜ[F] (1 : E)) : r = s :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (R := F) (A := R) (B := E)
    (FaithfulSMul.algebraMap_injective F E) h

theorem local_form (hCM : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} {j : F} (hj : J 0 0 = algebraMap F E j)
    (hj0 : j ≠ 0) {e : E} (he : e ≠ 0) (hσ : σ e = -e) {δ : F} (hδ : e * e = algebraMap F E δ) (β : F)
    (Y : Fin 1 → Fin 1 → R ⊗[F] E) (hY : gramR R σ J Y = (hermScal R σ (algebraMap F R β)).1) :
    ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
  obtain ⟨a, b, hab⟩ := coord_R R hCM he hσ (Y 0 0)
  refine ⟨a, b, ?_⟩
  have h00 : hR R σ J (Y 0) (Y 0) = algebraMap F R β ⊗ₜ[F] (1 : E) := congrFun (congrFun hY 0) 0
  have hsig : sigR R σ (Y 0 0) = a ⊗ₜ[F] (1 : E) - b ⊗ₜ[F] e := by
    rw [hab, map_add]
    simp [sigR, hσ, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hJ : inclR R (J 0 0) = algebraMap F R j ⊗ₜ[F] (1 : E) := by
    rw [hj]
    simp [inclR, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hee : (b ⊗ₜ[F] e) * (b ⊗ₜ[F] e) = (algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_mul_assoc, one_mul, sq]
  have hn : sigR R σ (Y 0 0) * Y 0 0 = (a ^ 2 - algebraMap F R δ * b ^ 2) ⊗ₜ[F] (1 : E) := by
    rw [hsig, hab, TensorProduct.sub_tmul, ← hee, sq, ← mul_one (1 : E), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    ring
  have h1 : (algebraMap F R j * (a ^ 2 - algebraMap F R δ * b ^ 2)) ⊗ₜ[F] (1 : E) = algebraMap F R β ⊗ₜ[F] (1 : E) := by
    rw [← h00]
    simp only [hR, hform, JR, Fin.sum_univ_one, Matrix.map_apply, hJ]
    rw [mul_comm (sigR R σ (Y 0 0)), mul_assoc, hn, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h2 := tmul_one_injective (F := F) (E := E) R h1
  have hu : algebraMap F R j * algebraMap F R j⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hj0, map_one]
  rw [div_eq_mul_inv, map_mul, ← h2]
  linear_combination (a ^ 2 - algebraMap F R δ * b ^ 2) * hu

end

section

variable {F : Type} [Field F] [NumberField F]

theorem exists_real_hom (τ : F →+* ℝ) : ∃ ψ : Ainf F →+* ℝ, ∀ x, ψ (algebraMap F (Ainf F) x) = τ x := by
  let φ : F →+* ℂ := Complex.ofRealHom.comp τ
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    simp [φ, ComplexEmbedding.conjugate]
  let v : InfinitePlace F := InfinitePlace.mk φ
  have hv : v.IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨(InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v), fun x => ?_⟩
  have h1 : (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
      (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) (algebraMap F (Ainf F) x) =
        InfinitePlace.embedding_of_isReal hv x :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv ((WithAbs.equiv v.1).symm x)
  refine h1.trans ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  rfl

end

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ hmi hm β hβ hinf hfin
  obtain ⟨j, hj⟩ := GoodMass.fixed_mem hCM _ (hJ.1 0 0)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hJ.2 (by rw [Matrix.det_fin_one, ← hj, map_zero])
  obtain ⟨e, he, hσ⟩ := exists_pure hCM
  obtain ⟨δ, hδ⟩ := GoodMass.fixed_mem hCM (e * e) (by rw [map_mul, hσ]; ring)
  have hδ' : e * e = algebraMap F E δ := hδ.symm
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact mul_ne_zero he he (by rw [hδ', map_zero])
  have hfib : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
      (μ' : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
      (m' : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)), IsGramFib R σ J 1 μ' ν m' →
      m' (hermScal R σ (algebraMap F R β)) ≠ 0 →
      ∃ a b : R, algebraMap F R (β / j) = a ^ 2 - algebraMap F R δ * b ^ 2 := by
    intro R _ _ _ μ' ν m' hG hne
    by_contra hcon
    have hempty : (gramR R σ J ⁻¹' {(hermScal R σ (algebraMap F R β)).1} ∩
        {X | IsUnit (gramR R σ J X).det}) = ∅ := by
      ext Y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro hY _
      exact hcon (local_form R hCM hj.symm hj0 he hσ hδ' β Y hY)
    apply hne
    have h1 := hG.1 (hermScal R σ (algebraMap F R β))
    rw [hempty, Set.compl_empty] at h1
    exact Measure.measure_univ_eq_zero.1 h1
  obtain ⟨a, c, hac⟩ := GlobalTheory.QNorm.hasseNormSt F δ (β / j) hδ0 (div_ne_zero hβ hj0)
    (fun τ => by
      obtain ⟨ψ, hψ⟩ := exists_real_hom τ
      obtain ⟨a, c, h⟩ := hfib (Ainf F) _ _ mi hmi hinf
      refine ⟨ψ a, ψ c, ?_⟩
      have := congrArg ψ h
      simpa [hψ] using this)
    (fun v => hfib (Fv F v) _ _ (m v) (hm v) (hfin v))
  refine ⟨fun _ _ => algebraMap F E a + algebraMap F E c * e, ?_⟩
  funext p q
  have hp : p = 0 := Subsingleton.elim _ _
  have hq : q = 0 := Subsingleton.elim _ _
  subst hp hq
  have hb : β = j * (a ^ 2 - δ * c ^ 2) := by
    rw [← hac]
    field_simp
  simp only [gramE, hE, hform, Fin.sum_univ_one, ← hj, RingHom.coe_coe, map_add, map_mul, hσ, AlgHom.commutes]
  rw [hb, map_mul, map_sub, map_mul, map_pow, map_pow, ← hδ']
  ring

end GlobalTheory.CompanionTheory.SW.BaseHasse
