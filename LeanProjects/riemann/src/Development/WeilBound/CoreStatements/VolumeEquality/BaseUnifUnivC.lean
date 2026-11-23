import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformSymplecticImaginaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitianStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDefStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImageStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateEmbeddingsCriterionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesActionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspaceStatement
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivA
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLatticeStatement

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

section Tz

variable {I : Type} [Fintype I]

theorem tz_add (Z : Matrix I I ℂ) (z w : I → ℂ) : tz Z (z + w) = tz Z z + tz Z w := by
  simp only [tz, star_add, mulVec_add]
  abel

theorem tz_I (Z : Matrix I I ℂ) (z : I → ℂ) :
    tz Z (Complex.I • z) = Complex.I • (z + Z *ᵥ star z) := by
  have h : star (Complex.I • z) = (-Complex.I) • star z := by
    funext i
    simp
  rw [tz, h, mulVec_smul, smul_add]
  funext i
  simp

def tzR (Z : Matrix I I ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun := tz Z
  map_add' := tz_add Z
  map_smul' r z := by
    have h : star (r • z) = r • star z := by
      funext i
      simp
    simp only [tz, h, RingHom.id_apply, smul_sub]
    rw [mulVec_smul]

theorem tz_support [DecidableEq I] (Z : Matrix I I ℂ) (d : I → ℂ) (M : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (h : ∀ z, tz Z (d * z) = M (tz Z z)) (i k : I) : d i * Z i k = Z i k * star (d k) := by
  have h2 : ∀ z : I → ℂ, d * z + Z *ᵥ star (d * z) = M z + M (Z *ᵥ star z) := by
    intro z
    have e : d * (Complex.I • z) = Complex.I • (d * z) := by
      funext i
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := h (Complex.I • z)
    rw [e, tz_I, tz_I, map_smul, map_add] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h1 : ∀ z : I → ℂ, d * z - Z *ᵥ star (d * z) = M z - M (Z *ᵥ star z) := by
    intro z
    have := h z
    rwa [tz, tz, map_sub] at this
  have h3 : ∀ z : I → ℂ, d * z = M z := by
    intro z
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star (d * z) = d * (Z *ᵥ star z) := by
    intro z
    rw [h3 (Z *ᵥ star z)]
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a2 - a1) / 2
  have := congrFun (h4 (Pi.single k 1)) i
  have s1 : star (d * (Pi.single k 1 : I → ℂ)) = Pi.single k (star (d k)) := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s1, s2] at this
  simp only [Pi.mul_apply, mulVec_single, MulOpposite.op_mul] at this
  simpa [mul_comm] using this.symm

theorem tz_unique [DecidableEq I] (S : Set (I → ℂ)) (hS : Submodule.span ℝ S = ⊤) (A A' : (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (Z Z' : Matrix I I ℂ) (h : ∀ z ∈ S, A (tz Z z) = A' (tz Z' z)) : Z = Z' := by
  have hall : ∀ z, A (tz Z z) = A' (tz Z' z) := by
    have hf : (A.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z = (A'.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z' :=
      LinearMap.ext_on hS fun z hz => h z hz
    exact fun z => LinearMap.congr_fun hf z
  have h2 : ∀ z : I → ℂ, A (z + Z *ᵥ star z) = A' (z + Z' *ᵥ star z) := by
    intro z
    have := hall (Complex.I • z)
    rw [tz_I, tz_I, map_smul, map_smul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : ∀ z : I → ℂ, A z = A' z := by
    intro z
    funext a
    have a1 := congrFun (hall z) a
    have a2 := congrFun (h2 z) a
    simp only [tz, map_sub, map_add, Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star z = Z' *ᵥ star z := by
    intro z
    apply A.injective
    have := h2 z
    rw [map_add, map_add, h3 z] at this
    rw [h3 (Z' *ᵥ star z)]
    exact add_left_cancel this
  ext i k
  have := congrFun (h4 (Pi.single k 1)) i
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s2] at this
  simpa using this

end Tz

section Big

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ}

theorem bigZe_symm (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (bigZe e q t)ᵀ = bigZe e q t := by
  unfold bigZe bigZ
  rw [transpose_submatrix, blockDiagonal_transpose]
  congr 2
  funext τ
  rw [fromBlocks_transpose]
  simp

theorem bigZ_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) (a : Fin j) (b : Fin j') :
    bigZ q t (Sum.inr a, τ) (Sum.inl b, τ) = t (q (τ, a, b)) := by
  simp [bigZ, blockDiagonal_apply_eq, ballMat]

theorem bigZe_injective (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    Function.Injective (bigZe e q) := by
  intro t t' h
  funext k
  obtain ⟨⟨τ, a, b⟩, rfl⟩ := q.surjective k
  have := congrFun (congrFun h (e (Sum.inr a, τ))) (e (Sum.inl b, τ))
  simpa [bigZe, bigZ_entry] using this

theorem bigZ_hol (q : Ψ × Fin j × Fin j' ≃ Fin n) (i k : Ix Ψ j j') :
    Differentiable ℂ (fun t => bigZ q t i k) := by
  obtain ⟨a, τ⟩ := i
  obtain ⟨b, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bigZ, blockDiagonal_apply_eq, ballMat, differentiable_apply]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem bigZe_hol (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (z : Fin g → ℂ) :
    Differentiable ℂ (fun t => tz (bigZe e q t) z) := by
  refine differentiable_pi.2 fun i => ?_
  simp only [tz, Pi.sub_apply, mulVec, dotProduct, bigZe, submatrix_apply]
  refine (differentiable_const _).sub (Differentiable.fun_sum fun k _ => ?_)
  exact (bigZ_hol q _ _).mul_const _

end Big

theorem member {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R₁ : RiemLat E g Λ) (Z : Matrix (Fin g) (Fin g) ℂ) (hH : R₁.Hm = 1) (hs : Zᵀ = Z) (hp : (1 - Zᴴ * Z).PosDef)
    (hc : ∀ a x, tz Z (R₁.B a x) = R₁.B a (tz Z x)) :
    ∃ R : RiemLat E g Λ, R.form = R₁.form ∧ R.B = R₁.B ∧ R.Hm = (1 - Zᴴ * Z)⁻¹ ∧ ∀ x, R.P x = tz Z (R₁.P x) := by
  have hinv : ((1 - Zᴴ * Z)⁻¹).PosDef := hp.inv
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x => tz Z (R₁.P x)
      map_zero' := by simp [tz]
      map_add' := fun x y => by rw [map_add, tz_add] }
  refine ⟨{ free := R₁.free, fin := R₁.fin, rank := R₁.rank, form := R₁.form, alt := R₁.alt, unimod := R₁.unimod,
            adj := R₁.adj, P := P, Hm := (1 - Zᴴ * Z)⁻¹, herm := hinv.isHermitian, pos := ?_, im := ?_, B := R₁.B,
            act := ?_ }, rfl, rfl, rfl, fun _ => rfl⟩
  · intro z hz
    have h := (Matrix.posDef_iff_dotProduct_mulVec.1 hinv).2 (x := star z) (by simpa using hz)
    rw [star_star, Complex.lt_def] at h
    exact h.1
  · intro x y
    show (tz Z (R₁.P x) ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z (R₁.P y))).im = _
    rw [GlobalTheory.T.siegel_transform_symplectic_imaginary Z hs hp, ← R₁.im, hH, one_mulVec]
  · intro a x
    show tz Z (R₁.P (a • x)) = R₁.B a (tz Z (R₁.P x))
    rw [R₁.act, hc]

theorem exists_univFam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ R₀ σ q hσ hsig
  classical
  obtain ⟨e, c, hc, hco⟩ := Frame.exists_ortho_frame R₀ σ hσ hsig
  obtain ⟨R₁, hform, hHm, hB⟩ := GlobalTheory.T.exists_normalized_riemann_lattice R₀ σ e c hc hco
  have hmem : ∀ t, ∃ R : RiemLat E g Λ, R.form = R₀.form ∧ (t ∈ ballDom q → R.B = R₁.B ∧
      R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ ∧ ∀ x, R.P x = tz (bigZe e q t) (R₁.P x)) := by
    intro t
    by_cases ht : t ∈ ballDom q
    · obtain ⟨R, h1, h2, h3, h4⟩ := member R₁ (bigZe e q t) hHm (bigZe_symm e q t)
        ((GlobalTheory.T.ball_domain_iff_pos_def e q t).1 ht) (GlobalTheory.T.siegel_transform_commutes_action σ e q t R₁.B hσ hB)
      exact ⟨R, h1.trans hform, fun _ => ⟨h2, h3, h4⟩⟩
    · exact ⟨R₁, hform, fun h => absurd h ht⟩
  choose R hRf hR using hmem
  have hfr := GlobalTheory.T.span_standard_basis_eigenspace σ e R₁.B hσ hB
  have hli : ∀ {m : ℕ} (f : Fin m → Ix Ψ j j'), Function.Injective f →
      LinearIndependent ℂ (fun i : Fin m => (Pi.single (e (f i)) 1 : Fin g → ℂ)) := by
    intro m f hf
    have := (Pi.basisFun ℂ (Fin g)).linearIndependent.comp (fun i => e (f i))
      (e.injective.comp hf)
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  have hl : ∀ τ, LinearIndependent ℂ (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inl i, τ)) (fun a b h => by simpa using h)
  have hr : ∀ τ, LinearIndependent ℂ (fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inr i, τ)) (fun a b h => by simpa using h)
  refine ⟨{ q := q, σ := σ, cm := hσ, form := R₀.form, R := R, form_eq := hRf,
            hol := ?_, sig := ?_, b := fun τ i _ => Pi.single (e (Sum.inl i, τ)) 1,
            frames := ?_, logDet_eq := ?_, univ := ?_ }, rfl, rfl, rfl⟩
  · refine ⟨fun t _ t' _ => (hRf t).trans (hRf t').symm, fun x => ?_⟩
    exact ((bigZe_hol e q (R₁.P x)).differentiableOn).congr fun t ht => (hR t ht).2.2 x
  · intro t ht τ
    rw [(hR t ht).1, ← (hfr τ).1, ← (hfr τ).2]
    exact ⟨by rw [finrank_span_eq_card (hl τ)]; simp, by rw [finrank_span_eq_card (hr τ)]; simp⟩
  · refine ⟨fun τ i => differentiableOn_const _, fun t ht τ => ⟨hl τ, ?_⟩⟩
    show _ = eigSp (R t).B (σ τ)
    rw [(hR t ht).1]
    exact (hfr τ).1
  · intro t ht
    exact GlobalTheory.T.log_det_eq_ball_potential e q t (R t) ht (hR t ht).2.1
  · intro R' hR' _
    obtain ⟨L, hL1, hL2, hL3⟩ := exists_realExt R₁ R' (hR'.trans hform.symm)
    obtain ⟨A, Z, hZs, hZp, hLZ⟩ := GlobalTheory.T.siegel_normal_form_of_hermitian L R'.Hm R'.herm R'.pos (by
      intro z w
      rw [hL2, hHm, one_mulVec])
    have hsupp : ∀ (a : 𝓞 E) i k, emb σ (e.symm i) a * Z i k = Z i k * star (emb σ (e.symm k) a) := by
      intro a
      refine tz_support Z (fun k => emb σ (e.symm k) a)
        (A.symm.toLinearMap ∘ₗ (R'.B a) ∘ₗ A.toLinearMap) fun z => ?_
      have hz : (fun k => emb σ (e.symm k) a) * z = R₁.B a z := by
        funext k
        simp [hB]
      apply A.injective
      rw [hz]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← hLZ, ← hLZ, hL3]
    have hZ0 : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft := by
      intro i k hik
      refine (GlobalTheory.T.conjugate_embeddings_criterion σ hσ (e.symm i) (e.symm k)).1 fun a => ?_
      have := hsupp a i k
      rw [mul_comm] at this
      exact mul_left_cancel₀ hik this
    obtain ⟨t, rfl⟩ := GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe e q Z hZs hZ0
    have ht : t ∈ ballDom q := (GlobalTheory.T.ball_domain_iff_pos_def e q t).2 hZp
    refine ⟨t, ⟨ht, A, fun x => ?_⟩, ?_⟩
    · rw [(hR t ht).2.2 x, ← hLZ, hL1]
      rfl
    · rintro t' ⟨ht', h', hh⟩
      have hspan := (SheetDecomposition.riemBasic E g Λ Ψ R₁).2.1
      refine bigZe_injective e q (tz_unique _ hspan h' A _ _ ?_)
      rintro _ ⟨x, rfl⟩
      rw [← (hR t' ht').2.2 x, ← hh x, ← hLZ, hL1]
      rfl

end SheetDecomposition.Univ

theorem SheetDecomposition.univExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form :=
  SheetDecomposition.Univ.exists_univFam
