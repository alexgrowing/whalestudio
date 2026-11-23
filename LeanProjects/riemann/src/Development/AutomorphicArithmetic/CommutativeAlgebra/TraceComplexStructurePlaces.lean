import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMul
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan
import Development.AutomorphicArithmetic.CommutativeAlgebra.TraceActionEqSumPlaces

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem jt_sum_emb {F : Type} [Field F] [NumberField F] [IsCMField F] (g : (F →+* ℂ) → ℂ) :
    ∑ σ : F →+* ℂ, g σ = ∑ w : InfinitePlace F,
      (g w.embedding + g (ComplexEmbedding.conjugate w.embedding)) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : F →+* ℂ => InfinitePlace.mk σ) g]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    have hc : w.IsComplex := IsTotallyComplex.isComplex w
    exact (InfinitePlace.isComplex_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h.symm)
  have hf : (Finset.univ.filter fun σ : F →+* ℂ => InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · right; rw [h]; simp
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne]

private theorem jt_indep {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [IsCMField F]
    (e : E ≃+* F) (a : (E →+* ℂ) → ℂ) (t : InfinitePlace F → ℂ)
    (h : ∀ c : 𝓞 E, ∑ σ : E →+* ℂ, a σ * σ (c : E) =
      ∑ w : InfinitePlace F, (t w * w.embedding (e c) +
        (starRingEnd ℂ) (t w) * (starRingEnd ℂ) (w.embedding (e c))))
    (w : InfinitePlace F) : a (w.embedding.comp (e : E →+* F)) = t w := by
  let r : (F →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => σ.comp (e : E →+* F)
      invFun := fun σ => σ.comp (e.symm : F →+* E)
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  let B : (F →+* ℂ) → ℂ := fun σ =>
    if σ = (InfinitePlace.mk σ).embedding then t (InfinitePlace.mk σ)
    else (starRingEnd ℂ) (t (InfinitePlace.mk σ))
  have hB1 : ∀ w : InfinitePlace F, B w.embedding = t w := by
    intro w; simp [B, InfinitePlace.mk_embedding]
  have hB2 : ∀ w : InfinitePlace F, B (ComplexEmbedding.conjugate w.embedding) = (starRingEnd ℂ) (t w) := by
    intro w
    have hne : ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
      intro h
      have hc : w.IsComplex := IsTotallyComplex.isComplex w
      exact (InfinitePlace.isComplex_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
    simp only [B, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    rw [if_neg hne]
  have key : ∀ c : 𝓞 E, ∑ σ : E →+* ℂ, (a σ - B (r.symm σ)) * σ (c : E) = 0 := by
    intro c
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [h c, sub_eq_zero, ← Equiv.sum_comp r (fun σ => B (r.symm σ) * σ (c : E))]
    have := jt_sum_emb (fun σ : F →+* ℂ => B σ * σ (e c))
    simp only [Equiv.symm_apply_apply]
    have hr : ∑ σ : F →+* ℂ, B σ * (r σ) (c : E) = ∑ σ : F →+* ℂ, B σ * σ (e c) :=
      Finset.sum_congr rfl fun _ _ => rfl
    rw [hr, this]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hB1, hB2, ComplexEmbedding.conjugate_coe_eq]
  have h0 := GlobalTheory.UPel.HT.LieType.DimSum.coeff_eq_zero_of_sum_embeddings _ key (r w.embedding)
  simp only [Equiv.symm_apply_apply, hB1] at h0
  exact sub_eq_zero.mp h0

private theorem jt_ne {p : ℕ} [Fact p.Prime] (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have h0 := D.ρc_root
  rw [hre] at h0
  have h1 : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by exact_mod_cast h0
  have h2 : ((D.tr ^ 2 - 4 * D.nm : ℤ) : ℝ) < 0 := by exact_mod_cast D.disc_neg
  push_cast at h2
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

private theorem jt_root {p : ℕ} [Fact p.Prime] (D : Datum p) (τ : D.F →+* ℂ) :
    τ (D.ω : D.F) = D.ρc ∨ τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
  have hω : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hz : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) hω
    simpa using this
  have hρ := D.ρc_root
  have hc : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) hρ
    simpa using this
  have hsum : (starRingEnd ℂ) D.ρc + D.ρc - (D.tr : ℂ) = 0 := by
    have : ((starRingEnd ℂ) D.ρc - D.ρc) * ((starRingEnd ℂ) D.ρc + D.ρc - (D.tr : ℂ)) = 0 := by
      linear_combination hc - hρ
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (jt_ne D))
  have : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    linear_combination hz - τ (D.ω : D.F) * hsum + D.ρc * hsum - hρ
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem jt_S {p : ℕ} [Fact p.Prime] (D : Datum p) (c : 𝓞 D.F) :
    (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F)) -
      (starRingEnd ℂ) (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc),
        (D.n : ℂ) * τ (c : D.F)) =
    ∑ τ : D.F →+* ℂ, (D.n : ℂ) * (if τ (D.ω : D.F) ≠ D.ρc then 1 else -1) * τ (c : D.F) := by
  have hc : (starRingEnd ℂ) (∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc),
        (D.n : ℂ) * τ (c : D.F)) =
      ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => ¬ τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) := by
    rw [map_sum]
    refine Finset.sum_nbij' (fun σ => (starRingEnd ℂ).comp σ) (fun σ => (starRingEnd ℂ).comp σ) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have hσ' : σ (D.ω : D.F) ≠ D.ρc := (Finset.mem_filter.mp hσ).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases jt_root D σ with h | h
      · exact absurd h hσ'
      · simp [h]
    · intro σ hσ
      have hσ' : ¬ σ (D.ω : D.F) ≠ D.ρc := (Finset.mem_filter.mp hσ).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have h : σ (D.ω : D.F) = D.ρc := not_not.mp hσ'
      simpa [h] using jt_ne D
    · intro σ _; ext x; simp
    · intro σ _; ext x; simp
    · intro σ _; simp
  rw [hc, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc)
    (fun τ => (D.n : ℂ) * (if τ (D.ω : D.F) ≠ D.ρc then 1 else -1) * τ (c : D.F)),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun τ h => ?_
    rw [if_pos (Finset.mem_filter.mp h).2]; ring
  · refine Finset.sum_congr rfl fun τ h => ?_
    rw [if_neg (Finset.mem_filter.mp h).2]; ring

private theorem jt_lhs {p : ℕ} [Fact p.Prime] (D : Datum p) (τ₁ : D.F →+* ℂ) (c : 𝓞 D.F) :
    ∑ σ : D.F →+* ℂ, (Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1))) * σ (c : D.F) =
      Complex.I * ((D.m : ℂ) * (τ₁ (c : D.F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (τ₁ (c : D.F)))) +
      (starRingEnd ℂ) (Complex.I * ((D.m : ℂ) * (τ₁ (c : D.F) +
        ∑ τ ∈ Finset.univ.filter (fun τ : D.F →+* ℂ => τ (D.ω : D.F) ≠ D.ρc), (D.n : ℂ) * τ (c : D.F) -
        (starRingEnd ℂ) (τ₁ (c : D.F))))) := by
  have hS := jt_S D c
  have e1 : ∑ σ : D.F →+* ℂ, (if σ = τ₁ then (2 : ℂ) else 0) * σ (c : D.F) = 2 * τ₁ (c : D.F) := by
    simp [ite_mul]
  have e2 : ∑ σ : D.F →+* ℂ, (if σ = (starRingEnd ℂ).comp τ₁ then (2 : ℂ) else 0) * σ (c : D.F) =
      2 * (starRingEnd ℂ) (τ₁ (c : D.F)) := by
    simp [ite_mul]
  have e0 : ∑ σ : D.F →+* ℂ, (Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1))) * σ (c : D.F) =
      Complex.I * (D.m : ℂ) * (∑ σ : D.F →+* ℂ, (if σ = τ₁ then (2 : ℂ) else 0) * σ (c : D.F) -
        ∑ σ : D.F →+* ℂ, (if σ = (starRingEnd ℂ).comp τ₁ then (2 : ℂ) else 0) * σ (c : D.F) +
        ∑ σ : D.F →+* ℂ, (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1) * σ (c : D.F)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e0, e1, e2, ← hS]
  simp only [map_mul, map_add, map_sub, Complex.conj_I, Complex.conj_natCast, Complex.conj_conj]
  ring

private theorem jt_actOn {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (x : C) :
    actOn rep ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) = (rep x).baseChange ℝ := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, _root_.one_mul]
  rfl

private theorem jt_psi {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (x : G.F)
    (J : ℝ ⊗[ℚ] G.C) :
    Matrix.trace (G.psiR v (J * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C x))) =
      Matrix.trace (G.psiR v J) * v.embedding x := by
  have h : G.psiR v ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (v.embedding x) := by
    unfold HTGroup.psiR
    erw [Algebra.TensorProduct.lift_tmul]
    simp only [map_one, _root_.one_mul]
    exact G.psi_F v x
  rw [map_mul, h]
  simp [Matrix.trace, Matrix.scalar_apply, Matrix.mul_diagonal, Finset.sum_mul]

private theorem jt_real {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ))
    (Jc : ℝ ⊗[ℚ] G.C) (h1 : ∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u)
    (h2 : ∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u) (c : 𝓞 D.F) :
    LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D)
        (actOn L.rep ℝ (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))) =
      2 * (Complex.I * (ρ (algebraMap (𝓞 D.F) D.O c)).trace).re := by
  have hX : Φ.conj (actOn L.rep ℝ (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))) =
      (Matrix.toLin' (Complex.I • ρ (algebraMap (𝓞 D.F) D.O c))).restrictScalars ℝ := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_mul, Module.End.mul_apply, jt_actOn,
      L.rep_F, h2, h1, LinearEquiv.apply_symm_apply, LinearMap.restrictScalars_apply,
      Matrix.toLin'_apply, Matrix.smul_mulVec]
  rw [← LinearMap.trace_conj' _ Φ, hX, GlobalTheory.UPel.HT.LieType.DimSum.trace_real_restrict, Matrix.trace_smul,
    smul_eq_mul]

theorem UpperTheory.trace_complex_structure_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (v : InfinitePlace G.F), D.a = 1 → TypeAt D ρ → sigPosH (G.gram_herm v) = 1 → ∀ (Φ : (ℝ ⊗[ℚ] VQ D) ≃ₗ[ℝ] (Fin D.g → ℂ)) (Jc : ℝ ⊗[ℚ] G.C), Jc * Jc = -1 → (∀ (b : D.O) u, Φ ((actQ D b).baseChange ℝ u) = ρ b *ᵥ Φ u) → (∀ u, Φ (actOn L.rep ℝ Jc u) = Complex.I • Φ u) → ∀ v' : InfinitePlace G.F, Matrix.trace (G.psiR v' Jc) = (if v'.embedding (L.e D.ω) = D.ρc then Complex.I else -Complex.I) * (2 * (if v' = v then 1 else 0) - (G.n : ℂ)) := by
  intro p _ D G L ρ v ha hT hv Φ Jc _ h1 h2 v'
  have hm : (D.m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.m_pos.ne'
  have hn : (G.n : ℂ) = (D.n : ℂ) := by rw [L.n_eq]
  let i0 : Fin D.a := ⟨0, by omega⟩
  have hsum : ∀ f : Fin D.a → ℂ, ∑ i, f i = f i0 := fun f =>
    Fintype.sum_eq_single i0 (fun j hj => absurd (Fin.ext (by simp only [i0]; omega)) hj)
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i0 := Fin.ext (by simp only [i0]; omega)
  rw [hii] at hi
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : D.F →+* ℂ, τ₁ = D.tau i0 := ⟨_, rfl⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : G.F →+* ℂ, σ₀ = G.iotaC.comp (L.s i0) := ⟨_, rfl⟩
  rw [← hσ₀] at hi
  have hσ : σ₀.comp (L.e : D.F →+* G.F) = τ₁ := by
    ext x
    rw [hσ₀, hτ₁]
    exact L.s_C i0 x
  have hτω : τ₁ (D.ω : D.F) = D.ρc := by rw [hτ₁]; exact D.tau_ω i0

  have hmain := jt_indep L.e
    (fun σ : D.F →+* ℂ => Complex.I * (D.m : ℂ) * ((if σ = τ₁ then 2 else 0) -
        (if σ = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
        (D.n : ℂ) * (if σ (D.ω : D.F) ≠ D.ρc then 1 else -1)))
    (fun w => (D.m : ℂ) * Matrix.trace (G.psiR w Jc)) (fun c => by
      have h484 := UpperTheory.trace_action_eq_sum_places p D G L (Jc * ((1 : ℝ) ⊗ₜ[ℚ] algebraMap G.F G.C (L.e c)))
      rw [jt_real D G L ρ Φ Jc h1 h2 c] at h484
      simp only [jt_psi] at h484
      have hTc := hT c
      rw [hsum, hsum, ← hτ₁] at hTc
      rw [hTc] at h484
      rw [jt_lhs D τ₁ c, Complex.add_conj, h484]
      have hw : ∀ w : InfinitePlace G.F, (D.m : ℂ) * Matrix.trace (G.psiR w Jc) * w.embedding (L.e c) +
          (starRingEnd ℂ) ((D.m : ℂ) * Matrix.trace (G.psiR w Jc)) *
            (starRingEnd ℂ) (w.embedding (L.e c)) =
          ((2 * (D.m : ℝ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c)).re : ℝ) : ℂ) := by
        intro w
        have hre : ((D.m : ℂ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c))).re =
            (D.m : ℝ) * (Matrix.trace (G.psiR w Jc) * w.embedding (L.e c)).re := by
          simp [Complex.mul_re]
        rw [← map_mul, Complex.add_conj, mul_assoc (D.m : ℂ), hre]
        push_cast
        ring
      simp only [hw]
      push_cast
      rw [Finset.mul_sum]) v'
  obtain ⟨σ', hσ'⟩ : ∃ σ' : D.F →+* ℂ, σ' = v'.embedding.comp (L.e : D.F →+* G.F) := ⟨_, rfl⟩
  rw [← hσ'] at hmain
  have hσω : σ' (D.ω : D.F) = v'.embedding (L.e D.ω) := by rw [hσ']; rfl
  rw [← hσω, hn]
  have hdiv : Matrix.trace (G.psiR v' Jc) = Complex.I * ((if σ' = τ₁ then 2 else 0) -
      (if σ' = (starRingEnd ℂ).comp τ₁ then 2 else 0) +
      (D.n : ℂ) * (if σ' (D.ω : D.F) ≠ D.ρc then 1 else -1)) := by
    apply mul_left_cancel₀ hm
    rw [← hmain]
    ring
  have hcj : ∀ f g : G.F →+* ℂ, f.comp (L.e : D.F →+* G.F) = g.comp (L.e : D.F →+* G.F) → f = g := by
    intro f g h
    ext y
    have := RingHom.congr_fun h (L.e.symm y)
    simpa using this
  have hconj : ((ComplexEmbedding.conjugate σ₀).comp (L.e : D.F →+* G.F)) = (starRingEnd ℂ).comp τ₁ := by
    rw [← hσ]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hvv : v' = v ↔ σ' = τ₁ ∨ σ' = (starRingEnd ℂ).comp τ₁ := by
    constructor
    · intro h
      rcases InfinitePlace.embedding_mk_eq σ₀ with h3 | h3
      · left
        rw [hσ', h, hi, h3, hσ]
      · right
        rw [hσ', h, hi, h3, hconj]
    · rintro (h | h)
      · rw [hi, ← hcj v'.embedding σ₀ (by rw [← hσ', h, hσ]), InfinitePlace.mk_embedding]
      · rw [hi, ← InfinitePlace.mk_conjugate_eq σ₀,
          ← hcj v'.embedding (ComplexEmbedding.conjugate σ₀) (by rw [← hσ', h, hconj]),
          InfinitePlace.mk_embedding]
  by_cases hε : σ' (D.ω : D.F) = D.ρc
  · have h2' : σ' ≠ (starRingEnd ℂ).comp τ₁ := by
      intro h
      have h3 : σ' (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by rw [h, RingHom.comp_apply, hτω]
      exact jt_ne D (h3.symm.trans hε)
    by_cases hw : v' = v
    · have h1' : σ' = τ₁ := (hvv.mp hw).resolve_right h2'
      rw [hdiv, if_pos h1', if_neg h2', if_pos hε, if_pos hw, if_neg (not_not.mpr hε)]
      ring
    · have h1' : σ' ≠ τ₁ := fun h => hw (hvv.mpr (Or.inl h))
      rw [hdiv, if_neg h1', if_neg h2', if_pos hε, if_neg hw, if_neg (not_not.mpr hε)]
      ring
  · have h1' : σ' ≠ τ₁ := fun h => hε (by rw [h, hτω])
    by_cases hw : v' = v
    · have h2' : σ' = (starRingEnd ℂ).comp τ₁ := (hvv.mp hw).resolve_left h1'
      rw [hdiv, if_neg h1', if_pos h2', if_neg hε, if_pos hw, if_pos hε]
      ring
    · have h2' : σ' ≠ (starRingEnd ℂ).comp τ₁ := fun h => hw (hvv.mpr (Or.inr h))
      rw [hdiv, if_neg h1', if_neg h2', if_neg hε, if_neg hw, if_pos hε]
      ring
