import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SkewAdCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, sig_sig σ h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

theorem sigR_alg (σ : E →ₐ[F] E) (c : F) :
    sigR (AF F) σ (algebraMap F (AF F ⊗[F] E) c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ).commutes c

theorem inclR_alg (c : F) : inclR (F := F) (AF F) (algebraMap F E c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes c

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem cT_apply {A : Type} [CommRing A] (s : A →+* A) {m p : Type} (M : Matrix m p A) (i : p) (k : m) :
    cT s M i k = s (M k i) := rfl

theorem cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (j : ℕ) : ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  classical
  haveI := hσ.1
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hσ _ _ _ hΩ₀ hcov j
  set s := sigR (AF F) σ with hs_def
  set hh : AF F ⊗[F] E := algebraMap F (AF F ⊗[F] E) 2⁻¹ with hh_def
  have h2 : hh * 2 = 1 := by
    rw [hh_def, ← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hsh : s hh = hh := sigR_alg σ _
  have hss : ∀ z, s (s z) = z := sigR_sigR σ hσ
  have hsi : ∀ e, s (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := sigR_inclR σ
  let sk : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    fun z => Matrix.of fun i k => hh * (z i k - s (z k i))
  have sk_skew : ∀ z, cT s (sk z) = -sk z := fun z => by
    ext i k
    simp only [cT_apply, sk, Matrix.of_apply, Matrix.neg_apply, map_mul, map_sub, hsh, hss]
    ring
  have hcont : Continuous fun p : (AF F ⊗[F] E) × (AF F ⊗[F] E) => hh * (p.1 - s p.2) :=
    continuous_const.mul (continuous_fst.sub ((continuous_sigR σ).comp continuous_snd))
  refine ⟨_, C, (hΩ.prod hΩ).image hcont, fun μ => ?_⟩
  obtain ⟨Y, hY, hc⟩ := h μ
  have hd : ∀ i, s ((GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i) = (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := fun i => by
    rw [map_pow, hs_def, GlobalTheory.Eis.Conv.sigR_halfE]
  have htor : (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    simp [tor, GlobalTheory.Eis.Conv.dg]
  have htor' : cT s (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    rw [htor]
    ext i k
    rw [cT_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik; simp [hd]
    · simp [hik, Ne.symm hik]
  refine ⟨Y.image sk, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)), ?_, fun x hx => ?_⟩
  · simp only [bse, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact sk_skew z
  · obtain ⟨S₀, y, hy, ω, hω, e⟩ := hc x hx
    set c : E := algebraMap F E 2⁻¹ with hc_def
    have hσc : σ c = c := σ.commutes _
    refine ⟨Matrix.of fun i k => c * (S₀ i k - σ (S₀ k i)), ?_, sk y, Finset.mem_image_of_mem _ hy, sk ω, sk_skew ω,
      fun i k => ⟨(ω i k, ω k i), ⟨hω i k, hω k i⟩, rfl⟩, ?_⟩
    · ext i k
      simp only [cT_apply, Matrix.of_apply, Matrix.neg_apply, AlgHom.coe_toRingHom, map_mul, map_sub, hσc,
        sig_sig σ hσ]
      ring
    · rw [htor', htor]
      ext i k
      have hx1 : s (x k i) = - x i k := by
        have := congrFun (congrFun hx i) k
        rwa [cT_apply, Matrix.neg_apply] at this
      have e1 := congrFun (congrFun e i) k
      have e2 := congrArg s (congrFun (congrFun e k) i)
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_add, map_mul,
        hsi, hd] at e1 e2
      rw [hx1] at e2
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adMat, Matrix.map_apply,
        Matrix.of_apply, sk, map_mul, map_sub, inclR_alg]
      rw [hc_def, inclR_alg, ← hh_def]
      linear_combination hh * e1 - hh * e2 - x i k * h2
end GlobalTheory.SkewAdCover
