import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Chr.DetOrd

variable {L : Type} [Field L] [NumberField L]

theorem ordF_mul' (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) : ordF w (a * b) = ordF w a + ordF w b := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [Units.val_mul, map_mul, WithZero.log_mul ha hb]
  ring

theorem ordF_nonneg_of_isInteger (w : HeightOneSpectrum (𝓞 L)) (a : Lˣ)
    (h : IsLocalization.IsInteger (𝓞 L) (a : L)) : 0 ≤ ordF w a := by
  obtain ⟨r, hr⟩ := h
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hle : w.valuation L (a : L) ≤ 1 := by
    rw [← hr]; exact w.valuation_le_one r
  have := (WithZero.log_le_log ha one_ne_zero).2 hle
  unfold ordF
  simpa using this

theorem ordF_finite (a : Lˣ) : {w : HeightOneSpectrum (𝓞 L) | ordF w a ≠ 0}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 L) (a : L)).union
    (HeightOneSpectrum.Support.finite (𝓞 L) ((a⁻¹ : Lˣ) : L))).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hn
  apply hw
  have h0 : w.valuation L (a : L) ≠ 0 := by simp
  have h1 : w.valuation L (a : L) = 1 := by
    refine le_antisymm hn.1 ?_
    have h2 := hn.2
    rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
    exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 h2
  simp [ordF, h1]

theorem isFractional_detSub {N : ℕ} (M : Submodule (𝓞 L) (Fin N → L)) (hM : M.FG) :
    IsFractional (𝓞 L)⁰ (detSub M) := by
  obtain ⟨a, ha, hint⟩ := Formalism.L2.LamCM.A2.exists_den M hM
  refine ⟨a ^ N, pow_mem ha N, fun b hb => ?_⟩
  induction hb using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨x, hx, rfl⟩ := hd
    have : (a ^ N) • (Matrix.of x).det = (Matrix.of fun i j => a • x i j).det := by
      rw [show (Matrix.of fun i j => a • x i j) = (algebraMap (𝓞 L) L a) • Matrix.of x by
        ext i j; simp [Algebra.smul_def]]
      rw [Matrix.det_smul, Fintype.card_fin, Algebra.smul_def, map_pow]
    rw [this]
    exact Formalism.L2.LamCM.A2.isInteger_det _ fun i j => hint _ (hx i) j
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy => rw [smul_add]; exact IsLocalization.isInteger_add hx hy
  | smul r x _ hx => rw [smul_comm]; exact IsLocalization.isInteger_smul hx

theorem exists_bound {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) :
    ∃ d : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ∀ k : Lˣ, (k : L) ∈ A → -ordF w d ≤ ordF w k := by
  obtain ⟨a, ha, hint⟩ := h
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero ha
  refine ⟨Units.mk0 _ ha0, fun w k hk => ?_⟩
  have h1 := ordF_nonneg_of_isInteger w (Units.mk0 _ ha0 * k) (by
    have := hint _ hk
    rwa [Algebra.smul_def] at this)
  rw [ordF_mul'] at h1
  linarith

theorem isLeast_ordSub {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    IsLeast {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} (ordSub w A) := by
  obtain ⟨d, hd⟩ := exists_bound h
  have hb : BddBelow {n | ∃ k : Lˣ, (k : L) ∈ A ∧ ordF w k = n} :=
    ⟨-ordF w d, by rintro n ⟨k, hk, rfl⟩; exact hd w k hk⟩
  exact ⟨Int.csInf_mem ⟨_, k0, hk0, rfl⟩ hb, fun n hn => csInf_le hb hn⟩

theorem ordSub_finite {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A) :
    {w : HeightOneSpectrum (𝓞 L) | ordSub w A ≠ 0}.Finite := by
  obtain ⟨d, hd⟩ := exists_bound h
  refine ((ordF_finite d).union (ordF_finite k0)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
  apply hw
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  have h1 := hl ⟨k0, hk0, rfl⟩
  have h2 := hd w k hk
  omega

theorem det_of_mulVec {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (x : Fin N → Fin N → L) :
    (Matrix.of fun i => γ.mulVec (x i)).det = γ.det * (Matrix.of x).det := by
  have : (Matrix.of fun i => γ.mulVec (x i)) = Matrix.of x * γ.transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, mul_comm]

theorem detSub_map {N : ℕ} (γ : Matrix (Fin N) (Fin N) L) (M : Submodule (𝓞 L) (Fin N → L)) :
    detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L))) =
      (detSub M).map (LinearMap.mulLeft (𝓞 L) γ.det) := by
  unfold detSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    choose x hx e using fun i => Submodule.mem_map.1 (hy i)
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    have : y = fun i => γ.mulVec (x i) := funext fun i => by
      rw [← e i]; simp
    rw [this, det_of_mulVec]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fun i => γ.mulVec (x i), fun i => Submodule.mem_map.2 ⟨x i, hx i, by simp⟩, ?_⟩
    rw [det_of_mulVec]
    rfl

theorem ordSub_map_mul {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (u : Lˣ) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A.map (LinearMap.mulLeft (𝓞 L) (u : L))) = ordF w u + ordSub w A := by
  obtain ⟨⟨k, hk, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine IsLeast.csInf_eq ⟨⟨u * k, Submodule.mem_map.2 ⟨k, hk, rfl⟩, by rw [ordF_mul', e]⟩, ?_⟩
  rintro n ⟨k', hk', rfl⟩
  obtain ⟨y, hy, ey⟩ := Submodule.mem_map.1 hk'
  have ey' : (u : L) * y = k' := ey
  have hy' : ((u⁻¹ * k' : Lˣ) : L) = y := by
    rw [Units.val_mul, ← ey', Units.inv_mul_cancel_left]
  have h1 := hl ⟨u⁻¹ * k', hy' ▸ hy, rfl⟩
  have h2 : ordF w k' = ordF w u + ordF w (u⁻¹ * k') := by
    rw [← ordF_mul', mul_inv_cancel_left]
  omega

end GlobalTheory.Mem.Chr.DetOrd

namespace GlobalTheory.Mem.Chr

open DetOrd

open Classical in

theorem ordSub_detSub_lattice :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Submodule (𝓞 L) (Fin N → L)), M.FG → Submodule.span L (M : Set (Fin N → L)) = ⊤ → {w | ordSub w (detSub M) ≠ 0}.Finite ∧ (∀ w, IsLeast {n | ∃ k : Lˣ, (k : L) ∈ detSub M ∧ ordF w k = n} (ordSub w (detSub M))) ∧ ∀ (γ : Matrix (Fin N) (Fin N) L) (u : Lˣ), γ.det = u → ∀ w, ordSub w (detSub (M.map ((Matrix.toLin' γ).restrictScalars (𝓞 L)))) = ordF w u + ordSub w (detSub M) := by
  intro L _ _ N M hfg hsp
  have hf := isFractional_detSub M hfg
  obtain ⟨x, hx, hd⟩ := Formalism.L2.LamCM.A2.exists_det_ne M hsp
  have hk : ((Units.mk0 _ hd : Lˣ) : L) ∈ detSub M := det_mem_detSub x hx
  refine ⟨ordSub_finite hf _ hk, isLeast_ordSub hf _ hk, fun γ u hu w => ?_⟩
  have e := detSub_map γ M
  have hu' : γ.det = u := by convert hu
  rw [hu'] at e
  have := ordSub_map_mul hf _ hk u w
  rw [← e] at this
  convert this

end GlobalTheory.Mem.Chr
