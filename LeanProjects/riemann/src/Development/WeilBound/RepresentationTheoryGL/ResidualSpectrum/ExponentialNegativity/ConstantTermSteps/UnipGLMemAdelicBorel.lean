import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.ConjBlock

noncomputable section

open NumberField MeasureTheory Filter Topology Polynomial
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing Pointwise

namespace PositivityTheory.Rg.Rs.ctstepglue

open PositivityTheory.Rg.Rs.An

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem unipGL_mem_adelicBorel (r : ℕ) (X : UPos n r → 𝔸[K]) :
    (unipGL X : AdelicGLn.AdelicGL K n) ∈ (adelicBorel (K := K) (n := n)) := by
  rw [mem_adelicBorel, coe_unipGL]
  intro i j hij
  have hij' : (j : ℕ) < i := hij
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  have hne : i ≠ j := fun h => by subst h; omega
  rw [if_neg hne, dif_neg (by omega), add_zero]

theorem ctn_unipGL_mul {r : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : IsLeftInvariant φ)
    (X : UPos n r → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    ctn r φ (unipGL X * g) = ctn r φ g := by
  unfold ctn
  congr 1
  have hFD := isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hFD' := hFD.vadd_of_comm X
  rw [constantTerm_eq_setIntegral hφ hFD' g]
  simp only [constantTerm, ← mul_assoc, ← unipGL_add]
  rw [show X +ᵥ unipFundamentalDomain K n r = (fun Z => X + Z) '' unipFundamentalDomain K n r from
      Set.image_vadd.symm,
    (measurePreserving_add_left (unipMeasure K n r) X).setIntegral_image_emb
      (measurableEmbedding_addLeft X)]
  congr 1
  ext Z
  rw [add_comm]

theorem norm_ctn_le {r : ℕ} (φ : AdelicGLn.AdelicGL K n → ℂ) {D : Set (UPos n r → 𝔸[K])}
    (hD : IsCompact D) (hFD : unipFundamentalDomain K n r ⊆ D) (g : AdelicGLn.AdelicGL K n)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ X ∈ D, ‖φ (unipGL X * g)‖ ≤ M) : ‖ctn r φ g‖ ≤ M := by
  unfold ctn
  have hfin : unipMeasure K n r (unipFundamentalDomain K n r) < ⊤ :=
    (measure_mono hFD).trans_lt hD.measure_lt_top
  have hI : ‖constantTerm r φ g‖ ≤ M * (unipMeasure K n r).real (unipFundamentalDomain K n r) :=
    norm_setIntegral_le_of_norm_le_const hfin (fun X hX => h X (hFD hX))
  set v := (unipMeasure K n r).real (unipFundamentalDomain K n r) with hv'
  have hv : 0 ≤ v := measureReal_nonneg
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hv]
  rcases hv.eq_or_lt with h0 | h0
  · rw [← h0]; simp [hM]
  · calc v⁻¹ * ‖constantTerm r φ g‖ ≤ v⁻¹ * (M * v) := by gcongr
      _ = M := by field_simp

theorem bnd_ctn {r : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} {m : ℕ → ℝ} (h : Bnd φ m) :
    Bnd (ctn r φ) m := by
  intro ω hω hωB t₀ Q hQ
  obtain ⟨D, hD, hFD⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  set ω' := (fun p : (UPos n r → 𝔸[K]) × AdelicGLn.AdelicGL K n => unipGL p.1 * p.2) '' (D ×ˢ ω)
  have hω' : IsCompact ω' :=
    (hD.prod hω).image ((continuous_unipGL.comp continuous_fst).mul continuous_snd)
  have hω'B : ω' ⊆ (adelicBorel (K := K) (n := n) : Set _) := by
    rintro _ ⟨⟨X, b⟩, ⟨hX, hb⟩, rfl⟩
    exact mul_mem (unipGL_mem_adelicBorel r X) (hωB hb)
  obtain ⟨C, hC⟩ := h ω' hω' hω'B t₀ Q hQ
  refine ⟨max C 0, fun b hb x hx q hq => ?_⟩
  refine norm_ctn_le φ hD hFD _ (by positivity) fun X hX => ?_
  have := hC (unipGL X * b) ⟨(X, b), ⟨hX, hb⟩, rfl⟩ x hx q hq
  rw [← mul_assoc, ← mul_assoc]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem tor_add (x y : Fin n → ℝ) : tor K (x + y) = tor K x * tor K y := by
  unfold tor
  rw [← map_mul]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [posIdele_mul]
  congr 1
  exact Real.exp_add _ _

theorem aR_mul (r : ℕ) (s t : ℝ) : aR K n r s * aR K n r t = aR K n r (s + t) := by
  unfold aR
  rw [← tor_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem borel_aR {r : ℕ} {b : AdelicGLn.AdelicGL K n} (hb : b ∈ (adelicBorel (K := K) (n := n)))
    (t : ℝ) : ∃ X : UPos n r → 𝔸[K], b * aR K n r t = unipGL X * (aR K n r t * b) := by
  obtain ⟨Y, hY0, hY⟩ := conj_block r b hb
    (fun i => posIdele (K := K) (Real.exp (if (i : ℕ) < r then t else 0)) (Real.exp_pos _))
    (by
      intro i j hij
      by_cases hi : (i : ℕ) < r
      · simp [hi, hij.1 hi]
      · simp [hi, (not_congr hij).1 hi])
  refine ⟨fun p => Y p.1.1 p.1.2, Units.ext ?_⟩
  have e : unipMatrix (fun p : UPos n r => Y p.1.1 p.1.2) = 1 + Y := by
    unfold unipMatrix
    congr 1
    ext i j
    rw [blockEntry_apply]
    split_ifs with h
    · rfl
    · exact (hY0 i j h).symm
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_unipGL, e]
  simpa only [aR, tor, coe_diagUnits] using hY

def shift (r : ℕ) (x : Fin n → ℝ) (s : ℝ) : Fin n → ℝ := fun i => x i + if (i : ℕ) < r then s else 0

theorem sr_shift {r : ℕ} (hr : 0 < r) (hrn : r < n) (x : Fin n → ℝ) (s : ℝ) (r' : ℕ) :
    sr (shift r x s) r' = sr x r' + if r' = r then s else 0 := by
  unfold sr
  by_cases h : 0 < r' ∧ r' < n
  · rw [dif_pos h, dif_pos h]
    simp only [shift]
    split_ifs <;> first | omega | ring
  · rw [dif_neg h, dif_neg h]
    have : r' ≠ r := by omega
    simp [this]

theorem tor_shift (r : ℕ) (x : Fin n → ℝ) (s : ℝ) : tor K (shift r x s) = aR K n r s * tor K x := by
  unfold aR
  rw [← tor_add]
  congr 1
  funext i
  simp only [shift, Pi.add_apply]
  split_ifs <;> ring

end PositivityTheory.Rg.Rs.ctstepglue

end
