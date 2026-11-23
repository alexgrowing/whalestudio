import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

noncomputable section

open scoped ContDiff

namespace GlobalTheory.SepReal

theorem expS_mem_UJset {m : ℕ} {ε : Fin m → Bool} {X : Mat m} (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.MainNotions.S.UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_right_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, hJJ, hJJ⟩, rfl⟩
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, neg_mul]
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  have hc : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, hXh, hJinv]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.exp_conjTranspose, hc, Matrix.exp_conj _ _ hJu, hJinv]
  have hcomm : Commute (-(t • X)) (t • X) := (Commute.refl _).neg_left
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-(t • X)) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp (t • X)
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-(t • X)) * NormedSpace.exp (t • X)) := by
        rw [mul_assoc (Formalism.REAL.Jm ε * _) (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, mul_one, mul_assoc]
    _ = Formalism.REAL.Jm ε := by
        rw [← Matrix.exp_add_of_commute _ _ hcomm, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem orbit_sub_le {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : Mat m → (H →L[ℂ] H)} (hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π) {X : Mat m}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) {v : H} (hv : SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v) :
    ‖π (NormedSpace.exp X) v - v‖ ≤ ‖dR π X v‖ := by
  set f : ℝ → H := fun s => π (NormedSpace.exp (s • X)) v with hf
  have hcd : ContDiff ℝ ∞ f := by
    have h1 := hv 1 (fun _ => X) (fun _ => hX)
    have h2 : ContDiff ℝ ∞ (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    have h3 := h1.comp h2
    convert h3 using 1
    funext s
    simp [f, List.ofFn_succ]
  have hdiff : Differentiable ℝ f := hcd.differentiable (by simp)
  have hder : ∀ t : ℝ, HasDerivAt f (π (NormedSpace.exp (t • X)) (dR π X v)) t := by
    intro t
    set Lt := π (NormedSpace.exp (t • X)) with hLt
    have h0 : HasDerivAt f (dR π X v) 0 := (hdiff 0).hasDerivAt
    have h1 : HasDerivAt (fun u : ℝ => (Lt.restrictScalars ℝ) (f u)) ((Lt.restrictScalars ℝ) (dR π X v)) (t - t) := by
      rw [sub_self]; exact (Lt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h0
    have h2 := h1.comp_sub_const t t
    have hfun : f = fun s : ℝ => (Lt.restrictScalars ℝ) (f (s - t)) := by
      funext s
      have he : NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
        rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _), ← add_smul]
        congr 2; ring
      simp only [f, he, hπ.1.2 _ (expS_mem_UJset hX t) _ (expS_mem_UJset hX (s - t))]
      rfl
    rw [hfun]
    exact h2
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f)
    (f' := fun t => π (NormedSpace.exp (t • X)) (dR π X v)) (C := ‖dR π X v‖)
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => le_of_eq (hπ.2.1 _ (expS_mem_UJset hX t) _))
  simpa [f, hπ.1.1] using hb

end GlobalTheory.SepReal

namespace GlobalTheory.SepReal

theorem exists_lowUnit {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Mat m → (H →L[ℂ] H)} (hds : IsDS ε lam π) : ∃ v, IsLowUnit ε lam π v := by
  obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ))⁻¹ • v, ?_, ?_⟩
  · have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    simp [norm_smul, this]
  · exact (le_sSup hS : S ≤ lowKSub ε lam π) (S.smul_mem _ hvS)

theorem one_le_eightMB {m : ℕ} {lam : Fin m → ℝ} {B : ℝ} (hm : 3 ≤ m) (hlam : IsHCParam lam)
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ 8 * (m : ℝ) * B := by
  have i0 : 0 < m := by omega
  have i1 : 1 < m := by omega
  have hlt : lam ⟨1, i1⟩ < lam ⟨0, i0⟩ := hlam.1 (show (⟨0, i0⟩ : Fin m) < ⟨1, i1⟩ from by simp [Fin.lt_def])
  obtain ⟨k0, hk0⟩ := hlam.2 ⟨0, i0⟩
  obtain ⟨k1, hk1⟩ := hlam.2 ⟨1, i1⟩
  have hk : (k1 : ℝ) < k0 := by linarith
  have hk' : k1 < k0 := by exact_mod_cast hk
  have hk'' : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast hk'
  have h0 := hB ⟨0, i0⟩
  have h1 := hB ⟨1, i1⟩
  rw [abs_le] at h0 h1
  have hB2 : 1 / 2 ≤ B := by linarith
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem degUpper_of (hlog : LogNear) (hlie : LieBound) (_hvol : VolBall) : DegUpper := by
  unfold DegUpper ForDS
  intro m ε lam B hm hlam hgap hB H _ _ π hds d hd
  obtain ⟨v₀, hv₀⟩ := exists_lowUnit hds
  obtain ⟨hsm, hbd⟩ := hlie m ε lam B hm hlam hgap hB H π hds v₀ hv₀
  have hπ : IsURepOn (Formalism.MainNotions.S.UJset ε) π := hds.2.2.1
  have hB1 := one_le_eightMB hm hlam hB
  set c : ℝ := (8 * (m : ℝ) * B) ^ 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hcpos : 0 < c := by linarith
  set δ : ℝ := 1 / (4 * c) with hδ
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδ]; apply one_div_le_one_div_of_le (by norm_num); linarith
  have hv1 : ‖v₀‖ = 1 := hv₀.1

  have key : ∀ g ∈ nbh ε δ, (1 / 4 : ℝ) ≤ ‖coefOn π v₀ v₀ g‖ ^ 2 := by
    intro g hg
    have hgU : umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
    obtain ⟨X, hX, hXn, hXe⟩ := hlog m ε δ hδ4 (umat g) hgU hg
    have h1 := hbd [X] (by simpa using hX) (by simp)
    simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at h1
    have h2 : ‖dR π X v₀‖ ≤ 1 / 2 := by
      calc ‖dR π X v₀‖ ≤ c * hsn X := h1
        _ ≤ c * (2 * δ) := by gcongr
        _ = 1 / 2 := by rw [hδ]; field_simp; ring
    have h3 : ‖π (umat g) v₀ - v₀‖ ≤ 1 / 2 := by
      rw [← hXe]; exact (orbit_sub_le hπ hX hsm).trans h2
    have h4 : coefOn π v₀ v₀ g = 1 + ⟪v₀, π (umat g) v₀ - v₀⟫_ℂ := by
      simp only [coefOn, inner_sub_right, inner_self_eq_norm_sq_to_K, hv1]
      push_cast; ring
    have h5 : ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ 1 / 2 := by
      calc ‖⟪v₀, π (umat g) v₀ - v₀⟫_ℂ‖ ≤ ‖v₀‖ * ‖π (umat g) v₀ - v₀‖ := norm_inner_le_norm _ _
        _ ≤ 1 / 2 := by rw [hv1, one_mul]; exact h3
    have h6 : 1 / 2 ≤ ‖coefOn π v₀ v₀ g‖ := by
      rw [h4]
      have := norm_sub_norm_le (1 : ℂ) (-⟪v₀, π (umat g) v₀ - v₀⟫_ℂ)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    nlinarith

  obtain ⟨hdpos, hI⟩ := hd
  obtain ⟨hint, hval⟩ := hI v₀ v₀ v₀ v₀
  have hpt : ∀ g : UJ ε, coefOn π v₀ v₀ g * star (coefOn π v₀ v₀ g) = ((‖coefOn π v₀ v₀ g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint' : Integrable (fun g => ‖coefOn π v₀ v₀ g‖ ^ 2) (muG ε) := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  have hval' : ∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε = 1 / d := by
    have h := hval
    simp only [hpt, inner_self_eq_norm_sq_to_K, hv1] at h
    rw [integral_complex_ofReal] at h
    have h' : ((∫ g, ‖coefOn π v₀ v₀ g‖ ^ 2 ∂muG ε : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
      rw [h]; push_cast; ring
    exact_mod_cast h'
  have hlint : ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ) ≤ ENNReal.ofReal (1 / d) := by
    calc ENNReal.ofReal (1 / 4) * muG ε (nbh ε δ)
        ≤ ENNReal.ofReal (1 / 4) * muG ε {g | ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2)} := by
          gcongr
          intro g hg
          exact ENNReal.ofReal_le_ofReal (key g hg)
      _ ≤ ∫⁻ g, ENNReal.ofReal (‖coefOn π v₀ v₀ g‖ ^ 2) ∂muG ε :=
          mul_meas_ge_le_lintegral₀ hint'.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
      _ = ENNReal.ofReal (1 / d) := by
          rw [← hval', ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun g => by positivity)]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by positivity)] at ht
  have : (muG ε (nbh ε δ)).toReal ≤ 4 * (1 / d) := by linarith
  rwa [mul_one_div] at this

end GlobalTheory.SepReal
