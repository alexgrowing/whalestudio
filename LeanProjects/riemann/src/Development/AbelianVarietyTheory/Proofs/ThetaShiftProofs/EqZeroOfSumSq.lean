import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RiemannFormFramePeriodsEqMajorant

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.IsoTime

section Pair
variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

theorem trace_mul_pairE (ξ : Module.Dual ℤ X) (b : 𝓞 E) (x : X) :
    Algebra.trace ℚ E ((b : E) * pairE ξ x) = (ξ (b • x) : ℚ) := by
  classical
  have h1 : ∀ j, Algebra.trace ℚ E (((RingOfIntegers.basis E j : 𝓞 E) : E) * pairE ξ x) =
      (ξ (RingOfIntegers.basis E j • x) : ℚ) := by
    intro j
    unfold pairE
    rw [Finset.mul_sum, map_sum, Finset.sum_eq_single j]
    · have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
        (integralBasis E) j j
      rw [Algebra.traceForm_apply, if_pos rfl, integralBasis_apply] at this
      rw [← mul_assoc, mul_comm _ ((_ : ℤ) : E), ← zsmul_eq_mul, map_zsmul, mul_comm]
      erw [this]
      simp
    · intro i _ hij
      have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
        (integralBasis E) i j
      rw [Algebra.traceForm_apply, if_neg (Ne.symm hij), integralBasis_apply] at this
      rw [← mul_assoc, mul_comm _ ((_ : ℤ) : E), ← zsmul_eq_mul, map_zsmul, mul_comm]
      erw [this]
      simp
    · simp
  have hb := (RingOfIntegers.basis E).sum_repr b
  conv_lhs => rw [← hb]
  conv_rhs => rw [← hb]
  simp only [map_sum, Finset.sum_smul, Finset.sum_mul, map_zsmul, smul_assoc, smul_mul_assoc]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  have := h1 j
  simp only [zsmul_eq_mul] at *
  erw [this]
  simp

theorem pairE_smul (ξ : Module.Dual ℤ X) (a : 𝓞 E) (x : X) : pairE ξ (a • x) = (a : E) * pairE ξ x := by
  have h : ∀ j, Algebra.traceForm ℚ E (pairE ξ (a • x) - (a : E) * pairE ξ x) (integralBasis E j) = 0 := by
    intro j
    rw [Algebra.traceForm_apply, integralBasis_apply, mul_comm, mul_sub, map_sub, ← mul_assoc]
    have h1 := trace_mul_pairE ξ (RingOfIntegers.basis E j) (a • x)
    have h2 := trace_mul_pairE ξ (RingOfIntegers.basis E j * a) x
    rw [mul_smul, ← h1] at h2
    push_cast at h2
    erw [h2]
    exact sub_self _
  have h0 : Algebra.traceForm ℚ E (pairE ξ (a • x) - (a : E) * pairE ξ x) = 0 :=
    (integralBasis E).ext h
  refine sub_eq_zero.mp ((traceForm_nondegenerate ℚ E).1 _ fun n => ?_)
  rw [h0]; rfl

end Pair

theorem re_herm_eq {g : ℕ} {Λ : Type} (P : Λ → (Fin g → ℂ)) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a b, (hermForm Hm' (L (P a)) (L (P b))).im = (hermForm Hm (P a) (P b)).im) (z : Fin g → ℂ) :
    (hermForm Hm' (L z) (L z)).re = (hermForm Hm z z).re := by
  have hs : ∀ (r : ℝ) (u : Fin g → ℂ), r • u = (r : ℂ) • u := fun r u => by ext; simp
  have h1 : ∀ b u, (hermForm Hm' (L u) (L (P b))).im = (hermForm Hm u (P b)).im := by
    intro b u
    have hu : u ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a b
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add, add_dotProduct, Complex.add_im] at *
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [hermForm, hs, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at *
      rw [hx]
  have h2 : ∀ u v, (hermForm Hm' (L u) (L v)).im = (hermForm Hm u v).im := by
    intro u v
    have hu : v ∈ Submodule.span ℝ (Set.range P) := hP ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h1 a u
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at *
      rw [hx, hy]
    | smul r x _ hx =>
      simp only [hermForm, hs, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at *
      rw [hx]
  have h3 := h2 (Complex.I • z) z
  simpa [hermForm, smul_dotProduct] using h3

theorem herm_nsmul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (m : ℤ) (z : Fin g → ℂ) :
    (hermForm Hm (m • z) (m • z)).re = (m : ℝ) ^ 2 * (hermForm Hm z z).re := by
  have hs : m • z = ((m : ℝ) : ℂ) • z := by ext; simp
  simp only [hermForm, hs, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
        Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem emb_cc (τ : E →+* ℂ) (a : E) : τ (cc a) = (starRingEnd ℂ) (τ a) :=
  IsCMField.complexEmbedding_complexConj E τ a

theorem maj_smul (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = ‖c‖ ^ 2 * X.maj x τ v := by
  have h1 : ∀ u, hermC τ.1 X.Gm (c • v) u = c * hermC τ.1 X.Gm v u := by
    intro u
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : hermC τ.1 X.Gm v (c • v) = (starRingEnd ℂ) c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h3 : c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h4 : X.posPart x τ (c • v) = ‖c‖ ^ 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [← Complex.re_ofReal_mul, ← h3]
    congr 1
    simp only [h1, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  unfold Data.maj
  rw [h4, h1, h2, ← mul_assoc c, h3, Complex.re_ofReal_mul]
  ring

theorem sum_cm (X : Data E r) (f : (E →+* ℂ) → ℂ) :
    ∑ τ, f τ = ∑ τ : X.Ψ, (f τ.1 + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext; simp
  rw [Finset.sum_coe_sort X.Ψ (fun τ => f τ + f (ComplexEmbedding.conjugate τ)), Finset.sum_add_distrib,
    ← Finset.sum_add_sum_compl X.Ψ]
  congr 1
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [X.cmType, hinv]; simpa using hτ
  · intro τ hτ
    simpa using (X.cmType τ).1 hτ
  · intro τ _; exact hinv τ
  · intro τ _; exact hinv τ
  · intro τ _; rw [hinv]

theorem trace_cm (X : Data E r) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : X.Ψ, 2 * (τ.1 z).re := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ τ : E →+* ℂ, τ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  rw [h2, sum_cm X] at h
  have := congrArg Complex.re h
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Complex.add_re,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at this
  rw [this]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [IsCMField E] in
theorem exists_den (z : E) : ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • z) :=
  ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)).exists_integral_multiple

theorem eq_zero_of_sum_sq (X : Data E r) (d : X.Ψ → ℝ)
    (h : ∀ a : 𝓞 E, ∑ τ : X.Ψ, ‖τ.1 (a : E)‖ ^ 2 * d τ = 0) (τ : X.Ψ) : d τ = 0 := by
  classical
  have h1 : ∀ a : 𝓞 E, ∑ τ : X.Ψ, 2 * (τ.1 (a : E)).re * d τ = 0 := by
    intro a
    have e1 := h (a + 1)
    have e2 := h a
    have e3 := h 1
    have : ∑ τ : X.Ψ, 2 * (τ.1 (a : E)).re * d τ = ∑ τ : X.Ψ, ‖τ.1 ((a + 1 : 𝓞 E) : E)‖ ^ 2 * d τ -
        ∑ τ : X.Ψ, ‖τ.1 (a : E)‖ ^ 2 * d τ - ∑ τ : X.Ψ, ‖τ.1 ((1 : 𝓞 E) : E)‖ ^ 2 * d τ := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      push_cast
      simp
      ring
    rw [this, e1, e2, e3]; ring
  let D : (E →+* ℂ) → ℂ := fun τ => if hτ : τ ∈ X.Ψ then (d ⟨τ, hτ⟩ : ℂ) else
    (d ⟨ComplexEmbedding.conjugate τ, by by_contra hc; exact hτ ((X.cmType τ).2 hc)⟩ : ℂ)
  have hinv : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext; simp
  have hD1 : ∀ τ : X.Ψ, D τ.1 = d τ := fun τ => by simp [D]
  have hD2 : ∀ τ : X.Ψ, D (ComplexEmbedding.conjugate τ.1) = d τ := fun τ => by
    simp only [D, dif_neg ((X.cmType τ.1).1 τ.2), hinv]
  have h2 : ∀ a : 𝓞 E, ∑ τ : E →+* ℂ, D τ * τ (a : E) = 0 := by
    intro a
    rw [sum_cm X]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1 a)
    simp only [Complex.ofReal_sum, Complex.ofReal_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hD1, hD2, ComplexEmbedding.conjugate_coe_eq, ← mul_add, Complex.add_conj]
    push_cast; ring
  have h3 : ∀ z : E, ∑ τ : E →+* ℂ, D τ * τ z = 0 := by
    intro z
    obtain ⟨m, hm, hi⟩ := exists_den z
    have := h2 ⟨m • z, hi⟩
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    refine (mul_eq_zero.1 ?_).resolve_left hm'
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change _ = D τ * τ (m • z)
    rw [map_zsmul, zsmul_eq_mul]; ring
  have hli : LinearIndependent ℂ (fun τ : E →+* ℂ => (τ : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun τ : E →+* ℂ => (τ : E →* ℂ)) RingHom.coe_monoidHom_injective
  have h4 := Fintype.linearIndependent_iff.1 hli D (by ext z; simpa using h3 z) τ.1
  rw [hD1] at h4
  exact_mod_cast h4

theorem tt_eq_im_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (k : U.Comp) (ξ : Module.Dual ℤ a.D₀.X) (ξ' : Fin r → E) (sE : E) (w : ℂ) (x : (U.X k).dom) (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), GoodEmb c σ → IsUnf U → NormOne Ha → Ha.T < w.im → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → IsBePar ξ a.be sE → (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w v)) → (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') → (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') → ∀ τ, (U.X k).tt ξ' x.1 τ = w.im * (τ.1 sE).re := by
  intro E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha k ξ ξ' sE w x L γ hG hU hN hw _ hξ hs hL hE ⟨t, ht, htξ⟩ τ₀
  obtain ⟨nn, hn1, hn2, hn3, hn4, -, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
  obtain ⟨-, -, -, hsp, Hm, hH⟩ := Ha.period w hw
  obtain ⟨-, -, -, -, Hm', hH'⟩ := Uw.period k x
  have hmaj := (GlobalTheory.RiemMaj.riemann_eq_majorant E H Dw l Xo c σ r U Uw k x Hm' hG hU hH').1
  have hre : ∀ u, (hermForm Hm (Ha.Pw w u) (Ha.Pw w u)).re =
      ∑ τ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k (γ u) : Fin r → E)) := by
    intro u
    rw [← hmaj, hL]
    refine (re_herm_eq (Ha.Pw w) hsp Hm Hm' L.toLinearMap (fun u v => ?_) _).symm
    simp only [LinearEquiv.coe_coe]
    rw [← hL, ← hL, hH'.2.2, hH.2.2, hE]
  set M : (U.X k).Ψ → ℝ := fun τ => (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 ξ') with hM
  have hreal : ∀ τ : E →+* ℂ, τ sE = ((τ sE).re : ℂ) := fun τ => by
    have := emb_cc τ sE
    rw [hs.1] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  have hcc : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z => by
    have : ((Algebra.trace ℚ E (cc z) : ℚ) : ℝ) = ((Algebra.trace ℚ E z : ℚ) : ℝ) := by
      rw [trace_cm (U.X k), trace_cm (U.X k)]
      simp only [emb_cc, Complex.conj_re]
    exact_mod_cast this
  have key : ∀ v, ∑ τ : (U.X k).Ψ, ‖τ.1 (pairE ξ (Ha.y v))‖ ^ 2 *
      ((τ.1 sE).re ^ 2 * M τ * w.im - (τ.1 sE).re) = 0 := by
    intro v
    set p : E := pairE ξ (Ha.y v) with hp
    obtain ⟨m, hm, hi⟩ := exists_den (2 * sE * p)
    set b : 𝓞 E := ⟨_, hi⟩ with hb
    have hbE : (b : E) = m • (2 * sE * p) := rfl
    have h1 : m • nn v = b • t := by
      apply (Uw.F.Di Ha.i).unimod.1
      ext v'
      have e1 := hn2 v v'
      have e2 := ht (H.bar b • v')
      rw [← (Uw.F.Di Ha.i).adj, Ha.y.map_smul] at e2
      have e3 := trace_mul_pairE ξ (H.bar b) (Ha.y v')
      have e4 := hs.2 (Ha.y v) (Ha.y v')
      rw [← hcc, H.bar_eq] at e3
      have e5 : cc (IsCMField.complexConj E (b : E) * pairE ξ (Ha.y v')) =
          m • (2 * sE * p * cc (pairE ξ (Ha.y v'))) := by
        unfold cc
        rw [map_mul, IsCMField.complexConj_apply_apply, hbE, smul_mul_assoc]
      rw [e5, map_zsmul, hp, e4, ← e2, ← e1] at e3
      have : (((Uw.F.Di Ha.i).EF (m • nn v) v' : ℤ) : ℚ) = (((Uw.F.Di Ha.i).EF (b • t) v' : ℤ) : ℚ) := by
        rw [map_zsmul, LinearMap.smul_apply]
        simp only [zsmul_eq_mul, smul_eq_mul] at e3 ⊢
        push_cast at e3 ⊢
        linarith
      exact_mod_cast this
    have h2 : Ha.N v = Ha.Pw w (nn v) := by
      rw [Ha.Pw_eq, hn1 (nn v), hn4 _ (hn3 v), map_zero, smul_zero, add_zero, hn1]
    have h3 := hre (m • nn v)
    rw [map_zsmul, herm_nsmul, ← h2, h1] at h3
    have h4 : ∀ τ : (U.X k).Ψ, (U.X k).c τ * (U.X k).maj x.1 τ (Data.emb τ.1 (Uw.φ k (γ (b • t)) : Fin r → E)) =
        (m : ℝ) ^ 2 * (4 * (τ.1 sE).re ^ 2 * ‖τ.1 p‖ ^ 2 * M τ) := by
      intro τ
      have : Data.emb τ.1 (Uw.φ k (γ (b • t)) : Fin r → E) = τ.1 (b : E) • Data.emb τ.1 ξ' := by
        rw [map_smul, map_smul, Submodule.coe_smul, htξ]
        ext i
        simp only [Data.emb, Pi.smul_apply, smul_eq_mul, ← map_mul]
        rfl
      rw [this, maj_smul, hbE, map_zsmul, zsmul_eq_mul, map_mul, map_mul, hreal τ.1]
      simp only [norm_mul, mul_pow, Complex.norm_intCast, sq_abs, Complex.norm_real, Real.norm_eq_abs, map_ofNat,
        Complex.norm_ofNat, Complex.ofReal_re, hM]
      ring
    simp only [h4, ← Finset.mul_sum] at h3
    have hm' : (m : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm)
    have h5 := mul_left_cancel₀ hm' h3
    have h6 := hN w hw Hm hH v
    have h7 : ((a.be (Ha.y v) (Ha.y v) : ℤ) : ℝ) = ∑ τ : (U.X k).Ψ, 4 * ‖τ.1 p‖ ^ 2 * (τ.1 sE).re := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hs.2 (Ha.y v) (Ha.y v))
      simp only [Rat.cast_intCast] at this
      rw [← this, trace_cm (U.X k)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← hp, mul_assoc, map_mul, map_mul, map_mul, emb_cc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        hreal τ.1, map_ofNat]
      have e : (2 : ℂ) * ((τ.1 sE).re : ℂ) * ((‖τ.1 p‖ ^ 2 : ℝ) : ℂ) =
          ((2 * (τ.1 sE).re * ‖τ.1 p‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.ofReal_re, Complex.ofReal_re]
      ring
    rw [h5, h7, Finset.sum_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h6
    refine mul_left_cancel₀ (four_ne_zero) ?_
    rw [mul_zero, ← h6, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, ξ y₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hξ (LinearMap.ext hc)
  obtain ⟨v₀, rfl⟩ := Ha.y_onto y₀
  have hp0 : (pairE ξ (Ha.y v₀) : E) ≠ 0 := fun h0 => hy₀ (by
    have := trace_mul_pairE ξ (1 : 𝓞 E) (Ha.y v₀)
    rw [h0, mul_zero, map_zero, one_smul] at this
    exact_mod_cast this.symm)
  have hs0 : sE ≠ 0 := fun h0 => by
    have e1 := a.be_pos (Ha.y v₀) (fun h => hy₀ (by rw [h, map_zero]))
    have e2 := hs.2 (Ha.y v₀) (Ha.y v₀)
    rw [h0] at e2
    simp only [mul_zero, zero_mul, map_zero] at e2
    have : a.be (Ha.y v₀) (Ha.y v₀) = 0 := by exact_mod_cast e2.symm
    omega
  have hfin := eq_zero_of_sum_sq (U.X k) (fun τ => ‖τ.1 (pairE ξ (Ha.y v₀))‖ ^ 2 *
      ((τ.1 sE).re ^ 2 * M τ * w.im - (τ.1 sE).re)) (fun b => by
    rw [← key (b • v₀)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_smul, pairE_smul, map_mul, norm_mul]
    ring) τ₀
  have hs1 : (τ₀.1 sE).re ≠ 0 := fun h0 => by
    have := hreal τ₀.1
    rw [h0] at this
    exact hs0 ((map_eq_zero τ₀.1).1 (by simpa using this))
  have hq := (mul_eq_zero.1 hfin).resolve_left
    (pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero τ₀.1).2 hp0)))
  have hq' : M τ₀ * (w.im * (τ₀.1 sE).re) = 1 := by
    apply mul_left_cancel₀ hs1
    linear_combination hq
  change 1 / M τ₀ = _
  rw [one_div]
  exact (eq_inv_of_mul_eq_one_right hq').symm

end GlobalTheory.ArcQ.IsoTime
