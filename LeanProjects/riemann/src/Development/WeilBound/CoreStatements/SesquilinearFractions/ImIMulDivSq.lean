import Development.WeilBound.CoreStatements.SesquilinearFractions.HermSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Xgf.DPer

open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem trace_sum (A : E) : (((Algebra.trace ℚ E A : ℚ) : ℝ) : ℂ) = ∑ σ : E →+* ℂ, σ A := by
  rw [Complex.ofReal_ratCast,
    show ((Algebra.trace ℚ E A : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E A) from (eq_ratCast _ _).symm,
    trace_eq_sum_embeddings]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

theorem trace_re (A : E) : ((Algebra.trace ℚ E A : ℚ) : ℝ) =
    ∑ σ ∈ Finset.univ.filter (fun σ : E →+* ℂ => σ (H.rt : E) = H.rt0), 2 * (σ A).re := by
  have h1 := congrArg Complex.re (trace_sum A)
  rw [Complex.ofReal_re, Complex.re_sum, sum_split (H := H)] at h1
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  ring

variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {p q : ℕ} (hty : IsTypeFn H p q ty)
variable (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) E)
variable {D : Datum H} (c : D.La →ₗ[𝓞 E] (Fin p ⊕ Fin q →₀ 𝓞 E)) (n : ℕ)

theorem per_at_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y : D.La) (a : Fin p) :
    per hty c n y ((eP hty σ h).symm a).1 = σ ((c y (.inl a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inl hty σ h _ ((eP hty σ h).symm a).2, ((eP hty σ h).symm a).2]
  simp

theorem per_at_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y : D.La) (a : Fin q) :
    per hty c n y ((eQ hty σ h).symm a).1 = σ ((c y (.inr a) : 𝓞 E) : E) / n := by
  rw [per_apply, blk_inr hty σ h _ ((eQ hty σ h).symm a).2, ((eQ hty σ h).symm a).2]
  simp

def blkA (y y' : D.La) : E := ∑ a : Fin p, ∑ b : Fin p,
  ((c y (.inl a) : 𝓞 E) : E) * G (.inl a) (.inl b) * IsCMField.complexConj E ((c y' (.inl b) : 𝓞 E) : E)

def blkB (y y' : D.La) : E := ∑ a : Fin q, ∑ b : Fin q,
  ((c y (.inr a) : 𝓞 E) : E) * G (.inr a) (.inr b) * IsCMField.complexConj E ((c y' (.inr b) : 𝓞 E) : E)

theorem Q_per_inl (σ : E →+* ℂ) (h : σ (H.rt : E) = H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkA G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inl hty G σ h]
  simp only [per_at_inl, blkA, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem Q_per_inr (σ : E →+* ℂ) (h : σ (H.rt : E) ≠ H.rt0) (y y' : D.La) :
    Q hty G σ (per hty c n y) (per hty c n y') = Complex.I * (2 * σ (blkB G c y y') / ((n : ℂ) * n)) := by
  rw [Q_inr hty G σ h]
  simp only [per_at_inr, blkB, map_sum, map_mul, IsCMField.complexEmbedding_complexConj, map_div₀, map_natCast,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem im_I_mul_div_sq (z : ℂ) (n : ℕ) : (Complex.I * (2 * z / ((n : ℂ) * n))).im = 2 * z.re / ((n : ℝ) * n) := by
  have e : (2 * z / ((n : ℂ) * n)) = ((2 / ((n : ℝ) * n) : ℝ) : ℂ) * z := by push_cast; ring
  rw [e, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofReal_mul]
  ring

theorem herm_im (y y' : D.La) :
    (hermForm (Hm hty G) (per hty c n y) (per hty c n y')).im =
      ((Algebra.trace ℚ E (blkA G c y y' + blkB G c y y') : ℚ) : ℝ) / ((n : ℝ) * n) := by
  rw [herm_split, Complex.im_sum, sum_split (H := H), ← Finset.sum_add_distrib, trace_re (H := H),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  have h : σ (H.rt : E) = H.rt0 := (Finset.mem_filter.mp hσ).2
  have h' : ComplexEmbedding.conjugate σ (H.rt : E) ≠ H.rt0 := fun hc => (conjugate_rt σ).mp hc h
  rw [Q_per_inl hty G c n σ h, Q_per_inr hty G c n _ h', im_I_mul_div_sq, im_I_mul_div_sq,
    ComplexEmbedding.conjugate_coe_eq, Complex.conj_re, map_add, Complex.add_re]
  ring

theorem sesq_blocks (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    blkA (gramE D x) c y y' + blkB (gramE D x) c y y' = (n : E) * n * sesq D y y' := by
  obtain ⟨-, hl, hr, hsl, hsr, hsk, -⟩ := sesq_sesquilinear_properties D
  let L : D.La → D.La →+ E := fun y' => AddMonoidHom.mk' (fun u => sesq D u y') (fun a b => hl a b y')
  let R : D.La → D.La →+ E := fun u => AddMonoidHom.mk' (fun v => sesq D u v) (fun a b => hr u a b)
  have key : sesq D (n • y) (n • y') = (n : E) * n * sesq D y y' := by
    have e1 : sesq D (n • y) (n • y') = n • sesq D y (n • y') := map_nsmul (L (n • y')) n y
    have e2 : sesq D y (n • y') = n • sesq D y y' := map_nsmul (R y) n y'
    rw [e1, e2, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [← key, ← hc y, ← hc y']
  have e3 : sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) = ∑ m, ∑ m', ((c y m : 𝓞 E) : E) *
      sesq D (x m) (x m') * IsCMField.complexConj E ((c y' m' : 𝓞 E) : E) := by
    rw [show sesq D (∑ m, c y m • x m) (∑ m, c y' m • x m) =
      L (∑ m, c y' m • x m) (∑ m, c y m • x m) from rfl, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show L (∑ m, c y' m • x m) (c y m • x m) = sesq D (c y m • x m) (∑ m, c y' m • x m) from rfl,
      hsl, show sesq D (x m) (∑ m', c y' m' • x m') = R (x m) (∑ m', c y' m' • x m') from rfl,
      map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [show R (x m) (c y' m' • x m') = sesq D (x m) (c y' m' • x m') from rfl, hsr]
    ring
  have horth' : ∀ a b, sesq D (x (.inr b)) (x (.inl a)) = 0 := fun a b => by
    rw [hsk, horth, map_zero, neg_zero]
  rw [e3]
  simp only [Fintype.sum_sum_type, blkA, blkB, gramE, Matrix.of_apply, horth, horth', mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

theorem herm_EF (hn : 0 < n) (x : Fin p ⊕ Fin q → D.La) (hc : ∀ y, ∑ m, c y m • x m = n • y)
    (horth : ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0) (y y' : D.La) :
    (hermForm (Hm hty (gramE D x)) (per hty c n y) (per hty c n y')).im = D.EF y y' := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 := trace_mul_sesq_eq_form D 1 y y'
  rw [one_smul, show ((1 : 𝓞 E) : E) = 1 by simp, _root_.one_mul] at h1
  have ht : Algebra.trace ℚ E ((n : E) * n * sesq D y y') = ((n * n : ℕ) : ℚ) * (D.EF y y' : ℚ) := by
    rw [show (n : E) * n * sesq D y y' = (n * n : ℕ) • sesq D y y' by rw [nsmul_eq_mul]; push_cast; ring,
      map_nsmul, h1, nsmul_eq_mul]
  rw [herm_im, sesq_blocks c n x hc horth, ht]
  push_cast
  field_simp

end PositivityTheory.Xgf.DPer

end
