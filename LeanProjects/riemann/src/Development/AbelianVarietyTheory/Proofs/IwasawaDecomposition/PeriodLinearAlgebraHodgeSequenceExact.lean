import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtIffIsDerivAt0
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsEigAtIffOfIsDerivAt0

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HodgeSeq

theorem exact_of_decomp {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Γ : Matrix (m ⊕ n) (m ⊕ n) ℂ) (C M : Matrix n (m ⊕ n) ℂ) (C' M' : Matrix m (m ⊕ n) ℂ) (hΓ : Γ.det ≠ 0)
    (h : Γ = Cᵀ * M + M'ᵀ * C') :
    C * ((Γᵀ)⁻¹ * C'ᵀ) = 0 ∧ (∃ R : Matrix m (m ⊕ n) ℂ, R * ((Γᵀ)⁻¹ * C'ᵀ) = 1) ∧
      ∃ S : Matrix (m ⊕ n) n ℂ, C * S = 1 := by
  have hu : IsUnit (Γᵀ).det := by rw [Matrix.det_transpose]; exact hΓ.isUnit
  have h1 : Matrix.fromCols ((Γᵀ)⁻¹ * C'ᵀ) ((Γᵀ)⁻¹ * Mᵀ) * Matrix.fromRows M' C = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add]
    have : C'ᵀ * M' + Mᵀ * C = Γᵀ := by
      rw [h, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_transpose, add_comm]
    rw [this, Matrix.nonsing_inv_mul _ hu]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  exact ⟨h2.2.2.1, ⟨_, h2.1⟩, _, h2.2.2.2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

omit [IsCMField E] in

theorem emb_ext {φ ψ : E →+* ℂ} (h : ∀ a : 𝓞 E, φ (a : E) = ψ (a : E)) : φ = ψ :=
  IsFractionRing.ringHom_ext (A := 𝓞 E) h

omit [IsCMField E] in

theorem indep {r : (E →+* ℂ) → (E →+* ℂ)} (hr : Function.Injective r) (f : (E →+* ℂ) → ℂ)
    (h : ∀ a : 𝓞 E, ∑ φ, f φ * r φ (a : E) = 0) (φ : E →+* ℂ) : f φ = 0 := by
  have hl := (linearIndependent_monoidHom (𝓞 E) ℂ).comp
    (fun φ : E →+* ℂ => ((r φ).comp (algebraMap (𝓞 E) E)).toMonoidHom)
    (fun φ ψ e => hr (emb_ext fun a => DFunLike.congr_fun e a))
  refine Fintype.linearIndependent_iff.1 hl f ?_ φ
  funext a
  simpa [Finset.sum_apply] using h a

omit [IsCMField E] in

theorem trace_eq {r : (E →+* ℂ) → (E →+* ℂ)} (hr : Function.Injective r) (a : E) :
    ((Algebra.trace ℚ E a : ℚ) : ℂ) = ∑ φ, r φ a := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := E) (x := a)
  rw [eq_ratCast] at h
  rw [h, (Finite.injective_iff_bijective.1 hr).sum_comp (fun φ => φ a)]
  exact ((RingHom.equivRatAlgHom (R := E) (S := ℂ)).sum_comp (fun φ => φ a)).symm

theorem conj_bar (φ : E →+* ℂ) (a : 𝓞 E) : starRingEnd ℂ (φ ((H.bar a : 𝓞 E) : E)) = φ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

section Pure

variable {L : Type} [Fintype L] [DecidableEq L]

def form (B : L → L → ℂ) (u v : L → ℂ) : ℂ := ∑ z, ∑ w, u z * B z w * starRingEnd ℂ (v w)

def imForm (B : L → L → ℂ) (s t : L → ℂ) : (L → ℂ) →ₗ[ℝ] (L → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (form B (s * u) (t * v)).im)
    (fun u u' v => by simp [form, mul_add, add_mul, Finset.sum_add_distrib])
    (fun a u v => by
      rw [smul_eq_mul, ← Complex.im_ofReal_mul]
      simp only [form, Finset.mul_sum, Pi.mul_apply, Pi.smul_apply, Complex.real_smul]
      congr 1
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring)
    (fun u v v' => by simp [form, mul_add, Finset.sum_add_distrib])
    (fun a u v => by
      rw [smul_eq_mul, ← Complex.im_ofReal_mul]
      simp only [form, Finset.mul_sum, Pi.mul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
      congr 1
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => by ring)

theorem form_single (B : L → L → ℂ) (z w : L) (a b : ℂ) :
    form B (Pi.single z a) (Pi.single w b) = a * B z w * starRingEnd ℂ b := by
  rw [form, Finset.sum_eq_single z (fun z' _ h => by simp [h]) (by simp),
    Finset.sum_eq_single w (fun w' _ h => by simp [h]) (by simp)]
  simp

theorem block (Di : Datum H) (t : L → (E →+* ℂ)) (Q : Di.La →+ (L → ℂ)) (B : L → L → ℂ)
    (hQ : ∀ (a : 𝓞 E) v z, Q (a • v) z = t z (a : E) * Q v z) (hs : Submodule.span ℝ (Set.range Q) = ⊤)
    (hB : ∀ x y, (form B (Q x) (Q y)).im = Di.EF x y) {z w : L} (hzw : t z ≠ t w) : B z w = 0 := by
  by_contra h0
  refine hzw (emb_ext fun a => ?_)
  have e : imForm B (fun z => t z (a : E)) 1 = imForm B 1 (fun z => t z ((H.bar a : 𝓞 E) : E)) := by
    refine LinearMap.ext_on_range hs fun x => LinearMap.ext_on_range hs fun y => ?_
    have e1 : (fun z => t z (a : E)) * Q x = Q (a • x) := funext fun z => (hQ a x z).symm
    have e2 : (fun z => t z ((H.bar a : 𝓞 E) : E)) * Q y = Q (H.bar a • y) := funext fun z => (hQ _ y z).symm
    simp only [imForm, LinearMap.mk₂_apply, e1, e2, _root_.one_mul, hB, Di.adj]
  have e' : ∀ s : ℂ, (s * (t z (a : E) * B z w)).im = (s * (t w (a : E) * B z w)).im := fun s => by
    have := LinearMap.congr_fun₂ e (Pi.single z s) (Pi.single w 1)
    simp only [imForm, LinearMap.mk₂_apply, _root_.one_mul, ← Pi.single_mul_right, form_single, _root_.mul_one, map_one, conj_bar] at this
    convert this using 2 <;> ring
  refine mul_right_cancel₀ h0 (Complex.ext ?_ ?_)
  · simpa only [Complex.I_mul_im] using e' Complex.I
  · simpa only [_root_.one_mul] using e' 1

end Pure

section Sigma

variable {m : (E →+* ℂ) → ℕ} {r : (E →+* ℂ) → (E →+* ℂ)}

def part (B : (Σ φ, Fin (m φ)) → (Σ φ, Fin (m φ)) → ℂ) (u v : (Σ φ, Fin (m φ)) → ℂ) (φ : E →+* ℂ) : ℂ :=
  ∑ i, ∑ j, u ⟨φ, i⟩ * B ⟨φ, i⟩ ⟨φ, j⟩ * starRingEnd ℂ (v ⟨φ, j⟩)

theorem emb_eq (hr : Function.Injective r) (hc : ∀ φ, r (conjEmb φ) = conjEmb (r φ)) (Di : Datum H)
    (Q : Di.La →+ ((Σ φ, Fin (m φ)) → ℂ)) (B : (Σ φ, Fin (m φ)) → (Σ φ, Fin (m φ)) → ℂ)
    (hQ : ∀ (a : 𝓞 E) v z, Q (a • v) z = r z.1 (a : E) * Q v z) (hs : Submodule.span ℝ (Set.range Q) = ⊤)
    (hB : ∀ x y, (form B (Q x) (Q y)).im = Di.EF x y) {x y : Di.La} {h : E}
    (hh : ∀ a : 𝓞 E, ((Di.EF (a • x) y : ℤ) : ℚ) = Algebra.trace ℚ E ((a : E) * h)) (τ : E →+* ℂ) :
    r τ h * (2 * Complex.I) = part B (Q x) (Q y) τ - starRingEnd ℂ (part B (Q x) (Q y) (conjEmb τ)) := by
  classical
  have hinv : Function.Involutive (conjEmb (E := E)) := fun φ => RingHom.ext fun a => by simp [conjEmb]
  rw [← sub_eq_zero]
  refine indep hr (fun τ => r τ h * (2 * Complex.I) -
    (part B (Q x) (Q y) τ - starRingEnd ℂ (part B (Q x) (Q y) (conjEmb τ)))) (fun a => ?_) τ
  have e1 : form B (Q (a • x)) (Q y) = ∑ φ, part B (Q x) (Q y) φ * r φ (a : E) := by
    rw [form, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [part, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_sigma, Finset.sum_eq_single φ (fun ψ _ hψ => Finset.sum_eq_zero fun j _ => by
      rw [block Di (fun z => r z.1) Q B hQ hs hB (fun e => hψ (hr e).symm), mul_zero, zero_mul]) (by simp),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hQ]; ring
  have e2 : starRingEnd ℂ (form B (Q (a • x)) (Q y)) =
      ∑ φ, starRingEnd ℂ (part B (Q x) (Q y) (conjEmb φ)) * r φ (a : E) := by
    rw [e1, map_sum, ← hinv.bijective.sum_comp]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [map_mul, hc]
    simp [conjEmb]
  have e3 : (((form B (Q (a • x)) (Q y)).im : ℝ) : ℂ) = ∑ φ, r φ h * r φ (a : E) := by
    rw [hB, Complex.ofReal_intCast, ← Rat.cast_intCast, hh, trace_eq hr]
    exact Finset.sum_congr rfl fun φ _ => by rw [map_mul, mul_comm]
  have e4 := Complex.sub_conj (form B (Q (a • x)) (Q y))
  rw [e2, Complex.ofReal_mul, e3, e1] at e4
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [e4, Finset.mul_sum, Finset.sum_mul, sub_eq_zero]
  exact Finset.sum_congr rfl fun φ _ => by push_cast; ring

end Sigma

variable {Dw : Datum H} {l : Level H}

theorem goodPer_of_form (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (Di : Datum H) (Q : Di.La →+ (Letter Dw → ℂ))
    (B : Letter Dw → Letter Dw → ℂ)
    (hQ : ∀ (a : 𝓞 E) v (z : Letter Dw), Q (a • v) z = Formalism.L2.PjFree.relab c σ z.1 (a : E) * Q v z)
    (hs : Submodule.span ℝ (Set.range Q) = ⊤) (hB : ∀ x y, (form B (Q x) (Q y)).im = Di.EF x y)
    {x : Idx Dw τ → Di.La} {hm : Matrix (Idx Dw τ) (Idx Dw τ) E} (hx : IsPerBasis Di x hm) : GoodPer c σ τ x hm Q := by
  have hr : Function.Injective (Formalism.L2.PjFree.relab (E := E) c σ) := fun φ ψ h =>
    GlobalTheory.DerivEig.eq_of_relab_eq c σ fun a => by rw [h]
  have hc : ∀ φ, Formalism.L2.PjFree.relab c σ (conjEmb φ) = conjEmb (Formalism.L2.PjFree.relab (E := E) c σ φ) := fun φ => by
    ext a
    have h1 : embF c (conjEmb φ) a = embF c φ (IsCMField.complexConj E a) :=
      Subtype.ext (IsCMField.complexEmbedding_complexConj E φ a).symm
    show σ (embF c (conjEmb φ) a) = starRingEnd ℂ (Formalism.L2.PjFree.relab c σ φ a)
    rw [h1]
    exact IsCMField.complexEmbedding_complexConj E (Formalism.L2.PjFree.relab c σ φ) a
  have hI : (2 * Complex.I) ≠ 0 := by simp
  refine ⟨hQ, exact_of_decomp _ _
    (Matrix.of fun i k => (2 * Complex.I)⁻¹ * ∑ j, B ⟨τ, i⟩ ⟨τ, j⟩ * starRingEnd ℂ (Q (x k) ⟨τ, j⟩)) _
    (Matrix.of fun j k => -(2 * Complex.I)⁻¹ *
      ∑ i, starRingEnd ℂ (Q (x k) ⟨conjEmb τ, i⟩ * B ⟨conjEmb τ, i⟩ ⟨conjEmb τ, j⟩)) ?_ ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hx.2.2.2
  · ext k k'
    have := emb_eq hr hc Di Q B hQ hs hB (fun a => hx.2.2.1 a k k') τ
    rw [Matrix.map_apply, (eq_mul_inv_iff_mul_eq₀ hI).2 this, sub_mul, sub_eq_add_neg, Matrix.add_apply]
    congr 1
    · simp only [part, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, perMat, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · simp only [part, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, perMat, Finset.sum_mul, Finset.mul_sum,
        map_sum, map_mul, Complex.conj_conj, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem goodPer_of_basis (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) (Di : Datum H) {g : ℕ} (e : Fin g ≃ Letter Dw)
    (Q : Di.La →+ (Letter Dw → ℂ)) (P : Di.La →+ (Fin g → ℂ)) (W : Letter Dw → Fin g → ℂ)
    (hP : IsPeriod Di (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P) (hW : LinearIndependent ℂ W)
    (hsupp : ∀ z j, W z j ≠ 0 → (e j).1 = z.1) (hPQ : ∀ v, P v = ∑ z, Q v z • W z)
    {x : Idx Dw τ → Di.La} {hm : Matrix (Idx Dw τ) (Idx Dw τ) E} (hx : IsPerBasis Di x hm) : GoodPer c σ τ x hm Q := by
  obtain ⟨hlin, -, -, hspan, Hm, -, -, hEF⟩ := hP
  let T : (Letter Dw → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ W
  have hT : Function.Injective T := hW.fintypeLinearCombination_injective
  have hTQ : ∀ v, T (Q v) = P v := fun v => (hPQ v).symm
  refine goodPer_of_form c σ τ Di Q (fun z w => hermForm Hm (W z) (W w)) (fun a v => ?_) ?_ (fun x y => ?_) hx
  · refine congrFun (hT (a₂ := fun z => Formalism.L2.PjFree.relab c σ z.1 (a : E) * Q v z) ?_)
    rw [hTQ]
    funext j
    rw [hlin, hPQ]
    simp only [T, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases h0 : W z j = 0
    · simp [h0]
    · rw [hsupp z j h0, _root_.mul_assoc]
  · refine Submodule.map_injective_of_injective (f := T.restrictScalars ℝ) hT ?_
    have h1 : (Submodule.span ℝ (Set.range Q)).map (T.restrictScalars ℝ) = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp, ← hspan]
      exact congrArg (fun f => Submodule.span ℝ (Set.range f)) (funext hTQ)
    rw [h1]
    exact (top_unique (h1 ▸ Submodule.map_mono le_top)).symm
  · rw [← hEF, hPQ, hPQ]
    congr 1
    simp only [form, hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [starRingEnd_apply]; ring

theorem dirs_indep {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw} (Fu : Fam Xo c σ e) (a : CxFr Z σ) (i : Fin Fu.n)
    {P : (Fu.Di i).La →+ (Fin g → ℂ)} {W : Letter Dw → Fin g → ℂ} {y : Sp ℂ ⟶ Xo.XF c}
    (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P) (hy : y ≫ pullback.fst _ _ = Fu.u i P)
    (hj : y ≫ Z.jQ = a.1.1)
    (hW : ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
      v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
      IsDerivAt0 (fun w => (Fu.ex i P w).left) (W z) (v₀ ≫ Z.m0.toSABMap.φ)) :
    LinearIndependent ℂ W ∧ ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := by
  choose v h1 h2 h3 using hW
  have hx : y ≫ Z.jQ ≫ pullback.fst _ _ = a.1.1 ≫ genι Z := by rw [← Category.assoc, hj]
  have heig := GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e Fu i P hP
  have htan := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ Fu i P hP
  have hcomb := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ Fu i P hP
  have hsupp : ∀ z j, W z j ≠ 0 → (e j).1 = z.1 := fun z =>
    (heig (W z) _ z.1 (h3 z)).1 fun b =>
      (OpenReg.eig_iff Z.m0.toSABMap (h1 z) b _).2 ((OpenReg.eig_iff Z.m (h1 z) b _).1 (h2 z ▸ a.2.eig z.1 z.2 b))
  refine ⟨Fintype.linearIndependent_iff.2 fun f hf z => ?_, hsupp⟩
  obtain ⟨τ, k⟩ := z
  have h0 : ∑ k, f ⟨τ, k⟩ • W ⟨τ, k⟩ = 0 := by
    funext j
    by_cases hτ : (e j).1 = τ
    · have := congrFun hf j
      rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single τ (fun ψ _ hψ => Finset.sum_eq_zero fun k _ => by
        have : W ⟨ψ, k⟩ j = 0 := by_contra fun h => hψ ((hsupp _ j h).symm.trans hτ)
        simp [this]) (by simp)] at this
      rw [Finset.sum_apply]
      exact this
    · rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        have : W ⟨τ, k⟩ j = 0 := by_contra fun h => hτ (hsupp _ j h)
        simp [this]
  obtain ⟨u, hu, -⟩ := htan.2.1 0
  have hut := htan.1 0 u hu
  obtain ⟨u', hu1, rfl⟩ := OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) u
    (by rw [hut.1, ← hy, Category.assoc])
  have hb := a.2.basis τ (u' ≫ Z.m.φ) ((OpenReg.tan_iff Z.m hx hu1).2 ((OpenReg.tan_iff Z.m0.toSABMap hy hu1).1 hut))
    fun b => (OpenReg.eig_iff Z.m hu1 b _).2 ((OpenReg.eig_iff Z.m0.toSABMap hu1 b _).1
      ((heig 0 _ τ hu).2 (fun j h => (h rfl).elim) b))
  have e1 : a.2.v τ = fun k => v ⟨τ, k⟩ ≫ Z.m.φ := funext fun k => (h2 ⟨τ, k⟩).symm
  rw [e1] at hb
  have key : ∀ cf : Fin (Dw.mult τ) → ℂ, ∑ k, cf k • W ⟨τ, k⟩ = 0 →
      IsCombAtG Z.t (a.1.1 ≫ genι Z) (fun k => v ⟨τ, k⟩ ≫ Z.m.φ) cf (u' ≫ Z.m.φ) := fun cf hcf =>
    (OpenReg.comb_iff Z.m hx (fun k => h1 ⟨τ, k⟩) cf hu1).2
      ((OpenReg.comb_iff Z.m0.toSABMap hy (fun k => h1 ⟨τ, k⟩) cf hu1).1
        ((hcomb _ _ (fun k => W ⟨τ, k⟩) (fun k => h3 ⟨τ, k⟩) cf _).2 (hcf ▸ hu)))
  exact congrFun (hb.unique (key (fun k => f ⟨τ, k⟩) h0) (key 0 (by simp))) k

end GlobalTheory.ShFam.HodgeSeq

theorem GlobalTheory.ShFam.Hor.goodPer_of_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (a : CxFr Z σ) (i : Fin Fu.n) (Q : (Fu.Di i).La →+ (Letter Dw → ℂ)) (x : Idx Dw τ → (Fu.Di i).La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E), Per Fu a i Q → IsPerBasis (Fu.Di i) x hm → GoodPer c σ τ x hm Q := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu τ a i Q x hm ⟨P, W, y, hP, hy, hj, hW, hPQ⟩ hx
  have h := GlobalTheory.ShFam.HodgeSeq.dirs_indep Fu a i hP hy hj hW
  exact GlobalTheory.ShFam.HodgeSeq.goodPer_of_basis c σ τ _ e Q P W hP h.1 h.2 hPQ hx
