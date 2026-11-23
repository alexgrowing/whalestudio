import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MulVecOfRealVecAddMemSpanPeriodLattice

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.SharpObj

variable {h : ℕ}

def per (τ : Matrix (Fin h) (Fin h) ℂ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x i => τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ)
      map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
      map_add' := fun x y => by
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        ring }

theorem per_apply (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    per τ x i = τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ) := rfl

def imInv (τ : Matrix (Fin h) (Fin h) ℂ) : Matrix (Fin h) (Fin h) ℂ :=
  (τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)

theorem hermForm_real_re (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).re =
      (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).re) + (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

theorem hermForm_real_im (M : Matrix (Fin h) (Fin h) ℝ) (z w : Fin h → ℂ) :
    (hermForm (M.map fun x : ℝ => (x : ℂ)) z w).im =
      (fun i => (z i).im) ⬝ᵥ M.mulVec (fun i => (w i).re) - (fun i => (z i).re) ⬝ᵥ M.mulVec (fun i => (w i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.im_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

variable {τ : Matrix (Fin h) (Fin h) ℂ}

theorem imInv_isHermitian (hp : (τ.map Complex.im).PosDef) : (imInv τ).IsHermitian := by
  unfold imInv
  exact hp.inv.isHermitian.map _ fun x => by simp

theorem imInv_pos (hp : (τ.map Complex.im).PosDef) (z : Fin h → ℂ) (hz : z ≠ 0) :
    0 < (hermForm (imInv τ) z z).re := by
  have hN := hp.inv
  rw [imInv, hermForm_real_re]
  have key : ∀ v : Fin h → ℝ, 0 ≤ v ⬝ᵥ (τ.map Complex.im)⁻¹.mulVec v := fun v => by
    simpa using hN.posSemidef.dotProduct_mulVec_nonneg v
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := by
      intro hi
      apply hz
      funext i
      apply Complex.ext
      · simpa using congrFun hr i
      · simpa using congrFun hi i
    have := hN.dotProduct_mulVec_pos hi
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).re)]
  · have := hN.dotProduct_mulVec_pos hr
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).im)]

theorem per_eq (x : Fin h ⊕ Fin h → ℤ) :
    per τ x = τ.mulVec (ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inl i) : ℝ)) +
      ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inr i) : ℝ) := by
  funext i
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [per_apply]

private theorem re_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).re = ((τ.map Complex.re).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

private theorem im_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).im = ((τ.map Complex.im).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

private theorem re_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).re) = (τ.map Complex.re).mulVec (fun i => (x (.inl i) : ℝ)) + fun i => (x (.inr i) : ℝ) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]

private theorem im_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).im) = (τ.map Complex.im).mulVec (fun i => (x (.inl i) : ℝ)) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]

theorem im_hermForm_per (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (x y : Fin h ⊕ Fin h → ℤ) :
    (hermForm (imInv τ) (per τ x) (per τ y)).im = omegaStd x y := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have hYt : Matrix.transpose (τ.map Complex.im) = τ.map Complex.im := by
    have := hp.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hXt : Matrix.transpose (τ.map Complex.re) = τ.map Complex.re := by
    rw [← Matrix.transpose_map, hs.eq]
  rw [imInv, hermForm_real_im, re_per', im_per', re_per', im_per']
  set X := τ.map Complex.re
  set Y := τ.map Complex.im
  set a : Fin h → ℝ := fun i => (x (.inl i) : ℝ)
  set b : Fin h → ℝ := fun i => (x (.inr i) : ℝ)
  set c : Fin h → ℝ := fun i => (y (.inl i) : ℝ)
  set d : Fin h → ℝ := fun i => (y (.inr i) : ℝ)
  have e1 : Y⁻¹.mulVec (Y.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have e2 : ∀ v, (Y.mulVec a) ⬝ᵥ (Y⁻¹.mulVec v) = a ⬝ᵥ v := fun v => by
    rw [← hYt, ← Matrix.vecMul_transpose, hYt, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hYt,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have e3 : (X.mulVec a) ⬝ᵥ c = a ⬝ᵥ (X.mulVec c) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hXt, dotProduct_comm]
  rw [e1, e2, add_dotProduct, e3, dotProduct_add]
  have hω : (omegaStd x y : ℝ) = a ⬝ᵥ d - b ⬝ᵥ c := by
    simp only [omegaStd, a, b, c, d, dotProduct]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [hω]
  ring

private theorem eq_zero_of_mulVec_ofRealVec_add_eq_zero (hp : (τ.map Complex.im).PosDef) (a b : Fin h → ℝ)
    (hab : τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a) + ReciprocityTheory.PTheta.ofRealVec b = 0) : a = 0 ∧ b = 0 := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have him : (τ.map Complex.im).mulVec a = 0 := by
    funext i
    have := congrArg (fun v => (v i).im) hab
    simp only [Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec, Pi.zero_apply, Complex.zero_im] at this
    simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this
  have ha : a = 0 := by
    calc a = ((τ.map Complex.im)⁻¹ * τ.map Complex.im).mulVec a := by
          rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, him, Matrix.mulVec_zero]
  refine ⟨ha, ?_⟩
  funext i
  have := congrArg (fun v => (v i).re) hab
  simp only [Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec, ha, Matrix.mulVec_zero, Pi.zero_apply,
    Complex.zero_re, zero_add] at this
  simpa [ReciprocityTheory.PTheta.ofRealVec.eq_1] using this

theorem per_lattice (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (per τ) ∧ DiscreteTopology (LinearMap.range (per τ)) ∧
      Submodule.span ℝ (LinearMap.range (per τ) : Set (Fin h → ℂ)) = ⊤ := by
  obtain ⟨P, hP⟩ : ∃ P : (Fin h ⊕ Fin h → ℝ) →ₗ[ℝ] (Fin h → ℂ), ∀ g, P g =
      τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) + ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i)) :=
    ⟨{ toFun := fun g => τ.mulVec (ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inl i))) +
          ReciprocityTheory.PTheta.ofRealVec (fun i => g (.inr i))
       map_add' := fun g g' => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Complex.ofReal_add,
            mul_add, Finset.sum_add_distrib]
          ring
       map_smul' := fun c g => by
          funext i
          unfold ReciprocityTheory.PTheta.ofRealVec
          simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul, mul_add, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun _ _ => by ring }, fun _ => rfl⟩
  have hPinj : Function.Injective P := by
    refine (injective_iff_map_eq_zero P).2 fun g hg => ?_
    rw [hP] at hg
    obtain ⟨h1, h2⟩ := eq_zero_of_mulVec_ofRealVec_add_eq_zero hp _ _ hg
    funext j
    cases j with
    | inl i => exact congrFun h1 i
    | inr i => exact congrFun h2 i
  have hper : ∀ x, per τ x = P (fun j => (x j : ℝ)) := fun x => by rw [hP, per_eq]
  have hinj : Function.Injective (per τ) := fun x y hxy => by
    rw [hper, hper] at hxy
    funext j
    exact_mod_cast congrFun (hPinj hxy) j
  have hdim : Module.finrank ℝ (Fin h ⊕ Fin h → ℝ) = Module.finrank ℝ (Fin h → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    omega
  set e := P.linearEquivOfInjective hPinj hdim with he
  set b := (Pi.basisFun ℝ (Fin h ⊕ Fin h)).map e with hb
  have hrepr : ∀ w j, b.repr w j = e.symm w j := fun w j => by
    simp [hb, Module.Basis.map_repr]
  have hrange : LinearMap.range (per τ) = Submodule.span ℤ (Set.range b) := by
    ext w
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b w, LinearMap.mem_range]
    simp only [hrepr]
    constructor
    · rintro ⟨x, rfl⟩ j
      refine ⟨x j, ?_⟩
      have : e.symm (P fun j => (x j : ℝ)) = fun j => (x j : ℝ) := e.symm_apply_apply _
      rw [hper, this]
      simp
    · intro hw
      choose n hn using hw
      refine ⟨n, ?_⟩
      have : (fun j => (n j : ℝ)) = e.symm w := funext fun j => by simpa using hn j
      rw [hper, this]
      exact e.apply_symm_apply w
  refine ⟨hinj, ?_, ?_⟩
  · rw [hrange]
    infer_instance
  · rw [hrange, Submodule.span_span_of_tower, b.span_eq]

def turn (h : ℕ) : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) where
  toFun x := Sum.elim (fun i => -x (.inr i)) (fun i => x (.inl i))
  invFun x := Sum.elim (fun i => x (.inr i)) (fun i => -x (.inl i))
  map_add' x y := by ext (i | i) <;> simp [add_comm]
  map_smul' c x := by ext (i | i) <;> simp
  left_inv x := by ext (i | i) <;> simp
  right_inv x := by ext (i | i) <;> simp

theorem exists_form (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    ∃ Ef : LinearMap.BilinForm ℤ (LinearMap.range (per τ)),
      (∀ a b : LinearMap.range (per τ), (Ef a b : ℝ) = (hermForm (imInv τ) a b).im) ∧ Function.Bijective Ef := by
  have hinj := (per_lattice hs hp).1
  set e := LinearEquiv.ofInjective (per τ) hinj with he
  have hpe : ∀ a : LinearMap.range (per τ), per τ (e.symm a) = a := fun a => by
    rw [← LinearEquiv.ofInjective_apply (per τ) (h := hinj) (e.symm a), ← he, e.apply_symm_apply]
  obtain ⟨ω, hω⟩ : ∃ ω : LinearMap.BilinForm ℤ (Fin h ⊕ Fin h → ℤ), ∀ x y, ω x y = omegaStd x y :=
    ⟨LinearMap.mk₂ ℤ omegaStd
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring), fun _ _ => rfl⟩
  refine ⟨ω.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, fun a b => ?_, ?_, ?_⟩
  · rw [LinearMap.compl₁₂_apply, hω, ← im_hermForm_per hs hp]
    erw [hpe, hpe]
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have hx : ∀ y, omegaStd (e.symm a) y = 0 := fun y => by
      have := LinearMap.congr_fun ha (e y)
      simpa [LinearMap.compl₁₂_apply, hω] using this
    have hz : e.symm a = 0 := by
      funext j
      cases j with
      | inl i =>
        have := hx (fun k => if Sum.inr i = k then 1 else 0)
        simpa [omegaStd] using this
      | inr i =>
        have := hx (fun k => if Sum.inl i = k then 1 else 0)
        simpa [omegaStd] using this
    simpa using congrArg e hz
  · intro φ
    set ψ := φ.comp e.toLinearMap with hψ
    refine ⟨e (Sum.elim (fun i => ψ (fun k => if Sum.inr i = k then 1 else 0))
      (fun i => -ψ (fun k => if Sum.inl i = k then 1 else 0))), ?_⟩
    ext a
    obtain ⟨y, rfl⟩ := e.surjective a
    rw [LinearMap.compl₁₂_apply, hω]
    erw [e.symm_apply_apply, e.symm_apply_apply]
    have : φ (e y) = ψ y := rfl
    rw [this, LinearMap.pi_apply_eq_sum_univ ψ y, Fintype.sum_sum_type]
    simp only [omegaStd, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem form_ext {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) (hs : Submodule.span ℝ s = ⊤)
    (B : V → V → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w) (h2 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h3 : ∀ (c : ℂ) z w, B (c • z) w = c * B z w) (h4 : ∀ (c : ℝ) z w, B z ((c : ℂ) • w) = c * B z w)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : V) : B z w = 0 := by
  have hB0r : ∀ z, B z 0 = 0 := fun z => by
    have := h2 z 0 0
    simpa using this
  have hB0l : ∀ w, B 0 w = 0 := fun w => by
    have := h1 0 0 w
    simpa using this
  have step1 : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simp [hB0r]
    | add w w' _ _ ihw ihw' => rw [h2, Complex.add_im, ihw, ihw', add_zero]
    | smul c w _ ihw => rw [← Complex.coe_smul, h4, Complex.im_ofReal_mul, ihw, mul_zero]
  have step2 : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact step1 z hz w
    | zero => simp [hB0l]
    | add z z' _ _ ihz ihz' => rw [h1, Complex.add_im, ihz, ihz', add_zero]
    | smul c z _ ihz => rw [← Complex.coe_smul, h3, Complex.im_ofReal_mul, ihz, mul_zero]
  apply Complex.ext
  · have := step2 (Complex.I • z) w
    rw [h3] at this
    simpa using this
  · simpa using step2 z w

end GlobalTheory.SharpObj

end
