import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex

def sesq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm Hm)
    (fun _ _ _ => by simp [hermForm]) (fun _ _ _ => by simp [hermForm])
    (fun _ _ _ => by simp [hermForm, Matrix.mulVec_add]) (fun _ _ _ => by simp [hermForm, Matrix.mulVec_smul])

theorem sesq_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq Hm z w = hermForm Hm z w := rfl

theorem sesq_conj {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    starRingEnd ℂ (sesq Hm z w) = sesq Hm w z := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  simp only [sesq_apply, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem sesq_of {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ) (z w : Fin n → ℂ) :
    hermForm (Matrix.of fun i j => S (Pi.single i 1) (Pi.single j 1)) z w = S z w := by
  conv_rhs => rw [pi_eq_sum_univ' z, pi_eq_sum_univ' w]
  simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

def imForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).im) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

@[simp] theorem imForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : imForm S x y = (S x y).im := rfl

def reForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).re) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

@[simp] theorem reForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : reForm S x y = (S x y).re := rfl

theorem sesq_ext {ι : Type} {v : ι → W} (hv : Submodule.span ℝ (Set.range v) = ⊤) {S S' : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ}
    (h : ∀ i k, (S (v i) (v k)).im = (S' (v i) (v k)).im) (x y : W) : S x y = S' x y := by
  have h1 : imForm S = imForm S' := LinearMap.ext_on_range hv fun i => LinearMap.ext_on_range hv fun k => h i k
  have h2 : ∀ x y, (S x y).im = (S' x y).im := fun x y => congr($h1 x y)
  exact Complex.ext (by simpa using h2 (I • x) y) (h2 x y)

variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}

theorem exists_imPart [FiniteDimensional ℝ W] (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) :
    ∃ b : W →ₗ[ℝ] W, (∀ w, b w ∈ R) ∧ ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im := by
  have hnd : ((reForm S).restrict R).Nondegenerate := by
    constructor
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
  refine ⟨R.subtype ∘ₗ (LinearMap.BilinForm.toDual _ hnd).symm.toLinearMap ∘ₗ (imForm S).domRestrict₂ R,
    fun w => Subtype.property _, fun w r hr => Complex.ext ?_ ?_⟩
  · exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) ((imForm S).domRestrict₂ R w) ⟨r, hr⟩
  · exact hR _ (Subtype.property _) r hr

section

variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)

omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' in

theorem imPart_eq {w c : W} (hc : c ∈ R) (h : ∀ r ∈ R, (S c r).re = (S w r).im) : b w = c := by
  by_contra hne
  have h1 := hpos _ (sub_ne_zero.2 hne)
  have h2 := R.sub_mem (hb w) hc
  rw [map_sub S, LinearMap.sub_apply, hb' w _ h2, Complex.sub_re, h _ h2] at h1
  simp at h1

omit [IsScalarTower ℝ ℂ W] in
include hconj hb' in

theorem apply_imPart (w : W) {r : W} (hr : r ∈ R) : S r (b w) = (S w r).im := by
  rw [← hconj, hb' w r hr, Complex.conj_ofReal]

variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)

omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' hρ hρR in

theorem imPart_act (a : O) (w : W) : b (ρ a w) = ρ a (b w) :=
  imPart_eq hpos hb hb' (hρR _ _ (hb w)) fun r hr => by
    rw [hρ, hρ, hb' _ _ (hρR _ _ hr), Complex.ofReal_re]

include hpos hb hb' hρ hρR in

theorem exists_compl [FiniteDimensional ℂ W] (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (n : ℕ) (q : W →ₗ[ℂ] (Fin n → ℂ)) (j : (Fin n → ℂ) →ₗ[ℂ] W) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧
      (∀ z, q (j z) = z) ∧ (∀ z, ∀ r ∈ R, S (j z) r = 0) ∧ (∀ w, w = b (I • w) + I • b w + j (q w)) ∧
      (∀ w, (∀ r ∈ R, S w r = 0) → j (q w) = w) ∧ ∀ a z, j (F a z) = ρ a (j z) := by
  let U : Submodule ℂ W :=
    { carrier := {u | ∀ r ∈ R, S u r = 0}
      zero_mem' := fun r _ => by simp
      add_mem' := fun {u u'} hu hu' r hr => by simp [hu r hr, hu' r hr]
      smul_mem' := fun c u hu r hr => by simp [hu r hr] }
  have hII : ∀ w : W, I • I • w = -w := fun w => by rw [smul_smul, I_mul_I, neg_smul, one_smul]
  have hsm : ∀ (c : ℂ) (w : W), c • w = c.re • w + c.im • I • w := fun c w => by
    rw [← algebraMap_smul ℂ c.re, ← algebraMap_smul ℂ c.im, smul_smul, ← add_smul]
    congr 1
    exact (re_add_im c).symm
  let p₀ : W →ₗ[ℝ] W := LinearMap.id - b ∘ₗ (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ -
    (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ ∘ₗ b
  have hp₀ : ∀ w, p₀ w = w - b (I • w) - I • b w := fun _ => rfl
  have hpI : ∀ w, p₀ (I • w) = I • p₀ w := fun w => by
    simp only [hp₀, hII, smul_sub, map_neg]; abel
  have hpU : ∀ w, p₀ w ∈ U := fun w r hr => by
    simp only [hp₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hb' _ r hr, smul_eq_mul]
    apply Complex.ext <;> simp
  let p : W →ₗ[ℂ] U :=
    { toFun := fun w => ⟨p₀ w, hpU w⟩
      map_add' := fun w w' => Subtype.ext (map_add p₀ w w')
      map_smul' := fun c w => Subtype.ext (by
        show p₀ (c • w) = c • p₀ w
        rw [hsm c w, hsm c (p₀ w), map_add, map_smul, map_smul, hpI]) }
  have hb0 : ∀ u ∈ U, b u = 0 := fun u hu => imPart_eq hpos hb hb' R.zero_mem fun r hr => by simp [hu r hr]
  have hpu : ∀ u : U, p u = u := fun u => Subtype.ext (by
    show p₀ u = u
    rw [hp₀, hb0 _ u.2, hb0 _ (U.smul_mem _ u.2), smul_zero, sub_zero, sub_zero])
  have hρU : ∀ a, ∀ u ∈ U, ρ a u ∈ U := fun a u hu r hr => by rw [hρ]; exact hu _ (hρR _ _ hr)
  let σ : O →+* Module.End ℂ U :=
    { toFun := fun a => (ρ a).restrict (hρU a)
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  obtain ⟨n, k, F, hF, hk⟩ := hQ U σ
  refine ⟨n, k.toLinearMap ∘ₗ p, U.subtype ∘ₗ k.symm.toLinearMap, F, hF, fun z => ?_, fun z => (k.symm z).2,
    fun w => ?_, fun w hw => ?_, fun a z => ?_⟩
  · simp [hpu]
  · have : (U.subtype ∘ₗ k.symm.toLinearMap) ((k.toLinearMap ∘ₗ p) w) = p₀ w := by simp [p]
    rw [this, hp₀]; abel
  · have := hpu ⟨w, hw⟩
    simp only at this
    simp [this]
  · obtain ⟨u, rfl⟩ := k.surjective z
    rw [← hk]
    simp [σ]

omit [IsScalarTower ℝ ℂ W] in
include hconj hR hb in

theorem sub_swap {w w' u u' : W} (hu : ∀ r ∈ R, S u r = 0) (hu' : ∀ r ∈ R, S u' r = 0)
    (h : w = b (I • w) + I • b w + u) (h' : w' = b (I • w') + I • b w' + u') :
    S w (b w') - S u u' / (2 * I) = S w' (b w) - S u' u / (2 * I) - (S w w').im := by
  have hv : ∀ r ∈ R, S r u' = 0 := fun r hr => by rw [← hconj, hu' r hr, map_zero]
  have hre : ∀ z z', (S z z').re = (S z' z).re := fun z z' => by rw [← hconj z z', conj_re]
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  generalize b (I • w) = a, hb (I • w) = ha at h
  generalize b (I • w') = a', hb (I • w') = ha' at h'
  generalize b w = c, hb w = hc at h ⊢
  generalize b w' = c', hb w' = hc' at h' ⊢
  subst h h'
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu _ ha', hu _ hc',
    hu' _ hc, hv _ ha, hv _ hc, AnArc.div_two_I]
  apply Complex.ext <;>
    simp [hR _ ha _ ha', hR _ ha _ hc', hR _ hc _ ha', hR _ hc _ hc', hR _ ha' _ hc, hR _ hc' _ hc, hre a' c, hre c' c,
      hre u' u, him u' u]
  ring

end

open NumberField in

theorem exists_diag {E : Type} [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : 𝓞 E →+* Module.End ℂ U) :
    ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : 𝓞 E →+* Module.End ℂ (Fin n → ℂ)),
      (∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) ∧ ∀ a u, k (σ a u) = F a (k u) := by
  classical
  let T₀ : Set U := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, σ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ T₀ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) σ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) σ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ T₀
  let b : Module.Basis T ℂ U := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Finite T := Module.Finite.finite_basis b
  have : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, σ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  let e := Fintype.equivFin T
  obtain ⟨k, hk⟩ := PeriodNonempty.exists_diag σ (fun i => s (e.symm i)) fun a => by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, e.symm.sum_comp fun v => s v (a : E)]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb]
  refine ⟨_, k, k.conjRingEquiv.toRingHom.comp σ, ⟨fun i => s (e.symm i), fun a z i => ?_⟩, fun a u => ?_⟩
  · obtain ⟨u, rfl⟩ := k.surjective z
    simpa using hk a u i
  · simp

section Hom

variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

theorem finrank_hom_complex : Module.finrank ℂ (Y →+ ℂ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self, mul_one]

theorem finrank_hom_int : Module.finrank ℤ (Y →+ ℤ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).finrank_eq]
  simp [Module.finrank_linearMap]

theorem span_intHom :
    Submodule.span ℂ (Set.range fun n : Y →+ ℤ => (Int.castAddHom ℂ).comp n) = ⊤ := by
  refine eq_top_iff.2 fun l _ => ?_
  let b := Module.Free.chooseBasis ℤ Y
  have : l = ∑ i, l (b i) • (Int.castAddHom ℂ).comp (b.coord i).toAddMonoidHom := by
    ext x
    conv_lhs => rw [← b.sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Hom

theorem zsmul_mem_Lam {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℤ) (z : Fin A.gB → ℂ)
    (h : ∀ l : A.abelian₂, ∃ n : ℤ, k * (A.H l z).im = n) : k • z ∈ A.abelian₂ := by
  choose n hn using h
  let φ : A.abelian₂ →+ ℤ := AddMonoidHom.mk' (fun l => -n l) fun l l' => by
    have : ((n (l + l') : ℤ) : ℝ) = n l + n l' := by
      rw [← hn, ← hn, ← hn, Submodule.coe_add, A.H_add_left, add_im, mul_add]
    have : n (l + l') = n l + n l' := by exact_mod_cast this
    simp only [this]; ring
  obtain ⟨l₀, hl₀⟩ := A.Ef_bij.2 φ.toIntLinearMap
  have h1 : ∀ l : A.abelian₂, imForm (sesq A.Hm) (l₀ - k • z) l = 0 := fun l => by
    have h2 : (A.Ef l₀ l : ℝ) = -n l := by rw [hl₀]; simp [φ]
    rw [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    change (A.H l₀ l).im - k • (A.H z l).im = 0
    rw [← A.Ef_eq_im, h2, ← hn, A.H_im_symm z l]
    simp
  have h3 : imForm (sesq A.Hm) (l₀ - k • z) = 0 := LinearMap.ext_on A.full fun l hl => h1 ⟨l, hl⟩
  have h4 : (l₀ : Fin A.gB → ℂ) - k • z = 0 := by
    by_contra hne
    have h5 := A.H_pos hne
    have h6 : (A.H (l₀ - k • z) (I • (l₀ - k • z))).im = 0 := congr($h3 (I • (l₀ - k • z)))
    rw [A.H_smul_right] at h6
    generalize A.H (l₀ - k • z) (l₀ - k • z) = c at h5 h6
    simp at h6
    linarith
  rw [← sub_eq_zero.1 h4]
  exact l₀.2

end GlobalTheory.OfPeriod
