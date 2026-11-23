import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslateJetNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CoeffEqZeroOfOrthonormal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableFderivApply
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImFormApply

open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder

namespace GlobalTheory.ThetaTranslJet

theorem spans_pow {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (m : Ideal R)
    (J : Submodule k R) (hJ : ∀ y ∈ m, ∃ s ∈ J, y - s ∈ m ^ 2) (d : ℕ) :
    ∀ y ∈ m ^ (d + 1), ∃ A ∈ J ^ (d + 1), y - A ∈ m ^ (d + 2) := by
  induction d with
  | zero => simpa using hJ
  | succ d ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) ?_
    · obtain ⟨A, hA, hA'⟩ := ih a ha
      obtain ⟨s, hs, hs'⟩ := hJ b hb
      refine ⟨A * s, by rw [pow_succ]; exact Submodule.mul_mem_mul hA hs, ?_⟩
      have hsm : s ∈ m := by
        simpa using m.sub_mem hb (Ideal.pow_le_self two_ne_zero hs')
      have e : a * b - A * s = a * (b - s) + (a - A) * s := by ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add m (d + 1) 2]; exact Ideal.mul_mem_mul ha hs'
      · rw [pow_succ m (d + 2)]; exact Ideal.mul_mem_mul hA' hsm
    · rintro x y ⟨A, hA, hA'⟩ ⟨B, hB, hB'⟩
      refine ⟨A + B, add_mem hA hB, ?_⟩
      have e : x + y - (A + B) = (x - A) + (y - B) := by ring
      rw [e]
      exact Ideal.add_mem _ hA' hB'

noncomputable def pairing {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) :
    MvPowerSeries σ ℂ →ₗ[ℂ] ℂ :=
  ∑ m ∈ P.support, (P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ)) • MvPowerSeries.coeff m

theorem polyDeriv_eq_pairing {σ W : Type} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) :
    polyDeriv P u F 0 = pairing P (taylorDir u F) := by
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir]
  simp [pairing, LinearMap.sum_apply]

theorem pairing_eq_zero {σ : Type} [Fintype σ] (P : MvPolynomial σ ℂ) {x : MvPowerSeries σ ℂ}
    (hx : x ∈ germIdeal σ ℂ ^ (P.totalDegree + 1)) : pairing P x = 0 := by
  simp only [pairing, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun m hm => ?_
  have h1 : m.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
  rw [mem_germIdeal_pow_iff.1 hx m (by omega), smul_zero]

theorem exists_pairing_ne_zero {σ : Type} [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ x ∈ germIdeal σ ℂ ^ P.totalDegree, pairing P x ≠ 0 := by
  classical
  obtain ⟨m, hm, hd⟩ := Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.2 hP)
    (fun s => s.sum fun _ e => e)
  have hd' : P.totalDegree = m.degree := hd
  refine ⟨MvPowerSeries.monomial m 1, mem_germIdeal_pow_iff.2 fun d hd => ?_, ?_⟩
  · refine MvPowerSeries.coeff_monomial_ne (fun h => ?_) _
    subst h; omega
  · simp only [pairing, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_eq_single m (fun d _ hd => by rw [MvPowerSeries.coeff_monomial_ne hd, smul_zero])
      (fun h => absurd hm h), MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.1 hm) (cast_prod_factorial_ne_zero m)

theorem exists_prod_ne_zero {σ κ W : Type} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) (f : κ → W → ℂ) (hf : ∀ k, AnalyticAt ℂ (f k) 0) (hf0 : ∀ k, f k 0 = 0)
    (hsp : ∀ c : σ → ℂ, c ≠ 0 → ∃ k, ∑ i, c i * fderiv ℂ (f k) 0 (u i) ≠ 0)
    {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ s : Fin P.totalDegree → κ, ∀ h : W → ℂ, AnalyticAt ℂ h 0 → h 0 ≠ 0 →
      polyDeriv P u (fun z => (∏ j, f (s j) z) * h z) 0 ≠ 0 := by
  classical
  set m := germIdeal σ ℂ with hm
  have hmem : ∀ x : MvPowerSeries σ ℂ, x ∈ m ↔ MvPowerSeries.constantCoeff x = 0 := fun x => by
    rw [← pow_one m, mem_germIdeal_pow_iff]
    simp [Finsupp.degree_eq_zero_iff]
  have htm : ∀ k, taylorDir u (f k) ∈ m := fun k => by simp [hmem, hf0]
  set J := Submodule.span ℂ (Set.range fun k => taylorDir u (f k)) with hJ
  have hJm : ∀ y ∈ m, ∃ s ∈ J, y - s ∈ m ^ 2 := by
    intro y hy
    have hle : y ∈ J ⊔ (m ^ 2).restrictScalars ℂ := by
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
      have hφ' : ∀ x ∈ J ⊔ (m ^ 2).restrictScalars ℂ, φ x = 0 := fun x hx => by
        have := Submodule.mem_map_of_mem (f := φ) hx
        rwa [hφ, Submodule.mem_bot] at this
      have hform : ∀ x ∈ m, φ x =
          ∑ i, φ (MvPowerSeries.X i) * MvPowerSeries.coeff (Finsupp.single i 1) x := by
        intro x hx
        have := hφ' _ (Submodule.mem_sup_right (ThetaJet.sub_affine_mem_sq x))
        rw [map_sub, sub_eq_zero, (hmem x).1 hx] at this
        rw [this]
        simp [mul_comm]
      by_cases hc : (fun i => φ (MvPowerSeries.X i)) = 0
      · apply hφ0
        rw [hform y hy]
        simp [congrFun hc]
      · obtain ⟨k, hk⟩ := hsp _ hc
        apply hk
        have := hφ' _ (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
        rw [hform _ (htm k)] at this
        simpa only [ThetaJet.coeff_single_taylorDir u (hf k)] using this
    obtain ⟨s, hs, w, hw, e⟩ := Submodule.mem_sup.1 hle
    exact ⟨s, hs, by rw [← e, add_sub_cancel_left]; exact hw⟩
  have hex : ∃ s : Fin P.totalDegree → κ, pairing P (∏ j, taylorDir u (f (s j))) ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := exists_pairing_ne_zero hP
    obtain ⟨A, hA, hA'⟩ : ∃ A ∈ J ^ P.totalDegree, x - A ∈ m ^ (P.totalDegree + 1) := by
      generalize P.totalDegree = d at hx ⊢
      cases d with
      | zero =>
        refine ⟨MvPowerSeries.constantCoeff x • 1, Submodule.smul_mem _ _ ?_, ?_⟩
        · rw [pow_zero]; exact Submodule.one_le.1 le_rfl
        · simp [hmem]
      | succ d => exact spans_pow m J hJm d x hx
    by_contra hcon
    push Not at hcon
    have h1 := pairing_eq_zero P hA'
    rw [map_sub, sub_eq_zero] at h1
    rw [hJ, Submodule.span_pow] at hA
    refine hx0 (h1.trans ((Submodule.span_le (p := LinearMap.ker (pairing P))).2 ?_ hA))
    intro a ha
    obtain ⟨g, rfl⟩ := Set.mem_pow.1 ha
    choose s hs using fun j => (g j).2
    rw [List.prod_ofFn]
    simp only [← hs]
    exact hcon s
  obtain ⟨s, hs⟩ := hex
  refine ⟨s, fun h hh h0 => ?_⟩
  have e := taylorDir_mul u (Finset.analyticAt_fun_prod Finset.univ fun j _ => hf (s j)) hh
  rw [taylorDir_prod u _ fun j _ => hf (s j)] at e
  rw [polyDeriv_eq_pairing]
  change pairing P (taylorDir u ((fun z => ∏ j, f (s j) z) * h)) ≠ 0
  have h1 : ∏ j, taylorDir u (f (s j)) ∈ m ^ P.totalDegree := by
    simpa using Ideal.prod_mem_prod (s := Finset.univ) (I := fun _ => m) fun j _ => htm (s j)
  have h2 : taylorDir u h - h 0 • 1 ∈ m := by simp [hmem]
  have h3 := pairing_eq_zero P (x := _) (by rw [pow_succ]; exact Ideal.mul_mem_mul h1 h2)
  rw [mul_sub, map_sub, sub_eq_zero, mul_smul_comm, mul_one, map_smul] at h3
  rw [e, h3]
  exact mul_ne_zero h0 hs

theorem exists_coc {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  first
  | exact @_root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc
  | exact _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc
  | (apply _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperHalfImaginaryForm.exists_coc ..)

variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

open scoped MatrixOrder in

theorem exists_theta (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) :
    ∃ χ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 ∧ (∀ a ∈ Λ, ‖χ a‖ = 1) ∧
      ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
        Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  have hsp : Submodule.span ℝ (L : Set (Fin g → ℂ)) = ⊤ :=
    ThetaTranslSpan.span_eq_top hH Λ fun v => (hΛ v).1
  haveI : IsZLattice ℝ L := ⟨hsp⟩
  obtain ⟨B, hB, hY⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hH.isStrictlyPositive
  let Φ : (Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin g) :=
    (B.toLinearEquiv' hB.invertible).trans (WithLp.linearEquiv 2 ℂ _).symm
  have hΦ : ∀ v w, Hf (Φ v) (Φ w) = star w ⬝ᵥ Hm.mulVec v := fun v w => by
    have : Hf (Φ v) (Φ w) = star (B.mulVec w) ⬝ᵥ B.mulVec v := by
      rw [dotProduct_comm]; rfl
    rw [this, hY, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, star_eq_conjTranspose]
  let b₀ := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let b₁ := b₀.map (Φ.restrictScalars ℝ)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) =
      Fintype.card (Fin (2 * Fintype.card (Fin g))) := by
    rw [← Module.finrank_eq_card_basis b₁, finrank_real_of_complex]
    simp
  let b := b₁.reindex (Fintype.equivOfCardEq hcard)
  have hb : ∀ z, Φ z ∈ lat b ↔ z ∈ Λ := fun z => by
    change _ ↔ z ∈ L
    rw [← (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ, lat, Module.Basis.range_reindex]
    simp only [Module.Basis.mem_span_iff_repr_mem, b₁, Module.Basis.map_repr]
    simp [b₀]
  have hsk : ∀ z u : Fin g → ℂ, (star u ⬝ᵥ Hm.mulVec z).im = -(star z ⬝ᵥ Hm.mulVec u).im :=
    fun z u => by rw [ThetaTranslSpan.herm_swap hH z u]; simp
  obtain ⟨Y, hYb, hC⟩ := exists_coc b (fun x y hx hy => by
    obtain ⟨x, rfl⟩ := Φ.surjective x
    obtain ⟨y, rfl⟩ := Φ.surjective y
    rw [hΦ]
    exact (hΛ y).2 ((hb y).1 hy) x ((hb x).1 hx)) (fun φ => by
    let p : L →+ lat b := (Φ.toLinearMap.toAddMonoidHom.comp L.subtype.toAddMonoidHom).codRestrict
      (lat b) fun a => (hb _).2 a.2
    obtain ⟨y, hy⟩ := ThetaTranslSpan.exists_im_eq_lattice hH L hsp
      (-((Int.castAddHom ℝ).comp (φ.comp p)).toIntLinearMap)
    refine ⟨Φ y, (hb y).2 ((hΛ y).1 fun a ha => ⟨-φ (p ⟨a, ha⟩), by rw [hy ⟨a, ha⟩]; simp⟩), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Φ.surjective x
    rw [hΦ, hsk, hy ⟨x, (hb x).1 hx⟩]
    simp only [LinearMap.neg_apply, neg_neg]
    rfl)
  obtain ⟨s, ⟨hs, hs'⟩, hs0⟩ := ThetaExist.exists_sec_ne_zero Y hC
  refine ⟨fun a => Y.ka (Φ a), fun z => s (Φ z),
    hs.comp Φ.toContinuousLinearEquiv.differentiable, fun h => hs0 ?_,
    fun a ha => Y.ka_abs _ (hYb ▸ (hb a).2 ha), fun a ha z => ?_⟩
  · funext x
    obtain ⟨x, rfl⟩ := Φ.surjective x
    exact congrFun h x
  · simp only [map_add]
    rw [hs' _ (hYb ▸ (hb a).2 ha), hΦ, hΦ]
    congr 3
    push_cast; ring

theorem differentiable_herm (a : Fin g → ℂ) :
    Differentiable ℂ fun z : Fin g → ℂ => star a ⬝ᵥ Hm.mulVec z := by
  simp only [dotProduct, mulVec]
  fun_prop

theorem mult_add {Λ : AddSubgroup (Fin g → ℂ)} {χ θ : (Fin g → ℂ) → ℂ} {z₀ : Fin g → ℂ}
    (h0 : θ z₀ ≠ 0)
    (hθ : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) {a b : Fin g → ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    χ (a + b) = χ a * χ b *
      Complex.exp (Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec b - star b ⬝ᵥ Hm.mulVec a)) := by
  have e1 := hθ _ (Λ.add_mem ha hb) z₀
  rw [show z₀ + (a + b) = z₀ + b + a by abel, hθ a ha, hθ b hb, ← mul_assoc] at e1
  have e2 := mul_right_cancel₀ h0 e1
  refine mul_right_cancel₀ (Complex.exp_ne_zero _) (e2.symm.trans ?_)
  rw [mul_mul_mul_comm, mul_assoc (χ a * χ b), ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem exists_two_points {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (T : Fin g → ℂ) {p : ℕ} (hp : p ≠ 0) : ∃ c, θ c ≠ 0 ∧ θ (T - p • c) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have hd : Differentiable ℂ fun c : Fin g → ℂ => θ (T - p • c) :=
    hθ.comp ((differentiable_const T).sub (differentiable_id.const_smul p))
  have han : AnalyticOnNhd ℂ (fun c : Fin g → ℂ => θ (T - p • c)) Set.univ :=
    fun x _ => ThetaJet.analyticAt_of_differentiable hd x
  have h := han.eq_of_eventuallyEq (g := 0) (z₀ := x) analyticOnNhd_const (by
    filter_upwards [(isOpen_ne_fun hθ.continuous continuous_const).mem_nhds hx] with y hy
    exact hcon y hy)
  have h2 := congrFun h ((p : ℂ)⁻¹ • (T - x))
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hp), sub_sub_cancel] at h2
  exact hx h2

theorem exists_completion {Λ : AddSubgroup (Fin g → ℂ)} {χ θ : (Fin g → ℂ) → ℂ}
    (hd : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (hθ : ∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
      Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) (M : ℕ) (S : Fin g → ℂ) {κ : Type}
    (t : Finset κ) (x : κ → Fin g → ℂ) (ht : t.card + 2 ≤ M) :
    ∃ h : (Fin g → ℂ) → ℂ, Differentiable ℂ h ∧ h 0 ≠ 0 ∧ ∀ a ∈ Λ, ∀ z,
      (∏ j ∈ t, θ (z + a + x j)) * h (z + a) = χ a ^ M *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec S - star S ⬝ᵥ Hm.mulVec a)) *
        Complex.exp (M * (Real.pi * (star a ⬝ᵥ Hm.mulVec z) +
          Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a))) * ((∏ j ∈ t, θ (z + x j)) * h z) := by
  obtain ⟨p, rfl⟩ : ∃ p, M = t.card + (p + 1) + 1 := ⟨M - t.card - 2, by omega⟩
  obtain ⟨c, hc, hc'⟩ := exists_two_points hd h0 (S - ∑ j ∈ t, x j) (p := p + 1) (by omega)
  set c' := S - ∑ j ∈ t, x j - (p + 1) • c with hc'def
  have hS : S = ∑ j ∈ t, x j + (p + 1) • c + c' := by rw [hc'def]; abel
  refine ⟨fun z => Complex.exp (-(Real.pi * (star S ⬝ᵥ Hm.mulVec z))) *
    (θ (z + c) ^ (p + 1) * θ (z + c')), ?_, by simp [hc, hc'], fun a ha z => ?_⟩
  · exact ((differentiable_herm S).const_mul _).neg.cexp.mul
      (((hd.comp (differentiable_id.add_const c)).pow _).mul
        (hd.comp (differentiable_id.add_const c')))
  · set j : ℂ := Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a) with hj
    have h1 : ∀ y, θ (z + a + y) = χ a * Complex.exp j *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec y)) * θ (z + y) := fun y => by
      rw [add_right_comm, hθ a ha, mul_assoc (χ a) (Complex.exp j), ← Complex.exp_add, hj, mulVec_add,
        dotProduct_add]
      congr 3
      ring
    have h2 : Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec S)) =
        (∏ i ∈ t, Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec (x i)))) *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec c)) ^ (p + 1) *
        Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec c')) := by
      rw [← Complex.exp_sum, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      conv_lhs => rw [hS]
      rw [mulVec_add, mulVec_add, dotProduct_add, dotProduct_add, mulVec_sum, dotProduct_sum,
        mulVec_smul, dotProduct_smul, ← Finset.mul_sum, nsmul_eq_mul]
      ring
    clear_value j
    simp only [h1, Finset.prod_mul_distrib, Finset.prod_const]
    rw [mul_sub, sub_eq_add_neg, Complex.exp_add, h2, Complex.exp_nat_mul, mulVec_add,
      dotProduct_add, mul_add, neg_add, Complex.exp_add]
    ring

theorem exists_mem_ne_zero {σ V : Type} [Fintype σ] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} (P : MvPolynomial σ ℂ) (u : σ → Fin n → V) (T : Set (V → ℂ))
    (hT : ∀ G ∈ T, Differentiable ℂ G) (F : Fin n → V → ℂ) (hF : ∀ b, F b ∈ Submodule.span ℂ T)
    (h : polyDeriv P u (fun z => ∏ b, F b (z b)) 0 ≠ 0) :
    ∃ G : Fin n → V → ℂ, (∀ b, G b ∈ T) ∧ polyDeriv P u (fun z => ∏ b, G b (z b)) 0 ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  choose N c G hG using fun b => Submodule.mem_span_set'.1 (hF b)
  have e : (fun z : Fin n → V => ∏ b, F b (z b)) = fun z => ∑ p : ∀ b, Fin (N b),
      ((∏ b, c b (p b)) • fun z : Fin n → V => ∏ b, (G b (p b) : V → ℂ) (z b)) z := by
    funext z
    simp only [← hG, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have han : ∀ p : ∀ b, Fin (N b),
      AnalyticAt ℂ (fun z : Fin n → V => ∏ b, (G b (p b) : V → ℂ) (z b)) 0 := fun p =>
    Finset.analyticAt_fun_prod _ fun b _ => ThetaJet.analyticAt_of_differentiable
      ((hT _ (G b (p b)).2).comp (differentiable_apply b)) 0
  rw [e, polyDeriv_eq_pairing, taylorDir_sum u _ fun p _ => (han p).const_smul, map_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [taylorDir_smul u _ (han p), map_smul, ← polyDeriv_eq_pairing,
    hcon (fun b => G b (p b)) fun b => (G b (p b)).2, smul_zero]

theorem exists_translates_jet_ne_zero : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ (M : ℕ) (Λ₁ : AddSubgroup (Fin g → ℂ)), Λ₁ ≤ Λ → (∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = M * k) ↔ v ∈ Λ₁) → ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin g) ℂ), P ≠ 0 → P.totalDegree + 2 ≤ M → ∃ y : Fin n → Fin g → ℂ, (∀ b, (M : ℂ) • y b ∈ Λ₁) ∧ ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun q => (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ)) (fun z : Fin n → Fin g → ℂ => ∏ b, Complex.exp (-(Real.pi * (star (y b) ⬝ᵥ Hm.mulVec (z b)))) * θ (z b + y b)) 0 ≠ 0 := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ hle hΛ₁ n P hP hM
  classical
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hM0' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI hd₁ : DiscreteTopology Λ₁ := DiscreteTopology.of_subset (s := (Λ : Set (Fin g → ℂ))) hd hle
  set H' : Matrix (Fin g) (Fin g) ℂ := (M : ℝ)⁻¹ • Hm with hH'def
  have hH' : H'.PosDef := hH.smul (inv_pos.2 (Nat.cast_pos.2 (by omega)))
  have hHH : ∀ v w : Fin g → ℂ, star v ⬝ᵥ Hm.mulVec w = M * (star v ⬝ᵥ H'.mulVec w) := fun v w => by
    rw [hH'def, smul_mulVec, dotProduct_smul, Complex.real_smul]
    push_cast
    field_simp
  have hΛ' : ∀ v, (∀ a ∈ Λ₁, ∃ k : ℤ, (star v ⬝ᵥ H'.mulVec a).im = k) ↔ v ∈ Λ₁ := fun v => by
    rw [← hΛ₁]
    simp only [hHH, ← Complex.ofReal_natCast, Complex.im_ofReal_mul, mul_right_inj' hM0']
  obtain ⟨χ₁, θ₁, hθ₁, h0₁, hχ₁, hθt₁⟩ := exists_theta hH' Λ₁ hΛ'
  have hχ₁0 : ∀ a ∈ Λ₁, χ₁ a ≠ 0 := fun a ha h => by simpa [h] using hχ₁ a ha
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  obtain ⟨z₁, hz₁⟩ := Function.ne_iff.1 h0₁
  have hadd : ∀ a b : Λ₁, χ (a + b) / χ₁ (a + b) ^ M = χ a / χ₁ a ^ M * (χ b / χ₁ b ^ M) := by
    intro a b
    rw [mult_add hz₀ hθt (hle a.2) (hle b.2), mult_add hz₁ hθt₁ a.2 b.2, mul_pow, mul_pow,
      ← Complex.exp_nat_mul, hHH, hHH, ← mul_sub, mul_left_comm (M : ℂ),
      mul_div_mul_right _ _ (Complex.exp_ne_zero _), div_mul_div_comm]
  have hψ : ∀ a : Λ₁, ‖χ a / χ₁ a ^ M‖ = 1 := fun a => by
    rw [norm_div, norm_pow, hχ _ (hle a.2), hχ₁ _ a.2, one_pow, div_one]
  let ψ : AddChar Λ₁ ℂ :=
    { toFun := fun a => χ a / χ₁ a ^ M
      map_zero_eq_one' := by
        have h := hadd 0 0
        have h1 : χ (0 : Λ₁) / χ₁ (0 : Λ₁) ^ M ≠ 0 := fun h => by
          have := hψ 0
          rw [h, norm_zero] at this
          exact zero_ne_one this
        rw [← AddSubgroup.coe_add, add_zero] at h
        exact (mul_eq_left₀ h1).1 h.symm
      map_add_eq_mul' := hadd }
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ₁
  haveI hL : DiscreteTopology L := hd₁
  haveI : Module.Free ℤ Λ₁ := (inferInstance : Module.Free ℤ L)
  obtain ⟨φ, hφ⟩ := ThetaTranslSpan.exists_log_addChar ψ hψ
  obtain ⟨S, hS⟩ := ThetaTranslSpan.exists_im_eq_lattice hH' L
    (ThetaTranslSpan.span_eq_top hH' Λ₁ fun v => (hΛ' v).1) (-φ)
  have hSχ : ∀ a ∈ Λ₁, χ₁ a ^ M *
      Complex.exp (Real.pi * (star a ⬝ᵥ H'.mulVec S - star S ⬝ᵥ H'.mulVec a)) = χ a := by
    intro a ha
    have e1 : (star S ⬝ᵥ H'.mulVec a).im = -φ ⟨a, ha⟩ := hS ⟨a, ha⟩
    have e2 : χ a / χ₁ a ^ M = _ := hφ ⟨a, ha⟩
    rw [div_eq_iff (pow_ne_zero _ (hχ₁0 a ha))] at e2
    rw [e2, mul_comm, ← neg_sub, ThetaTranslSpan.herm_swap hH' S a, Complex.star_def,
      Complex.sub_conj, e1]
    congr 2
    push_cast
    ring
  have hdf : ∀ (b : Fin n) (a : Fin g → ℂ),
      Differentiable ℂ fun z : Fin n → Fin g → ℂ => θ₁ (z b + a) := fun b a =>
    hθ₁.comp ((differentiable_apply b).add_const a)
  obtain ⟨s, hs⟩ := exists_prod_ne_zero (κ := Fin n × {a // θ₁ a = 0})
    (fun q : Fin n × Fin g =>
      (Pi.single q.1 (Pi.single q.2 (1 : ℂ) : Fin g → ℂ) : Fin n → Fin g → ℂ))
    (fun k z => θ₁ (z k.1 + k.2)) (fun k => ThetaJet.analyticAt_of_differentiable (hdf _ _) 0)
    (fun k => by simpa using k.2.2) (fun c hc => by
      obtain ⟨⟨b, i⟩, hb⟩ := Function.ne_iff.1 hc
      obtain ⟨a, ha, ha'⟩ := GlobalTheory.ThetaGauss.exists_zero_fderiv_ne_zero g H' hH' Λ₁ hd₁ hΛ' χ₁ θ₁ hθ₁ h0₁ hχ₁ hθt₁
        (fun i => c (b, i)) (Function.ne_iff.2 ⟨i, hb⟩)
      refine ⟨(b, ⟨a, ha⟩), ?_⟩
      have h1 : HasFDerivAt (fun z : Fin n → Fin g → ℂ => θ₁ (z b + a))
          ((fderiv ℂ θ₁ a).comp (ContinuousLinearMap.proj b)) 0 := by
        refine HasFDerivAt.comp (f := fun z : Fin n → Fin g → ℂ => z b + a) 0 ?_
          ((hasFDerivAt_apply b 0).add_const a)
        simpa using (hθ₁ a).hasFDerivAt
      rw [h1.fderiv]
      simp only [← smul_eq_mul, ← map_smul, ← map_sum, ContinuousLinearMap.comp_apply]
      convert ha' using 2
      funext i'
      simp [Fintype.sum_prod_type, Pi.single_apply, ite_apply]) hP
  choose h hh hh0 hht using fun b : Fin n => exists_completion hθ₁ h0₁ hθt₁ M S
    (Finset.univ.filter fun j => (s j).1 = b) (fun j => ((s j).2 : Fin g → ℂ))
    (by have := Finset.card_filter_le Finset.univ fun j => (s j).1 = b
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega)
  have hne := hs (fun z => ∏ b, h b (z b)) (Finset.analyticAt_fun_prod _ fun b _ =>
    ThetaJet.analyticAt_of_differentiable ((hh b).comp (differentiable_apply b)) 0)
    (Finset.prod_ne_zero_iff.2 fun b _ => hh0 b)
  obtain ⟨G, hG, hG0⟩ := exists_mem_ne_zero P _ _ (by
      rintro _ ⟨y, -, rfl⟩
      exact ((differentiable_herm y).const_mul _).neg.cexp.mul
        (hθ.comp (differentiable_id.add_const y)))
    (fun b z => (∏ j ∈ Finset.univ.filter fun j => (s j).1 = b, θ₁ (z + (s j).2)) * h b z)
    (fun b => ThetaTranslSpan.mem_span_translates g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt M Λ₁ (by omega)
      hle hΛ₁ _ (Differentiable.mul (fun z => (HasFDerivAt.finsetProd fun j _ =>
        ((hθ₁.comp (differentiable_id.add_const _)) z).hasFDerivAt).differentiableAt) (hh b))
      fun a ha z => by
        rw [hht b a ha z, hSχ a ha, hHH, hHH]
        congr 3
        ring)
    (by
      refine ne_of_eq_of_ne (congrArg (fun F => polyDeriv P _ F 0) (funext fun z => ?_)) hne
      rw [Finset.prod_mul_distrib, ← Finset.prod_fiberwise Finset.univ (fun j => (s j).1)]
      congr 1
      refine Finset.prod_congr rfl fun b _ => Finset.prod_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.1 hj).2])
  choose y hy hy' using hG
  refine ⟨y, hy, ?_⟩
  simpa only [hy'] using hG0

end GlobalTheory.ThetaTranslJet
