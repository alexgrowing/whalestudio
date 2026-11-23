import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOperators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open scoped nonZeroDivisors

namespace GlobalTheory

namespace ThickPoint

section Abstract

variable {W : Type} [AddCommGroup W] [Module ℝ W]

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {W : Type} [AddCommGroup W] [Module ℝ W] in

theorem _root_.GlobalTheory.ThickPoint.exists_euclidean_real {M : ℕ} [FiniteDimensional ℝ W] (hM : finrank ℝ W = M)
    (B : LinearMap.BilinForm ℝ W) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) :
    ∃ φ : W →ₗ[ℝ] EuclideanSpace ℝ (Fin M), ∀ x y, inner ℝ (φ x) (φ y) = B x y := by
  subst hM
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hs)
  let L : W →ₗ[ℝ] (Fin (finrank ℝ W) → ℝ) :=
    LinearMap.pi fun i => √(B (v i) (v i)) • v.coord i
  refine ⟨(EuclideanSpace.equiv (Fin _) ℝ).symm.toLinearEquiv.toLinearMap ∘ₗ L, fun x y => ?_⟩
  have hB : B x y = ∑ i, v.repr x i * v.repr y i * B (v i) (v i) := by
    conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [hv hj]; ring) (by simp)]
    ring
  rw [hB]
  simp [L, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (v.repr x i * v.repr y i) * Real.mul_self_sqrt (hp (v i))

variable {V : Type} [AddCommGroup V] [Module ℚ V]

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {W : Type} [AddCommGroup W] [Module ℝ W] in
variable {V : Type} [AddCommGroup V] [Module ℚ V] in

theorem _root_.GlobalTheory.ThickPoint.transference_pair {M : ℕ} (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (φ ψ : V →+ EuclideanSpace ℝ (Fin M)) (hφ : ∀ x y, inner ℝ (φ x) (ψ y) = (B x y : ℝ))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ ‖ψ u‖ ^ 2) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, ‖φ (v i)‖ ^ 2 ≤ ((M : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set d := B.dualBasis hn b with hd
  have hpair : ∀ i j, inner ℝ (φ (b i)) (ψ (d j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hφ, hd, LinearMap.BilinForm.apply_dualBasis_right hn hs]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ (fun j => ψ (d j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun z => inner ℝ (φ (b i)) z) hg
    simpa [inner_sum, inner_smul_right, hpair] using h
  let c : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hc : ∀ j, c j = ψ (d j) := fun j => by simp [c]
  have hlat : ∀ x ∈ span ℤ (Set.range c), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨m, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    set u : V := ∑ j, m j • d j with hu
    have hψu : ψ u = ∑ j, m j • c j := by simp [hu, map_sum, map_zsmul, hc]
    have hu0 : u ≠ 0 := fun h => hx0 (by rw [← hψu, h, map_zero])
    have hint : ∀ j, ∃ k : ℤ, B u (b j) = k := fun j => ⟨m j, by
      simp [hu, map_sum, map_zsmul, LinearMap.sum_apply, hd,
        LinearMap.BilinForm.apply_dualBasis_left]⟩
    have h := hmin u hu0 hint
    rw [hψu] at h
    nlinarith [norm_nonneg (∑ j, m j • c j)]
  obtain ⟨y, hyli, hyint, hyle⟩ := _root_.ReciprocityTheory.ChartRestriction.G.T0.transference_dual c lam hlam hlat
  choose m hm using hyint
  have hφv : ∀ i, φ (∑ j, m i j • b j) = y i := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis c fun j => ?_
    rw [hm i j, hc j, map_sum, sum_inner]
    simp [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hpair]
  refine ⟨fun i => ∑ j, m i j • b j, fun i => ?_, ?_, fun i => ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : ∑ j, (g j : ℝ) • y j = 0 := by
      rw [← map_zero φ, ← hg, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hφv j, ← map_ratCast_smul φ ℚ ℝ (g j)]
      simp
    exact_mod_cast (Fintype.linearIndependent_iff.mp hyli) _ h1 i
  · rw [hφv]
    exact pow_le_pow_left₀ (norm_nonneg _) (hyle i) 2

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def traceFormOf (G : Matrix (Fin r) (Fin r) E) : LinearMap.BilinForm ℚ (Fin r → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (herm G x y))
    (fun x x' y => by rw [HermitianTraceFormVanishing.herm_add_left, map_add])
    (fun c x y => by
      rw [← map_smul, ← algebraMap_smul E c x, HermitianTraceFormVanishing.herm_smul_left, Algebra.smul_def])
    (fun x y y' => by simp [herm, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul, ← algebraMap_smul E c y, HermitianTraceFormVanishing.herm_smul_right, Algebra.smul_def]
      simp [cc])

theorem traceFormOf_apply (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    traceFormOf G x y = Algebra.trace ℚ E (herm G x y) := rfl

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma herm_swap_eq_cc_herm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a)
    (x y : Fin r → E) : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G y x = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) := by
  have hc : ∀ z : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = IsCMField.complexConj E z := fun _ => rfl
  have hcc : ∀ z : E, IsCMField.complexConj E (IsCMField.complexConj E z) = z := fun z => by
    simpa [hc] using _root_.GlobalTheory.TraceDualMin.cc_cc z
  simp only [hc] at hG
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hc, map_sum, map_mul, hcc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThickPoint.traceFormOf_isSymm {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) :
    (_root_.GlobalTheory.ThickPoint.traceFormOf G).IsSymm := by
  refine LinearMap.BilinForm.isSymm_iff.mpr ⟨fun x y => ?_⟩
  rw [RingHom.id_apply, _root_.GlobalTheory.ThickPoint.traceFormOf_apply, _root_.GlobalTheory.ThickPoint.traceFormOf_apply,
    herm_swap_eq_cc_herm hG x y, _root_.GlobalTheory.TraceDualMin.trace_cc]

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThickPoint.traceFormOf_nondegenerate {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a)
    (hdet : G.det ≠ 0) : (_root_.GlobalTheory.ThickPoint.traceFormOf G).Nondegenerate := by
  refine (LinearMap.BilinForm.isSymm_iff.mp
    (_root_.GlobalTheory.ThickPoint.traceFormOf_isSymm hG)).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  have h1 : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y = 0 := by
    intro y
    refine (traceForm_nondegenerate ℚ E).1 _ fun c => ?_
    have h := hx (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc c • y)
    rw [_root_.GlobalTheory.ThickPoint.traceFormOf_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, _root_.GlobalTheory.TraceDualMin.cc_cc] at h
    rw [Algebra.traceForm_apply, mul_comm]
    exact h
  have h2 : Matrix.vecMul x G = 0 := by
    funext b
    have hs : ∀ j, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((Pi.single b (1 : E) : Fin r → E) j) =
        (Pi.single b (1 : E) : Fin r → E) j := fun j => by
      by_cases hj : j = b <;> simp [hj, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply]
    have h := h1 (Pi.single b 1)
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hs] at h
    simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using h
  exact Matrix.eq_zero_of_vecMul_eq_zero hdet h2

theorem discr_smul_mem (X : DataX E r) (u : Fin r → E)
    (htr : ∀ y ∈ X.L', ∃ k : ℤ, Algebra.trace ℚ E (herm X.Gm u y) = k) :
    ((discr E : ℤ) : E) • u ∈ X.L' := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have h1 : ∀ y ∈ X.L', herm X.Gm u y ∈ D⁻¹ := by
    intro y hy
    refine TraceDualMin.mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (X.L'.smul_mem
      (⟨cc (a : E), TraceDualMin.isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (herm X.Gm u (cc (a : E) • y))
    rw [HermitianTraceFormVanishing.herm_smul_right, HermitianTraceFormVanishing.cc_cc, mul_comm]
  have hδ : ((discr E : ℤ) : E) ∈ D := by
    have := FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E)
      (NumberField.discr_mem_differentIdeal E (𝓞 E))
    rwa [map_intCast] at this
  refine X.L'_dual _ fun y hy => ?_
  rw [HermitianTraceFormVanishing.herm_smul_left]
  have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
  rw [mul_inv_cancel₀ hD0] at this
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
  rw [← hb]
  exact b.isIntegral_coe

noncomputable def majForm (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    LinearMap.BilinForm ℝ (X.Ψ → Fin r → ℂ) :=
  LinearMap.mk₂ ℝ (MajorantOperators.gI x) (MajorantOperators.gI_add_left x)
    (fun c u v => MajorantOperators.gI_smul_left x c u v)
    (fun u v v' => by
      rw [MajorantOperators.gI_comm hx, MajorantOperators.gI_add_left, MajorantOperators.gI_comm hx v,
        MajorantOperators.gI_comm hx v'])
    (fun c u v => by
      rw [MajorantOperators.gI_comm hx, MajorantOperators.gI_smul_left, MajorantOperators.gI_comm hx v, smul_eq_mul])

theorem majForm_apply (X : Data E r) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (u v : X.Ψ → Fin r → ℂ) : majForm X x hx u v = MajorantOperators.gI x u v := rfl

noncomputable def embHom (X : Data E r) : (Fin r → E) →+ (X.Ψ → Fin r → ℂ) :=
  AddMonoidHom.mk' X.embV fun u v => by
    funext τ a
    simp [Data.embV, Data.emb]

noncomputable def reflHom (X : Data E r) (x : Frame X.Ψ r) : (Fin r → E) →+ (X.Ψ → Fin r → ℂ) :=
  AddMonoidHom.mk' (fun v τ => (2 : ℂ) • X.jp x τ (embHom X v τ)) fun u v => by
    funext τ
    simp only [map_add, Pi.add_apply, Data.jp_add, smul_add]

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.ThickPoint.pair_eq (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hx : x ∈ X.dom) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI x (_root_.GlobalTheory.ThickPoint.embHom X u) (_root_.GlobalTheory.ThickPoint.reflHom X x v) =
      (_root_.GlobalTheory.ThickPoint.traceFormOf X.Gm u v : ℝ) := by
  rw [_root_.GlobalTheory.ThickPoint.traceFormOf_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.trace_eq_sum (X := X)]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI
  refine Finset.sum_congr rfl fun τ _ => ?_
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (X.jp x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ u))
    ((2 : ℂ) • X.jp x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v))).re = _
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_jp_jp X hx, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb]
  simp

end ThickPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma isIntegral_natAbs_discr_mul_of_mem_inv_differentIdeal {z : E}
    (hz : z ∈ (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) :
    IsIntegral ℤ (((discr E).natAbs : E) * z) := by
  have hD : (((discr E).natAbs : 𝓞 E)) ∈ differentIdeal ℤ (𝓞 E) := by
    have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 E))
    rwa [absNorm_differentIdeal E (𝓞 E)] at h
  have hD' : ((discr E).natAbs : E) ∈
      (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hD, by simp⟩
  have hmul := FractionalIdeal.mul_mem_mul hD' hz
  rw [mul_inv_cancel₀ _root_.GlobalTheory.coe_different_ne_zero, FractionalIdeal.mem_one_iff] at hmul
  obtain ⟨a, ha⟩ := hmul
  rw [← ha]
  exact RingOfIntegers.isIntegral_coe a

open NumberField Module Submodule in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.exists_short_basis_at {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hx : x ∈ X.dom) (ε : ℝ) (hε : 0 < ε)
    (hmin : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) :
    ∃ v : Fin r → Fin r → E, (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
      ∀ i, ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (v i)) ≤
        (2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r : ℝ) ^ 4 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E ^ 2 / (4 * ε) := by
  classical
  have hspan : span E (X.L' : Set (Fin r → E)) = ⊤ := by
    rw [eq_top_iff, ← X.toData.Λ_span]
    refine span_le.mpr fun y hy => ?_
    have hNA : (X.NA : E) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    have h := X.NA_sub y hy
    have hy' : y = (X.NA : E)⁻¹ • ((X.NA : E) • y) := by
      rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
    rw [hy']
    refine Submodule.smul_mem _ _ (subset_span ?_)
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at h
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.ShortVectors.exists_basis X.L' X.L'_fg hspan
  let B := _root_.GlobalTheory.ThickPoint.majForm X.toData x hx
  have hBs : B.IsSymm :=
    LinearMap.BilinForm.isSymm_iff.mpr ⟨fun u v => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_comm hx u v⟩
  have hBp : ∀ u, 0 ≤ B u u := fun u => by
    rw [_root_.GlobalTheory.ThickPoint.majForm_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_self hx]
    exact Finset.sum_nonneg fun τ _ => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.maj_nonneg hx τ _
  have hdim : finrank ℝ (X.Ψ → Fin r → ℂ) = 2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r := by
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi X.toData
    rw [Fintype.card_coe] at hc
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, hc]
    ring
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.ThickPoint.exists_euclidean_real hdim B hBs hBp
  let φ := Φ.toAddMonoidHom.comp (_root_.GlobalTheory.ThickPoint.embHom X.toData)
  let ψ := Φ.toAddMonoidHom.comp (_root_.GlobalTheory.ThickPoint.reflHom X.toData x)
  have hφψ : ∀ u v, inner ℝ (φ u) (ψ v) = (_root_.GlobalTheory.ThickPoint.traceFormOf X.Gm u v : ℝ) := by
    intro u v
    simp only [φ, ψ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hΦ, _root_.GlobalTheory.ThickPoint.majForm_apply, _root_.GlobalTheory.ThickPoint.pair_eq _ _ hx]
  have hself : ∀ w, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI x (_root_.GlobalTheory.ThickPoint.embHom X.toData w)
      (_root_.GlobalTheory.ThickPoint.embHom X.toData w) = ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 w) := by
    intro w
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_self hx]
    rfl
  have hφn : ∀ w, ‖φ w‖ ^ 2 = ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 w) := by
    intro w
    rw [← real_inner_self_eq_norm_sq]
    simp only [φ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hΦ, _root_.GlobalTheory.ThickPoint.majForm_apply, hself]
  have hψn : ∀ w, ‖ψ w‖ ^ 2 = 4 * ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 w) := by
    intro w
    have hrefl : _root_.GlobalTheory.ThickPoint.reflHom X.toData x w =
        (2 : ℝ) • fun τ => X.jp x τ (_root_.GlobalTheory.ThickPoint.embHom X.toData w τ) := by
      funext τ i
      simp [_root_.GlobalTheory.ThickPoint.reflHom]
    have hjj : _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI x (fun τ => X.jp x τ (_root_.GlobalTheory.ThickPoint.embHom X.toData w τ))
        (fun τ => X.jp x τ (_root_.GlobalTheory.ThickPoint.embHom X.toData w τ)) =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI x (_root_.GlobalTheory.ThickPoint.embHom X.toData w) (_root_.GlobalTheory.ThickPoint.embHom X.toData w) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI
      refine Finset.sum_congr rfl fun τ _ => ?_
      change (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (X.jp x τ (X.jp x τ _)) (X.jp x τ _)).re =
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (X.jp x τ _) _).re
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_jp_jp _ hx]
    rw [← real_inner_self_eq_norm_sq]
    simp only [ψ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [hΦ, _root_.GlobalTheory.ThickPoint.majForm_apply, hrefl, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_comm hx, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.gI_smul_left, hjj, hself]
    ring
  have hdE : _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E = ((discr E).natAbs : ℝ) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
    simp [Nat.cast_natAbs]
  have hdpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E := by
    rw [hdE]
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero E)
  set lam : ℝ := 2 * √ε / _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E with hlamdef
  have hlam : 0 < lam := by positivity
  have hmin' : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, _root_.GlobalTheory.ThickPoint.traceFormOf X.Gm u (b j) = k) →
      lam ^ 2 ≤ ‖ψ u‖ ^ 2 := by
    intro u hu0 hint
    have hL : ∀ y ∈ X.L', ∃ k : ℤ, _root_.GlobalTheory.ThickPoint.traceFormOf X.Gm u y = k := by
      intro y hy
      rw [← hb] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hint j
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨k, hk⟩ := hy
        obtain ⟨l, hl⟩ := hz
        exact ⟨k + l, by rw [map_add, hk, hl]; push_cast; ring⟩
      | smul n y _ hy =>
        obtain ⟨k, hk⟩ := hy
        exact ⟨n * k, by rw [map_zsmul, hk]; push_cast; simp⟩
    have hD : ∀ y ∈ X.L', _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u y ∈
        (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
      intro y hy
      refine _root_.GlobalTheory.TraceDualMin.mem_inv_different fun a => ?_
      let a' : 𝓞 E := ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (a : E), _root_.GlobalTheory.TraceDualMin.isIntegral_cc (RingOfIntegers.isIntegral_coe a)⟩
      obtain ⟨k, hk⟩ := hL _ (X.L'.smul_mem a' hy)
      refine ⟨k, ?_⟩
      rw [← hk, _root_.GlobalTheory.ThickPoint.traceFormOf_apply, ← algebraMap_smul E a' y]
      change _ = Algebra.trace ℚ E (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc (a : E) • y))
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, _root_.GlobalTheory.TraceDualMin.cc_cc, mul_comm]
    set N : E := ((discr E).natAbs : E) with hN
    have hNu : N • u ∈ X.L' := X.L'_dual _ fun y hy => by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left]
      exact isIntegral_natAbs_discr_mul_of_mem_inv_differentIdeal (hD y hy)
    have hN0 : N ≠ 0 := by
      rw [hN]
      exact_mod_cast Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hε' := hmin _ hNu (smul_ne_zero hN0 hu0)
    have hemb : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (N • u) =
        (((discr E).natAbs : ℝ) : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u := fun τ => by
      funext i
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, hN, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast,
        Complex.ofReal_natCast]
    simp only [hemb, _root_.ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.maj_smul hx] at hε'
    rw [← Finset.mul_sum, ← hdE] at hε'
    rw [hψn, hlamdef, div_pow, mul_pow, Real.sq_sqrt hε.le, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨v, hvL, hvli, hvle⟩ := _root_.GlobalTheory.ThickPoint.transference_pair b
    (_root_.GlobalTheory.ThickPoint.traceFormOf X.Gm) (_root_.GlobalTheory.ThickPoint.traceFormOf_isSymm X.Gm_herm)
    (_root_.GlobalTheory.ThickPoint.traceFormOf_nondegenerate X.Gm_herm X.Gm_det) φ ψ hφψ lam hlam hmin'
  have hbound : ∀ i, ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (v i)) ≤
      (2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r : ℝ) ^ 4 * _root_.ReciprocityTheory.ChartRestriction.G.FD.dE E ^ 2 / (4 * ε) := by
    intro i
    rw [← hφn]
    refine (hvle i).trans (le_of_eq ?_)
    rw [hlamdef, div_pow, div_pow, mul_pow, Real.sq_sqrt hε.le]
    push_cast
    field_simp
    ring
  have hfin : Fintype.card (Fin (2 * _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r)) = finrank ℚ (Fin r → E) := by
    rw [Fintype.card_fin, Module.finrank_pi_fintype]
    simp [_root_.GlobalTheory.ShortVectors.finrank_eq]
    ring
  have hQ : span ℚ (Set.range v) = ⊤ := hvli.span_eq_top_of_card_eq_finrank' hfin
  have hE : span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ span ℚ (Set.range v) := hQ ▸ Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ E _ hz
  obtain ⟨s, hsv, hss, hsli⟩ := exists_linearIndependent E (Set.range v)
  let bs : Basis s E (Fin r → E) :=
    Basis.mk hsli (by rw [Subtype.range_coe, hss, hE])
  let e : s ≃ Fin r := bs.indexEquiv (Pi.basisFun E (Fin r))
  refine ⟨fun i => (e.symm i : Fin r → E), fun i => ?_, hsli.comp _ e.symm.injective, fun i => ?_⟩
  · obtain ⟨k, hk⟩ := hsv (e.symm i).2
    show (e.symm i : Fin r → E) ∈ X.L'
    rw [← hk]
    exact (hb _).mp (hvL k)
  · obtain ⟨k, hk⟩ := hsv (e.symm i).2
    show ∑ τ, X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (e.symm i : Fin r → E)) ≤ _
    rw [← hk]
    exact hbound k

end GlobalTheory
