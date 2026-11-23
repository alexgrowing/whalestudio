import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslateJetNeZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBasisSpanEqOfCommensurable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfSelfD
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CoeffEqZeroOfOrthonormal

namespace GlobalTheory.Dict.SubJet

noncomputable section

section General

open Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped Classical

theorem exists_poly_scale {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) {s : ℂ}
    (hs : s ≠ 0) : ∃ P' : MvPolynomial σ ℂ, P'.support = P.support ∧
      ∀ (u : σ → W) (F : W → ℂ) (x : W), polyDeriv P (fun l => s • u l) F x = polyDeriv P' u F x := by
  let P' : MvPolynomial σ ℂ := ∑ m ∈ P.support,
    MvPolynomial.monomial m (s ^ Multiset.card (Finsupp.toMultiset m) * P.coeff m)
  have hc : ∀ m, P'.coeff m = s ^ Multiset.card (Finsupp.toMultiset m) * P.coeff m := by
    intro m
    simp only [P', MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 h, mul_zero]
  have hsup : P'.support = P.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff, hc, ne_eq, mul_eq_zero, pow_ne_zero _ hs, false_or]
  refine ⟨P', hsup, fun u F x => ?_⟩
  unfold polyDeriv
  rw [hsup]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ _ (fun _ => s), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, hc]
  ring

theorem exists_jet_of_periods {ι A : Type} [Fintype ι] [AddCommGroup A] (p : A →+ EuclideanSpace ℂ ι)
    (hp : Function.Injective p) (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hb : ∀ y, y ∈ lat b ↔ ∃ a, p a = y) (hint : ∀ a a', ∃ k : ℤ, (Hf (p a) (p a')).im = k)
    (hperf : ∀ φ : A →+ ℤ, ∃ a, ∀ a', (φ a' : ℝ) = (Hf (p a) (p a')).im) (Q : A → ℝ)
    (hQ : ∀ a a', ∃ k : ℤ, Q (a + a') = Q a + Q a' - (Hf (p a) (p a')).im + 2 * k)
    (q : ℕ) (P : MvPolynomial ι ℂ) (hP : P ≠ 0) (hq : 3 * P.totalDegree + 2 ≤ q) {s : ℂ} (hs : s ≠ 0) :
    ∃ G : EuclideanSpace ℂ ι → ℂ, Differentiable ℂ G ∧
      (∀ a v, G (v + p a) = cexp (Real.pi * I * (q * Q a : ℝ)) *
        cexp (q * Real.pi * Hf v (p a) + q * Real.pi * Hf (p a) (p a) / 2) * G v) ∧
      polyDeriv P (fun i => s • EuclideanSpace.single i 1) G 0 ≠ 0 := by
  let Y : GT ι :=
    { b := b
      integral := fun x y hx hy => by
        obtain ⟨a, rfl⟩ := (hb x).1 hx
        obtain ⟨a', rfl⟩ := (hb y).1 hy
        exact hint a a'
      perfect := fun φ => by
        obtain ⟨a, ha⟩ := hperf (φ.comp (p.codRestrict (lat b) fun a => (hb _).2 ⟨a, rfl⟩))
        refine ⟨p a, (hb _).2 ⟨a, rfl⟩, ?_⟩
        rintro ⟨y, hy⟩
        obtain ⟨a', rfl⟩ := (hb y).1 hy
        exact ha a'
      ka := fun y => cexp (Real.pi * I * Q (Function.invFun p y))
      ka_abs := fun x _ => by
        rw [Complex.norm_exp]
        simp }
  have hka : ∀ a, Y.ka (p a) = cexp (Real.pi * I * Q a) := fun a => by
    simp only [Y, Function.leftInverse_invFun hp a]
  have hC : FPw.Coc Y 1 := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (hb x).1 hx
    obtain ⟨a', rfl⟩ := (hb y).1 hy
    obtain ⟨k, hk⟩ := hQ a a'
    rw [← map_add, hka, hka, hka, hk, ← Complex.exp_add, ← Complex.exp_add,
      Complex.exp_eq_exp_iff_exists_int]
    refine ⟨k, ?_⟩
    push_cast
    ring
  obtain ⟨θ, hθ, h0⟩ := GlobalTheory.ThetaExist.exists_sec_ne_zero Y hC
  obtain ⟨P', hsup, hP'⟩ := exists_poly_scale (W := EuclideanSpace ℂ ι) P hs
  have hne : P' ≠ 0 := by
    rwa [Ne, ← MvPolynomial.support_eq_empty, hsup, MvPolynomial.support_eq_empty]
  have hdeg : P'.totalDegree ≤ P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsup]
  obtain ⟨G, hG, hlaw, hG0⟩ := exists_section_jet_ne_zero Y θ hθ h0 _ q hq P' hne hdeg
  refine ⟨G, hG, fun a v => ?_, by rw [hP']; exact hG0⟩
  rw [hlaw (p a) ((hb _).2 ⟨a, rfl⟩) v, hka, ← Complex.exp_nat_mul]
  congr 3
  push_cast
  ring

def colEquiv {K : Type} [Fintype K] {n g : ℕ} (e : K ≃ Fin n × Fin g) (s : ℂ) (hs : s ≠ 0) :
    (Fin n → Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ K where
  toFun z := WithLp.toLp 2 fun i => s * z (e i).1 (e i).2
  invFun y k j := s⁻¹ * y (e.symm (k, j))
  map_add' z z' := by ext i; simp [mul_add]
  map_smul' c z := by ext i; simp [mul_left_comm]
  left_inv z := by funext k j; simp [hs]
  right_inv y := by ext i; simp [hs]

theorem colEquiv_apply {K : Type} [Fintype K] {n g : ℕ} (e : K ≃ Fin n × Fin g) (s : ℂ) (hs : s ≠ 0)
    (z : Fin n → Fin g → ℂ) (i : K) : colEquiv e s hs z i = s * z (e i).1 (e i).2 := rfl

theorem exists_basis_cols {K κ : Type} [Fintype K] [Fintype κ] {n g : ℕ}
    (Φ : (Fin n → Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ K) (b₀ : Module.Basis κ ℝ (Fin g → ℂ)) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card K)) ℝ (EuclideanSpace ℂ K),
      ∀ z, Φ z ∈ lat b ↔ ∀ k, z k ∈ Submodule.span ℤ (Set.range b₀) := by
  let b₁ := (Pi.basis fun _ : Fin n => b₀).map (Φ.restrictScalars ℝ)
  have hcard : Fintype.card (Σ _ : Fin n, κ) = Fintype.card (Fin (2 * Fintype.card K)) := by
    rw [← Module.finrank_eq_card_basis b₁, finrank_real_of_complex]
    simp
  refine ⟨b₁.reindex (Fintype.equivOfCardEq hcard), fun z => ?_⟩
  rw [lat, Module.Basis.range_reindex]
  simp only [Module.Basis.mem_span_iff_repr_mem, b₁, Module.Basis.map_repr, Sigma.forall]
  simp

end General

section Arith

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.SW.TensLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r} {L : Lt E r}
  {𝔐 : Ideal (𝓞 E)} {M : ℕ}

theorem EF_add_left (u u' v : Fin r → E) : EF X (u + u') v = EF X u v + EF X u' v := by
  simp only [EF_eq_bilin, map_add, LinearMap.add_apply]

theorem EF_add_right (u v v' : Fin r → E) : EF X u (v + v') = EF X u v + EF X u v' := by
  simp only [EF_eq_bilin, map_add]

theorem EF_ratSmul_left (c : ℚ) (u v : Fin r → E) : EF X ((c : E) • u) v = c * EF X u v := by
  rw [Rat.cast_smul_eq_qsmul, EF_eq_bilin, EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem EF_mem_mul (hL : SelfD X L) (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {u v : Fin r → E}
    (hu : u ∈ 𝔐 • L) (hv : v ∈ 𝔐 • L) : ∃ k : ℤ, EF X u v = M * k := by
  refine Submodule.smul_induction_on hu (fun a ha x hx => ?_) ?_
  · refine Submodule.smul_induction_on hv (fun b hb y hy => ?_) ?_
    · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
      have h1 : a * b' ∈ Ideal.span {(M : 𝓞 E)} :=
        hM ▸ Ideal.mul_mem_mul ha (Ideal.subset_span ⟨b, hb, rfl⟩)
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
      have hc' : (c : E) * M = a * cc (b : E) := by
        have := congrArg (algebraMap (𝓞 E) E) hc
        rw [map_mul, map_mul, map_natCast] at this
        exact this
      obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem c hx) y hy
      refine ⟨k, ?_⟩
      have h2 : EF X (cc (b : E) • (a : E) • x) y = EF X ((a : E) • x) ((b : E) • y) := by
        rw [EF_smul]
        simp [cc]
      change EF X ((a : E) • x) ((b : E) • y) = _
      rw [← h2, ← hk, ← EF_ratSmul_left, smul_smul, mul_comm, ← hc']
      congr 1
      change _ = _ • (c : E) • x
      rw [smul_smul, mul_comm, Rat.cast_natCast]
    · rintro y y' ⟨k, hk⟩ ⟨k', hk'⟩
      exact ⟨k + k', by rw [EF_add_right, hk, hk']; push_cast; ring⟩
  · rintro y y' ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k + k', by rw [EF_add_left, hk, hk']; push_cast; ring⟩

theorem mem_of_EF_mem_mul (hL : SelfD X L) (hM0 : M ≠ 0) (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)})
    {u : Fin r → E} (hu : ∀ v ∈ 𝔐 • L, ∃ k : ℤ, EF X u v = M * k) : u ∈ 𝔐 • L := by
  have hQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have h1 : ∀ c ∈ conjI 𝔐, c • (((M : ℚ)⁻¹ : ℚ) : E) • u ∈ L := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨b, hb, hcb⟩ := hc
      refine (hL.2 _).2 fun y hy => ?_
      obtain ⟨k, hk⟩ := hu _ (Submodule.smul_mem_smul hb hy)
      refine ⟨k, ?_⟩
      change EF X ((c : E) • _) y = _
      change EF X u ((b : E) • y) = _ at hk
      have h3 : cc (cc (b : E)) = b := by simp [cc]
      rw [EF_smul, EF_ratSmul_left, hcb, h3, hk, inv_mul_cancel_left₀ hQ]
    | zero => rw [zero_smul]; exact L.zero_mem
    | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
    | smul a b _ hb => rw [smul_assoc]; exact L.smul_mem a hb
  have h2 : ∀ z ∈ 𝔐 * conjI 𝔐, z • (((M : ℚ)⁻¹ : ℚ) : E) • u ∈ 𝔐 • L := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) fun a b ha hb => ?_
    · rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h1 c hc)
    · rw [add_smul]
      exact Submodule.add_mem _ ha hb
  have h3 := h2 M (hM ▸ Ideal.mem_span_singleton_self _)
  have hE : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Rat.cast_inv, Rat.cast_natCast,
    smul_inv_smul₀ hE] at h3

theorem exists_EF_eq {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) (hL : SelfD X L) (hM0 : M ≠ 0)
    (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) (φ : (𝔐 • L : Lt E r) →+ ℤ) :
    ∃ u ∈ 𝔐 • L, ∀ v : (𝔐 • L : Lt E r), EF X u v = M * φ v := by
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
    (𝔐 • L : Lt E r).subtype.toAddMonoidHom (𝔐 • L : Lt E r).injective_subtype
    ((AddMonoidHom.mulLeft (M : ℚ)).comp ((Int.castAddHom ℚ).comp φ))
  let u := (LinearMap.BilinForm.toDual _ (SelfTorus.nondeg hs)).symm F.toRatLinearMap
  have hu (v : (𝔐 • L : Lt E r)) : EF X u v = M * φ v :=
    (LinearMap.BilinForm.apply_toDual_symm_apply (hB := SelfTorus.nondeg hs) F.toRatLinearMap v).trans
      (DFunLike.congr_fun hF v)
  exact ⟨u, mem_of_EF_mem_mul hL hM0 hM fun y hy => ⟨_, hu ⟨y, hy⟩⟩, hu⟩

theorem EF_quad {w : E} (hw : w + cc w = 1) (u v : Fin r → E) :
    EF X (u + v) (w • (u + v)) = EF X u (w • u) + EF X v (w • v) - EF X u v + 2 * EF X u (w • v) := by
  have h2 : EF X v (w • u) = -EF X u (cc w • v) := by rw [EF_swap, EF_smul]
  have h3 : EF X u (w • v) + EF X u (cc w • v) = EF X u v := by
    rw [← EF_add_right, ← add_smul, hw, one_smul]
  simp only [smul_add, EF_add_left, EF_add_right]
  linarith

theorem exists_basis_smul {κ : Type} [Fintype κ] (pl : (Fin r → E) →+ (Fin g → ℂ))
    (b₀ : Module.Basis κ ℝ (Fin g → ℂ))
    (hb₀ : ∀ z, z ∈ Submodule.span ℤ (Set.range b₀) ↔ ∃ u ∈ L, z = pl u) (hM0 : M ≠ 0)
    (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) :
    ∃ b₁ : Module.Basis κ ℝ (Fin g → ℂ), ∀ z, z ∈ Submodule.span ℤ (Set.range b₁) ↔ ∃ u ∈ 𝔐 • L, z = pl u := by
  have hle : Ideal.span {(M : 𝓞 E)} ≤ 𝔐 := by
    rw [← hM]
    exact Ideal.mul_le.2 fun a ha b _ => 𝔐.mul_mem_right b ha
  have hMm : (M : 𝓞 E) ∈ 𝔐 := (Ideal.span_singleton_le_iff_mem _).1 hle
  let N : Submodule ℤ (Fin g → ℂ) := ((𝔐 • L : Lt E r).toAddSubgroup.map pl).toIntSubmodule
  have hN : ∀ z, z ∈ N ↔ ∃ u ∈ 𝔐 • L, z = pl u := fun z =>
    ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩⟩
  obtain ⟨b₁, hb₁⟩ := TensorLat.exists_basis_span_eq_of_commensurable b₀ N (M := M) (by omega)
    (fun z hz => by
      obtain ⟨u, hu, rfl⟩ := (hb₀ z).1 hz
      refine (hN _).2 ⟨M • u, ?_, by rw [map_nsmul]⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMm hu)
    (fun z hz => by
      obtain ⟨u, hu, rfl⟩ := (hN z).1 hz
      exact (hb₀ _).2 ⟨M • u, nsmul_mem (Submodule.smul_le_right hu) M, by rw [map_nsmul]⟩)
  exact ⟨b₁, fun z => by rw [hb₁, hN]⟩

end Arith

end

end GlobalTheory.Dict.SubJet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

open GlobalTheory.Dict.SubJet in

theorem GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) ∧ I2.polyDeriv P (letterDir X hr idx) F 0 ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hxd ho t ht hc 𝔐 M _ hM P hP hdeg
  have hM0 : M ≠ 0 := by omega
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, him, -, -, hinj, -⟩ := hx_laws E r X g bas idx n hs hn x hxd
  obtain ⟨hdiag, -⟩ := hx_ortho E r X g bas idx hs x hxd ho
  obtain ⟨T, ψ, -, -, -, hT, -⟩ := exists_torus_of_selfD E r X g bas idx hs w hw L hL x hxd ho t ht hc
  let pl : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) fun u v => by
    simp only [pv, per_add]
    rfl
  have hpl : ∀ u, pl u = pv X idx x u := fun _ => rfl
  have hb₀ : ∀ z, z ∈ Submodule.span ℤ (Set.range (T.b.map (ψ.symm.restrictScalars ℝ))) ↔
      ∃ u ∈ L, z = pl u := by
    intro z
    have h1 : z ∈ Submodule.span ℤ (Set.range (T.b.map (ψ.symm.restrictScalars ℝ))) ↔ ψ z ∈ T.L := by
      simp only [Module.Basis.mem_span_iff_repr_mem, Module.Basis.map_repr]
      rfl
    rw [h1, hT]
    simp only [ψ.injective.eq_iff, hpl]
  obtain ⟨b₁, hb₁⟩ := exists_basis_smul pl _ hb₀ hM0 hM
  let s : ℂ := (Real.sqrt (t / M) : ℝ)
  have htM : 0 < t / M := by positivity
  have hs0 : s ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 htM).ne'
  have hss : (M : ℂ) * (s * s) = t := by
    simp only [s]
    rw [← ofReal_mul, Real.mul_self_sqrt htM.le]
    push_cast
    field_simp
  let e : Harm.Var X.Ψ q0 X.p0 (Fin n) ≃ Fin n × Fin g :=
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)).trans
      (Equiv.prodCongr (Equiv.refl _) ((rowOf X hr).trans idx.symm))
  let Φ := colEquiv e s hs0
  have hH : ∀ z z', (M : ℂ) * I2.Hf (Φ z) (Φ z') = ∑ b, hx X bas idx x (z b) (z' b) := by
    intro z z'
    simp only [hdiag, hc]
    rw [I2.Hf, Finset.mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv e _ _ fun i => ?_
    rw [colEquiv_apply, colEquiv_apply, map_mul, conj_ofReal, ← hss]
    ring
  obtain ⟨b, hb⟩ := exists_basis_cols Φ b₁
  let p : (Fin n → (𝔐 • L : Lt E r)) →+ EuclideanSpace ℂ (Harm.Var X.Ψ q0 X.p0 (Fin n)) :=
    AddMonoidHom.mk' (fun a => Φ fun k => pl (a k)) fun a a' => by
      rw [← map_add]
      congr 1
      funext k
      exact map_add pl _ _
  have hp : ∀ a, p a = Φ fun k => pv X idx x (a k) := fun _ => rfl
  have hI : ∀ a a', (I2.Hf (p a) (p a')).im = ((∑ k, EF X (a k) (a' k) : ℚ) : ℝ) / M := by
    intro a a'
    have h := congrArg Complex.im (hH (fun k => pv X idx x (a k)) fun k => pv X idx x (a' k))
    rw [← ofReal_natCast, im_ofReal_mul, im_sum] at h
    simp only [him] at h
    rw [hp, hp, eq_div_iff hMR, mul_comm, h, Rat.cast_sum]
  have hZ : ∀ u v : Fin n → Fin r → E, (∀ k, u k ∈ 𝔐 • L) → (∀ k, v k ∈ 𝔐 • L) →
      ∃ m : ℤ, ∑ k, EF X (u k) (v k) = M * m := by
    intro u v hu hv
    choose m hm using fun k => EF_mem_mul hL hM (hu k) (hv k)
    exact ⟨∑ k, m k, by simp only [hm, Int.cast_sum, Finset.mul_sum]⟩
  obtain ⟨G, hG, hlaw, hG0⟩ := exists_jet_of_periods p
    (fun a a' h => funext fun k => Subtype.ext (hinj (congrFun (Φ.injective h) k))) b
    (fun y => by
      obtain ⟨z, rfl⟩ := Φ.surjective y
      simp only [hb, hb₁]
      constructor
      · intro h
        choose u hu hu' using h
        exact ⟨fun k => ⟨u k, hu k⟩, congrArg Φ (funext fun k => (hu' k).symm)⟩
      · rintro ⟨a, ha⟩ k
        exact ⟨a k, (a k).2, (congrFun (Φ.injective ha) k).symm⟩)
    (fun a a' => by
      obtain ⟨m, hm⟩ := hZ _ _ (fun k => (a k).2) fun k => (a' k).2
      refine ⟨m, ?_⟩
      rw [hI, hm]
      push_cast
      field_simp)
    (fun φ => by
      choose u hu hu' using fun k => exists_EF_eq hs hL hM0 hM
        (φ.comp (AddMonoidHom.single (fun _ : Fin n => (𝔐 • L : Lt E r)) k))
      refine ⟨fun k => ⟨u k, hu k⟩, fun a' => ?_⟩
      rw [hI]
      simp only [hu']
      conv_lhs => rw [← Finset.univ_sum_single a', map_sum]
      rw [← Finset.mul_sum]
      push_cast
      field_simp
      rfl)
    (fun a => ((∑ k, EF X (a k) ((w : E) • (a k : Fin r → E)) : ℚ) : ℝ) / M)
    (fun a a' => by
      obtain ⟨m, hm⟩ := hZ _ (fun k => (w : E) • (a' k : Fin r → E)) (fun k => (a k).2)
        fun k => Submodule.smul_mem _ w (a' k).2
      refine ⟨m, ?_⟩
      simp only [hI, Pi.add_apply, Submodule.coe_add, EF_quad hw, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hm]
      push_cast
      field_simp)
    M P hP hdeg hs0
  refine ⟨G ∘ Φ.toContinuousLinearEquiv, hG.comp Φ.toContinuousLinearEquiv.differentiable, fun u hu z => ?_, ?_⟩
  · have h := hlaw (fun k => ⟨u k, hu k⟩) (Φ z)
    rw [hp, ← map_add, mul_div_cancel₀ _ hMR, mul_comm (M : ℂ), _root_.mul_assoc (Real.pi : ℂ) M,
      _root_.mul_assoc (Real.pi : ℂ) M, hH, hH] at h
    simp only at h
    obtain ⟨m, hm⟩ := hZ u (fun k => (w : E) • u k) hu fun k => Submodule.smul_mem _ w (hu k)
    have hadd : ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • pv X idx x (u k)) (pv X idx x (u k)) =
        ∑ k, hx X bas idx x (z k) (pv X idx x (u k)) +
          1 / 2 * ∑ k, hx X bas idx x (pv X idx x (u k)) (pv X idx x (u k)) := by
      simp only [hdiag, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    change G (Φ z) = _ * G (Φ (z + fun k => pv X idx x (u k)))
    rw [h, hadd, epsW, hm, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans (congrArg (· * G (Φ z)) ?_)
    refine (Complex.exp_int_mul_two_pi_mul_I (M * m)).symm.trans ?_
    congr 1
    push_cast
    ring
  · rw [Jet.polyDeriv_comp_equiv, map_zero]
    convert hG0 using 2
    funext l
    ext i
    change s * (Pi.single (e l).1 (Pi.single (e l).2 1) : Fin n → Fin g → ℂ) (e i).1 (e i).2 = _
    by_cases h : i = l
    · simp [h]
    · have h' : e i ≠ e l := fun h0 => h (e.injective h0)
      by_cases h1 : (e i).1 = (e l).1
      · have h2 : (e i).2 ≠ (e l).2 := fun h2 => h' (Prod.ext h1 h2)
        simp [h, h1, h2]
      · simp [h, h1]
