import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

private theorem exists_dual_fam : ∃ (N : ℕ) (a s : Fin N → Dw.La),
    (∀ x, ∑ m, Dw.EF (s m) x • a m = x) ∧ ∀ y, ∑ m, Dw.EF y (a m) • s m = y := by
  classical
  obtain ⟨N, ⟨a⟩⟩ : ∃ k : ℕ, Nonempty (Module.Basis (Fin k) ℤ Dw.La) := by
    haveI := Dw.fin
    haveI : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
    haveI : Module.IsTorsionFree ℤ Dw.La :=
      Function.Injective.moduleIsTorsionFree Dw.EF Dw.unimod.1 (fun r x => map_smul _ r x)
    haveI : Module.Free ℤ Dw.La := Module.free_of_finite_type_torsion_free'
    exact ⟨_, ⟨Module.finBasis ℤ Dw.La⟩⟩
  choose s hs using fun m : Fin N => Dw.unimod.2 (a.coord m)
  have h1 : ∀ x, ∑ m, Dw.EF (s m) x • a m = x := fun x => by
    simp only [hs, Module.Basis.coord_apply, a.sum_repr]
  refine ⟨N, a, s, h1, fun y => Dw.unimod.1 (LinearMap.ext fun x => ?_)⟩
  conv_rhs => rw [← h1 x]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun m _ => mul_comm _ _

private theorem pr_tmul {K : Type} [CommRing K] (c : K) (x a : Dw.La) :
    pr Dw (c ⊗ₜ x) a = c * (Dw.EF x a : K) := by
  simp [pr, LinearMap.BilinForm.baseChange_tmul, mul_comm]

private theorem pr_add {K : Type} [CommRing K] (y y' : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (y + y') a = pr Dw y a + pr Dw y' a := by
  simp [pr]

private theorem pr_smul {K : Type} [CommRing K] (c : K) (y : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (c • y) a = c * pr Dw y a := by
  simp [pr]

private theorem pr_expand {K : Type} [CommRing K] {N : ℕ} {a s : Fin N → Dw.La}
    (h : ∀ y, ∑ m, Dw.EF y (a m) • s m = y) (y : K ⊗[ℤ] Dw.La) :
    ∑ m, pr Dw y (a m) • ((1 : K) ⊗ₜ[ℤ] s m) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp [pr]
  | add x x' hx hx' => simp only [pr_add, add_smul, Finset.sum_add_distrib, hx, hx']
  | tmul c x =>
    conv_rhs => rw [← h x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [pr_tmul, TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, _root_.mul_one, zsmul_eq_mul, mul_comm]

private theorem pr_act {K : Type} [CommRing K] (o : 𝓞 E) (y : K ⊗[ℤ] Dw.La) (a : Dw.La) :
    pr Dw (((LinearMap.lsmul (𝓞 E) Dw.La o).restrictScalars ℤ).baseChange K y) a = pr Dw y (H.bar o • a) := by
  induction y using TensorProduct.induction_on with
  | zero => simp [pr]
  | add x x' hx hx' => simp only [map_add, pr_add, hx, hx']
  | tmul c x =>
    rw [LinearMap.baseChange_tmul, pr_tmul, pr_tmul, ← Dw.adj]
    rfl

private theorem norm_alg_le (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) : ‖algebraMap ℤ_[p] ℂ_[p] z‖ ≤ 1 :=
  (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 (padicIntHom p z).2

private theorem norm_span_le (p : ℕ) [Fact p.Prime] {T L : Type} [AddCommGroup T] [Module ℤ_[p] T] (f : L → T)
    (hf : Submodule.span ℤ_[p] (Set.range f) = ⊤) (φ : ℂ_[p] ⊗[ℤ_[p]] T →ₗ[ℂ_[p]] ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ a, ‖φ (1 ⊗ₜ f a)‖ ≤ r) (t : T) : ‖φ (1 ⊗ₜ t)‖ ≤ r := by
  have ht : t ∈ Submodule.span ℤ_[p] (Set.range f) := hf ▸ Submodule.mem_top
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [TensorProduct.tmul_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ_[p] c, map_smul, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le p c)).trans hx

private theorem norm_cong (p : ℕ) [Fact p.Prime] (n : ℕ) (g u : ℤ_[p]) (j : ℤ) (h : (p : ℤ_[p]) ^ n ∣ g - u * j)
    (y : ℂ_[p]) (hy : ‖y‖ ≤ 1) :
    ‖algebraMap ℤ_[p] ℂ_[p] u * (y * (j : ℂ_[p])) + y * -algebraMap ℤ_[p] ℂ_[p] g‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨c, hc⟩ := h
  have hc' := congrArg (algebraMap ℤ_[p] ℂ_[p]) hc
  rw [map_sub, map_mul, map_mul, map_intCast, map_pow, map_natCast] at hc'
  have e3 : algebraMap ℤ_[p] ℂ_[p] u * (y * (j : ℂ_[p])) + y * -algebraMap ℤ_[p] ℂ_[p] g =
      -(y * algebraMap ℤ_[p] ℂ_[p] c * (p : ℂ_[p]) ^ n) := by
    linear_combination (-y) * hc'
  have hp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  rw [e3, norm_neg, norm_mul, norm_mul, norm_pow, hp]
  exact mul_le_of_le_one_left (by positivity) (mul_le_one₀ hy (norm_nonneg _) (norm_alg_le p c))

private theorem isot (p : ℕ) [Fact p.Prime] (n : ℕ) {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
    (β : LinearMap.BilinForm ℤ_[p] T) (f : Dw.La →+ T) (u : ℤ_[p]) (hspan : Submodule.span ℤ_[p] (Set.range f) = ⊤)
    (hcong : ∀ a b, (p : ℤ_[p]) ^ n ∣ β (f a) (f b) - u * (Dw.EF a b : ℤ_[p]))
    {k : ℕ} (e t : Module.Basis (Fin k) ℤ_[p] T)
    (ht : ∀ w j, (t.baseChange ℂ_[p]).repr w j = β.baseChange ℂ_[p] w (1 ⊗ₜ e j))
    (B : ℂ_[p] ⊗[ℤ_[p]] T →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La)
    (hB : ∀ w x, pr Dw (B w) x = -β.baseChange ℂ_[p] w (1 ⊗ₜ f x)) (w w' : ℂ_[p] ⊗[ℤ_[p]] T)
    (h0 : β.baseChange ℂ_[p] w' w = 0) (hw : ∀ a, ‖pr Dw (B w) a‖ ≤ 1) (hw' : ∀ a, ‖pr Dw (B w') a‖ ≤ 1) :
    ‖Dw.EF.baseChange ℂ_[p] (B w) (B w')‖ ≤ (p : ℝ)⁻¹ ^ n := by
  obtain ⟨N, a, s, h1, h2⟩ := exists_dual_fam Dw
  have hr : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ n := by positivity
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ_[p] ⊗[ℤ_[p]] T →ₗ[ℂ_[p]] ℂ_[p], ∀ z, φ z =
      Dw.EF.baseChange ℂ_[p] (B z) (B w') + algebraMap ℤ_[p] ℂ_[p] u * β.baseChange ℂ_[p] w' z :=
    ⟨(Dw.EF.baseChange ℂ_[p]).flip (B w') ∘ₗ B + algebraMap ℤ_[p] ℂ_[p] u • β.baseChange ℂ_[p] w', fun z => rfl⟩
  have hf : ∀ x, ‖φ (1 ⊗ₜ f x)‖ ≤ (p : ℝ)⁻¹ ^ n := by
    intro x
    have e1 : Dw.EF.baseChange ℂ_[p] (B (1 ⊗ₜ f x)) (B w') =
        ∑ m, pr Dw (B w') (a m) * -algebraMap ℤ_[p] ℂ_[p] (β (f x) (f (s m))) := by
      conv_lhs => rw [← pr_expand Dw h2 (B w')]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, smul_eq_mul]
      congr 1
      refine (hB _ _).trans ?_
      rw [LinearMap.BilinForm.baseChange_tmul, _root_.mul_one, Algebra.algebraMap_eq_smul_one]
    have e2 : β.baseChange ℂ_[p] w' (1 ⊗ₜ f x) = ∑ m, pr Dw (B w') (a m) * (Dw.EF x (s m) : ℂ_[p]) := by
      conv_lhs => rw [← h1 x]
      simp only [map_sum, map_zsmul, TensorProduct.tmul_sum, TensorProduct.tmul_smul, hB, zsmul_eq_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← LinearMap.IsAlt.neg (B := Dw.EF) Dw.alt x (s m)]
      push_cast
      ring
    rw [hφ, e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun m _ => ?_
    rw [add_comm]
    exact norm_cong p n _ u _ (hcong x (s m)) _ (hw' _)
  have hT := norm_span_le p f hspan φ hr hf
  have hc := norm_span_le p f hspan (β.baseChange ℂ_[p] w) zero_le_one fun x => by
    have := hw x
    rwa [hB, norm_neg] at this
  have e4 : Dw.EF.baseChange ℂ_[p] (B w) (B w') = φ w := by
    rw [hφ, h0, mul_zero, add_zero]
  have e5 : φ w = ∑ j, β.baseChange ℂ_[p] w (1 ⊗ₜ e j) * φ (1 ⊗ₜ t j) := by
    conv_lhs => rw [← (t.baseChange ℂ_[p]).sum_repr w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, ht, Module.Basis.baseChange_apply]
  rw [e4, e5]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun j _ => ?_
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hc _)).trans (hT _)

private theorem exists_lin {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] (g : Dw.La →+ (V →ₗ[K] K)) :
    ∃ B : V →ₗ[K] K ⊗[ℤ] Dw.La, ∀ w x, pr Dw (B w) x = g x w := by
  obtain ⟨N, a, s, h1, -⟩ := exists_dual_fam Dw
  refine ⟨∑ m, (g (a m)).smulRight ((1 : K) ⊗ₜ[ℤ] s m), fun w x => ?_⟩
  conv_rhs => rw [← h1 x]
  simp only [pr, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum,
    map_smul, LinearMap.smul_apply, LinearMap.BilinForm.baseChange_tmul, map_zsmul,
    smul_eq_mul, zsmul_eq_mul, _root_.mul_one]
  exact Finset.sum_congr rfl fun m _ => by simp [mul_comm]

private theorem pr_ext {K : Type} [CommRing K] (y y' : K ⊗[ℤ] Dw.La) (h : ∀ x, pr Dw y x = pr Dw y' x) : y = y' := by
  obtain ⟨N, a, s, -, h2⟩ := exists_dual_fam Dw
  rw [← pr_expand Dw h2 y, ← pr_expand Dw h2 y']
  simp only [h]

end SlopeTestRemainingChoices

theorem UpperTheory.tate_module_pairing_congruence :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (P : PtP E p) (f : Dw.La →+ P.T) (u : ℤ_[p]), 1 ≤ n → Submodule.span ℤ_[p] (Set.range f) = ⊤ → (∀ (o : 𝓞 E) a, f (o • a) = P.actT o (f a)) → IsUnit u → (∀ a b, (p : ℤ_[p]) ^ n ∣ pairT P.A P.eps (f a) (f b) - u * (Dw.EF a b : ℤ_[p])) → ∃ B : P.V →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La, (∀ w a, pr Dw (B w) a = -P.pairV w (1 ⊗ₜ f a)) ∧ (∀ w (σ : 𝓞 E →+* ℂ_[p]), (∀ o, P.actV o w = σ o • w) → IsEigL Dw σ (B w)) ∧ ∀ w w', P.pairV w w' = 0 → (∀ a, ‖pr Dw (B w) a‖ ≤ 1) → (∀ a, ‖pr Dw (B w') a‖ ≤ 1) → ‖Dw.EF.baseChange ℂ_[p] (B w) (B w')‖ ≤ (p : ℝ)⁻¹ ^ n := by
  intro E _ _ _ H Dw p _ n _ hstar P f u _ hspan hact _ hcong
  obtain ⟨B, hB'⟩ := exists_lin Dw (K := ℂ_[p]) (V := P.V)
    (-(P.pairV.flip.toAddMonoidHom.comp ((TensorProduct.mk ℤ_[p] ℂ_[p] P.T 1).toAddMonoidHom.comp f)))
  have hB : ∀ w x, pr Dw (B w) x = -P.pairV w (1 ⊗ₜ f x) := hB'
  refine ⟨B, hB, fun w σ hw o => pr_ext Dw _ _ fun x => ?_, fun w w' h0 hw hw' => ?_⟩
  · rw [pr_act, pr_smul, hB, hB, hact, ← hstar]
    have e : P.pairV w (1 ⊗ₜ P.actT (star o) (f x)) = P.pairV (P.actV o w) (1 ⊗ₜ f x) :=
      (P.pairV_act o w (1 ⊗ₜ f x)).symm
    rw [e, hw, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_neg]
  · obtain ⟨k, e, t, -, ht⟩ := P.exists_dual_bases
    have h0' : P.pairV w' w = 0 := by rw [P.pairV_swap w' w, h0, neg_zero]
    exact isot Dw p n (pairT P.A P.eps) f u hspan hcong e t ht B hB w w' h0' hw hw'
