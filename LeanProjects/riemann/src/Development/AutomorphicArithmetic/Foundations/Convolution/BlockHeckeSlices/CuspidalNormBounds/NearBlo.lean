import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.NearFinite
import GroundTheory.AutomorphicForms.LocallyProfinite
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IndependenceEigenvectors
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonSplitSequence

open NumberField IsDedekindDomain Topology GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Cm
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.BW

private theorem indep {V I J : Type} [AddCommGroup V] [Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ)
    (h0 : ∀ j, v j ≠ 0) (he : ∀ j i, T i (v j) = lam j i • v j) (hinj : Function.Injective lam) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.IndependenceEigenvectors.indep T v lam h0 he hinj

private theorem nss {G A : Type} [Group G] [NormedRing A] [NormedAlgebra ℝ A] (ρ : G →* A) (H : Subgroup G)
    (h : ∀ g ∈ H, ‖ρ g - 1‖ ≤ 1 / 2) : ∀ g ∈ H, ρ g = 1 :=
  _root_.UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.nss ρ H h

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private theorem openKer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {d : ℕ} (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ρ u = 1 := by
  have hc : Continuous fun g => ‖ρ g - 1‖ := (hρ.sub continuous_const).norm
  have hn : {g | ‖ρ g - 1‖ < 1 / 2} ∈ 𝓝 (1 : G) := (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_isCompact_subset hn
  exact ⟨U, U.isOpen, nss ρ U fun g hg => (hU hg).le⟩

private theorem trInv {R : Type} [CommRing R] {r : ℕ} (X Y Z : Matrix (Fin r) (Fin r) R) :
    Matrix.trace ((X * Y - Y * X) * Z) = -Matrix.trace (Y * (X * Z - Z * X)) := by
  rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, neg_sub, mul_assoc X, Matrix.trace_mul_comm X, mul_assoc, mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r : ℕ}

private theorem cenScalar (z : UC E r) (hz : z ∈ Subalgebra.center ℂ (UC E r)) :
    ∃ κ : ((E →+* ℂ) → Fin r → ℂ) → ℂ, Continuous κ ∧ ∀ (f : Sm E r) Λ, (∀ τ u, cap τ u f = (∏ i, (u + Λ τ i)) • f) →
      uC E r z f = κ Λ • f := by
  rw [center_UC] at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨fun Λ => ∏ i, (u + Λ τ i), by fun_prop, fun f Λ h => by rw [uC_capC, h]⟩
  | algebraMap c => exact ⟨fun _ => c, continuous_const, fun f Λ _ => by rw [AlgHom.commutes]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, ha.add hb, fun f Λ h => by rw [map_add, LinearMap.add_apply, h1 f Λ h, h2 f Λ h, Pi.add_apply, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a * b, ha.mul hb, fun f Λ h => by
      rw [map_mul, Module.End.mul_apply, h2 f Λ h, map_smul, h1 f Λ h, Pi.mul_apply, smul_smul, mul_comm]⟩

private theorem typeMap (ρ : Typ E r) : ∃ (X : Submodule ℂ (Matrix (Fin ρ.d) (Fin ρ.d) ℂ)) (τ : Representation ℂ (archCompact E r) X),
    ∀ φ : cuspForms E r, Killed ρ.ρ φ.1 → ∃ f : X →ₗ[ℂ] cuspForms E r,
      (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb E r (k : archGroup E r))) ∧ φ ∈ LinearMap.range f := by
  let A : (KA E r →₀ ℂ) →ₗ[ℂ] Matrix (Fin ρ.d) (Fin ρ.d) ℂ := Finsupp.linearCombination ℂ ρ.ρ
  let ι : archCompact E r →* KA E r :=
    { toFun := fun k => ⟨infEmb E r (k : archGroup E r), k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hA : ∀ (k : KA E r) x, A (x.mapDomain (k * ·)) = ρ.ρ k * A x := by
    intro k x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy, mul_add]
    | single a c => simp [A]
  have hst : ∀ (k : KA E r), ∀ y ∈ LinearMap.range A, LinearMap.mulLeft ℂ (ρ.ρ k) y ∈ LinearMap.range A := by
    rintro k _ ⟨x, rfl⟩
    exact ⟨_, hA k x⟩
  refine ⟨LinearMap.range A,
    { toFun := fun k => (LinearMap.mulLeft ℂ (ρ.ρ (ι k))).restrict (hst (ι k))
      map_one' := LinearMap.ext fun y => Subtype.ext (by simp)
      map_mul' := fun k l => LinearMap.ext fun y => Subtype.ext (by simp [mul_assoc]) }, fun φ hφ => ?_⟩
  have hmem : ∀ k : KA E r, rightTranslate (k : GA E r) φ.1 ∈ cuspForms E r :=
    fun k => ⟨φ.2.1.rightTranslate_of_mem_maxCompact k.2, φ.2.2.translate _⟩
  let B : (KA E r →₀ ℂ) →ₗ[ℂ] cuspForms E r := Finsupp.linearCombination ℂ fun k => ⟨_, hmem k⟩
  have hB : ∀ x g, (B x).1 g = x.sum fun k c => c * φ.1 (g * (k : GA E r)) := by
    intro x g
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), ← hx, ← hy]
      rfl
    | single a c =>
      rw [Finsupp.sum_single_index (zero_mul _)]
      simp only [B, Finsupp.linearCombination_single]
      rfl
  have hAB : ∀ x y, A x = A y → B x = B y := by
    intro x y h
    rw [← sub_eq_zero, ← map_sub] at h ⊢
    exact Subtype.ext (funext fun g => (hB _ g).trans (hφ _ h g))
  obtain ⟨s, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  have hs' : ∀ y : LinearMap.range A, A (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  refine ⟨B ∘ₗ s, fun k x g => ?_, ⟨⟨_, Finsupp.single 1 1, rfl⟩, ?_⟩⟩
  · have e1 : A (s ((LinearMap.mulLeft ℂ (ρ.ρ (ι k))).restrict (hst (ι k)) x)) = A ((s x).mapDomain (ι k * ·)) :=
      (hs' _).trans (((hA (ι k) (s x)).trans (congrArg (ρ.ρ (ι k) * ·) (hs' x))).symm)
    refine (congrArg (fun z : cuspForms E r => z.1 g) (hAB _ _ e1)).trans ?_
    change _ = (B (s x)).1 _
    rw [hB, hB,
      Finsupp.sum_mapDomain_index (h := fun (k' : KA E r) c => c * φ.1 (g * (k' : GA E r))) (fun _ => zero_mul _)
        (fun _ _ _ => add_mul _ _ _)]
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rfl
  · rw [LinearMap.comp_apply, hAB _ (Finsupp.single 1 1) (hs' _)]
    refine Subtype.ext (funext fun g => ?_)
    rw [hB, Finsupp.sum_single_index (zero_mul _)]
    simp

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem finSpace (ρ : Typ E r) (B : ℝ) : ∃ W : Submodule ℂ (cuspForms E r), FiniteDimensional ℂ W ∧
    ∀ (S) (b : Blo S r), Killed ρ.ρ b.f.1 → (∀ τ i, ‖b.Λ τ i‖ ≤ B) → (⟨b.f.1, b.cusp⟩ : cuspForms E r) ∈ W := by
  obtain ⟨Bf, hB, hsym, d, e, ε, hε, horth, -⟩ := UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact E r
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> rw [h] <;> norm_num
  have hc : casimir e ε ∈ Subalgebra.center ℝ _ := casimir_mem_center hε2 horth hsym fun X Y Z => by
    rw [hB, hB, C.trForm, C.trForm, ← map_neg]
    congr 1
    exact trInv (R := mixedEmbedding.mixedSpace E) (X : ArchMatrix E r) (Y : ArchMatrix E r) (Z : ArchMatrix E r)
  have hc' : ((1 : ℂ) ⊗ₜ[ℝ] casimir e ε : UC E r) ∈ Subalgebra.center ℂ (UC E r) := by
    rw [Subalgebra.mem_center_iff]
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm c, Subalgebra.mem_center_iff.1 hc x]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  obtain ⟨κ, hκ, hκ'⟩ := cenScalar _ hc'
  obtain ⟨c, hcb⟩ := (isCompact_closedBall (0 : (E →+* ℂ) → Fin r → ℂ) (max B 0)).exists_bound_of_continuousOn hκ.continuousOn
  let ι : AdelicGLn.integralFiniteGL E r →* KA E r :=
    { toFun := fun k => ⟨finEmb E r k, finEmb_mem_maxCompact k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hι : Continuous ι := (continuous_finEmb.comp continuous_subtype_val).subtype_mk _
  obtain ⟨U, hU, hUρ⟩ := openKer (ρ.ρ.comp ι) (ρ.cont.comp hι)
  obtain ⟨X, τ, hX⟩ := typeMap ρ
  refine ⟨_, C.nearFinite E r (Fin d) e ε hε2 (fun i j => by rw [← hB, horth]) U hU X τ c, fun S b hk hb =>
    Submodule.subset_span ⟨fun s x => ?_, fun u hu g => ?_, hX _ hk, (smEq E r b.f).2, κ b.Λ, ?_, ?_⟩⟩
  · have := b.cen (Real.log s) x
    simpa only [zt, Real.exp_log s.2] using this
  · have h1 := hk (Finsupp.single (ι u) 1 - Finsupp.single 1 1) (by
      change Finsupp.linearCombination ℂ ρ.ρ _ = 0
      rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_one,
        show ρ.ρ (ι u) = 1 from hUρ u hu, sub_self]) g
    rw [Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
      Finsupp.sum_single_index (zero_mul _), one_mul, one_mul, sub_eq_zero] at h1
    rw [OneMemClass.coe_one, mul_one] at h1
    exact h1
  · have h1 := hcb b.Λ (by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      intro τ
      rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      exact fun i => (hb τ i).trans (le_max_left _ _))
    exact (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
  · have h1 := hκ' b.f b.Λ b.inf
    rw [uC_tmul, one_smul] at h1
    have h2 := congrArg (smEq E r) h1
    rw [smEq_uTC, map_smul] at h2
    exact h2

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.nearBlo :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.NearBlo E := by
  classical
  intro E _ _ _ S r ρ B
  obtain ⟨W, hW, hmem⟩ := finSpace ρ B
  let I := ((E →+* ℂ) × ℂ) ⊕ ({w : Pl E // w ∉ S} × Fin (r + 1))
  let T : I → Module.End ℂ (Sm E r) := Sum.elim (fun p => cap p.1 p.2) fun p => hk r p.1.1 p.2
  let lam : (((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ)) → I → ℂ := fun q =>
    Sum.elim (fun p => ∏ i, (p.2 + q.1 p.1 i)) fun p =>
      (qc p.1.1 ^ ((((p.2 : ℕ) : ℂ) * ((r : ℂ) - (p.2 : ℕ))) / 2))⁻¹ * GlobalTheory.LFun.satEig (Formalism.UG.qV E p.1.1) r (q.2 p.1.1) p.2
  set P := {p : ((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ) | ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧ (∀ τ i, ‖b.Λ τ i‖ ≤ B) ∧
    p.1 = b.Λ ∧ ∀ w, p.2 w = if w ∈ S then 0 else b.sat w} with hP
  have heig : ∀ (q) (b : Blo S r), q.1 = b.Λ → (∀ w, q.2 w = if w ∈ S then 0 else b.sat w) → ∀ i, T i b.f = lam q i • b.f := by
    rintro q b h1 h2 (⟨τ, u⟩ | ⟨⟨w, hw⟩, j⟩)
    · change cap τ u b.f = (∏ i, (u + q.1 τ i)) • b.f
      rw [h1, b.inf]
    · change hk r w j b.f = (_ * GlobalTheory.LFun.satEig _ r (q.2 w) j) • b.f
      rw [(hkOps E r w j).1, (b.isSat w hw).2.2.2 _ (GlobalTheory.LFun.exists_isUnifV w).choose_spec j (Nat.lt_succ_iff.1 j.2), smul_smul,
        h2, if_neg hw]
  have himg : (lam '' P).Finite := by
    have hex : ∀ x : lam '' P, ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧ (∀ τ i, ‖b.Λ τ i‖ ≤ B) ∧ ∀ i, T i b.f = x.1 i • b.f := by
      rintro ⟨_, q, ⟨b, h1, h2, h3, h4⟩, rfl⟩
      exact ⟨b, h1, h2, heig q b h3 h4⟩
    choose b h1 h2 h3 using hex
    have li := indep T (fun x => (b x).f) (fun x : lam '' P => x.1) (fun x => (b x).ne) h3 Subtype.val_injective
    have li2 : LinearIndependent ℂ fun x : lam '' P => (⟨⟨(b x).f.1, (b x).cusp⟩, hmem S (b x) (h1 x) (h2 x)⟩ : W) :=
      LinearIndependent.of_comp ((cuspForms E r).subtype ∘ₗ W.subtype) (li.map' (Sm E r).subtype (Submodule.ker_subtype _))
    exact Set.finite_coe_iff.1 li2.finite
  refine Set.Finite.of_finite_fibers lam himg ?_
  rintro _ ⟨q, ⟨b, -, -, h3, h4⟩, rfl⟩
  refine ((Set.Finite.pi' fun τ => Set.Finite.pi' fun _ : Fin r => Set.finite_range (q.1 τ)).prod
    (Set.finite_singleton q.2)).subset ?_
  rintro q' ⟨⟨b', -, -, h3', h4'⟩, he⟩
  have he : lam q' = lam q := he
  refine ⟨fun τ i => ?_, funext fun w => ?_⟩
  · have h : ∏ k, (-q'.1 τ i + q'.1 τ k) = ∏ k, (-q'.1 τ i + q.1 τ k) := congrFun he (Sum.inl (τ, -q'.1 τ i))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (neg_add_cancel _), eq_comm, Finset.prod_eq_zero_iff] at h
    obtain ⟨k, -, hk⟩ := h
    exact ⟨k, (neg_add_eq_zero.1 hk).symm⟩
  · by_cases hw : w ∈ S
    · rw [h4, h4', if_pos hw, if_pos hw]
    · have c1 : (q'.2 w).card = r := by rw [h4', if_neg hw]; exact (b'.isSat w hw).2.2.1
      have c2 : (q.2 w).card = r := by rw [h4, if_neg hw]; exact (b.isSat w hw).2.2.1
      have hq : Formalism.UG.qV E w ≠ 0 := GlobalTheory.LFun.qV_ne_zero w
      refine GlobalTheory.LFun.eq_of_satEig_eq hq c1 c2 fun j hj => ?_
      have h := congrFun he (Sum.inr (⟨w, hw⟩, ⟨j, Nat.lt_succ_iff.2 hj⟩))
      exact mul_left_cancel₀ (inv_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hq)))) h
