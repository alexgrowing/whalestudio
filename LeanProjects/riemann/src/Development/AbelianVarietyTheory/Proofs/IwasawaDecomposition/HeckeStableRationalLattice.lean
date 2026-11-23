import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistSideFormsLeSpanGoodLiftForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.HeckeLat

theorem exists_integral_functional {O K V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V) (hN : N.FG)
    (v : V) (hv : v ≠ 0) (hp : ∀ c : K, c • v ∈ N → ∃ o : O, algebraMap O K o = c) :
    ∃ r : V →ₗ[K] K, r v = 1 ∧ ∀ n ∈ N, ∃ o : O, algebraMap O K o = r n := by
  let q : V →ₗ[K] V ⧸ (K ∙ v) := (K ∙ v).mkQ
  let N' : Submodule O (V ⧸ (K ∙ v)) := N.map (q.restrictScalars O)
  haveI : Module.Finite O N' := Module.Finite.iff_fg.mpr (hN.map _)
  haveI : Module.IsTorsionFree O (V ⧸ (K ∙ v)) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hk : algebraMap O K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hr.ne_zero
    have h : r • x = r • y := hxy
    rw [← algebraMap_smul K r, ← algebraMap_smul K r] at h
    exact smul_right_injective _ hk h
  haveI : Module.Free O N' := Module.free_of_finite_type_torsion_free'
  let e := Module.finBasis O N'
  have hli : LinearIndependent K (fun i => ((e i : N') : V ⧸ (K ∙ v))) :=
    (LinearIndependent.iff_fractionRing O K).mp (e.linearIndependent.map' N'.subtype (Submodule.ker_subtype _))
  choose m hm hq using fun i => (e i).2
  have hq' : ∀ i, q (m i) = e i := hq
  have hqv : q v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v)
  have hnot : v ∉ Submodule.span K (Set.range m) := by
    intro h
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
    have h0 : ∑ i, a i • ((e i : N') : V ⧸ (K ∙ v)) = 0 := by
      have h1 := congrArg q ha
      rw [map_sum, hqv] at h1
      simpa only [map_smul, hq'] using h1
    have := Fintype.linearIndependent_iff.mp hli a h0
    apply hv
    rw [← ha]
    simp [this]
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
  have hfm : ∀ i, f (m i) = 0 := fun i => hker (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨(f v)⁻¹ • f, by simp [hf], fun n hn => ?_⟩
  let n' : N' := ⟨q n, n, hn, rfl⟩
  have h1 : q (n - ∑ i, e.repr n' i • m i) = 0 := by
    have h2 : (n' : V ⧸ (K ∙ v)) = ∑ i, e.repr n' i • ((e i : N') : V ⧸ (K ∙ v)) := by
      have h3 := congrArg Subtype.val (e.sum_repr n')
      rw [Submodule.coe_sum] at h3
      exact h3.symm
    rw [map_sub, map_sum, sub_eq_zero]
    refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [q.map_smul_of_tower, hq']
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp h1)
  obtain ⟨o, ho⟩ := hp c (by
    rw [hc]
    exact N.sub_mem hn (N.sum_mem fun i _ => N.smul_mem _ (hm i)))
  refine ⟨o, ?_⟩
  have h3 := congrArg f hc
  rw [map_sub, map_sum, map_smul] at h3
  simp only [f.map_smul_of_tower, hfm, smul_zero, Finset.sum_const_zero, sub_zero, smul_eq_mul] at h3
  rw [ho, LinearMap.smul_apply, ← h3, smul_eq_mul]
  field_simp

theorem exists_integral_reading {LL : Type} [Field LL] [NumberField LL] (L0 : IntermediateField ℚ LL) {O K : Type}
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] (rd : L0 →+* K) :
    ∃ lam : LL →+ K, lam 1 = 1 ∧ (∀ (c : L0) (y : LL), lam ((c : LL) * y) = rd c * lam y) ∧
      ∀ a : 𝓞 LL, ∃ o : O, algebraMap O K o = lam a := by
  letI : Algebra L0 (AlgebraicClosure K) := ((algebraMap K (AlgebraicClosure K)).comp rd).toAlgebra
  haveI : Module.IsTorsionFree L0 (AlgebraicClosure K) := DivisionSemiring.to_moduleIsTorsionFree
  let ι : LL →ₐ[L0] AlgebraicClosure K := IsAlgClosed.lift
  let B := RingOfIntegers.basis LL
  let N : Submodule O (AlgebraicClosure K) := Submodule.span O (Set.range fun i => ι (B i : LL))
  have hint : ∀ a : 𝓞 LL, IsIntegral O (ι (a : LL)) := fun a =>
    ((RingOfIntegers.isIntegral_coe a).map (ι.toRingHom.toIntAlgHom)).tower_top
  have hN : ∀ n ∈ N, IsIntegral O n := by
    have : N ≤ (integralClosure O (AlgebraicClosure K)).toSubmodule := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hint _
    exact fun n hn => this hn
  have hmem : ∀ a : 𝓞 LL, ι (a : LL) ∈ N := by
    intro a
    rw [← B.sum_repr a]
    push_cast
    rw [map_sum]
    refine N.sum_mem fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (B i : LL)) i)) _
  obtain ⟨r, hr1, hr⟩ := exists_integral_functional (K := K) N (Submodule.fg_span (Set.finite_range _)) 1 one_ne_zero (by
    intro c hc
    have h := hN _ hc
    rw [← Algebra.algebraMap_eq_smul_one, isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective] at h
    exact IsIntegrallyClosed.isIntegral_iff.mp h)
  refine ⟨r.toAddMonoidHom.comp ι.toRingHom.toAddMonoidHom, ?_, fun c y => ?_, fun a => hr _ (hmem a)⟩
  · change r (ι 1) = 1
    rw [map_one, hr1]
  · change r (ι ((c : LL) * y)) = rd c * r (ι y)
    have h : ι (c : LL) = algebraMap K (AlgebraicClosure K) (rd c) := ι.commutes c
    rw [map_mul, h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem mem_span_solutions {R O : Type} [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O] {ι κ : Type} [Fintype ι]
    [Fintype κ] (A : ι → κ → R) (o : ι → O) (ho : ∀ k, ∑ t, o t * algebraMap R O (A t k) = 0) :
    o ∈ Submodule.span O {x : ι → O | ∃ c : ι → R, (∀ k, ∑ t, c t * A t k = 0) ∧ x = fun t => algebraMap R O (c t)} := by
  classical
  let g : (ι → R) →ₗ[R] (κ → R) := (Matrix.of A).vecMulLinear
  have hg : ∀ c k, g c k = ∑ t, c t * A t k := fun c k => rfl
  have hex := Module.Flat.lTensor_exact O (LinearMap.exact_subtype_ker_map g)
  have hcomp : ∀ z : O ⊗[R] (ι → R), ∀ k, TensorProduct.piScalarRight R O O κ (g.lTensor O z) k =
      ∑ t, TensorProduct.piScalarRight R O O ι z t * algebraMap R O (A t k) := by
    intro z k
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, hg,
        Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_mul, Finset.sum_add_distrib]
  obtain ⟨z, rfl⟩ := (TensorProduct.piScalarRight R O O ι).surjective o
  have hz : g.lTensor O z = 0 := by
    apply (TensorProduct.piScalarRight R O O κ).injective
    funext k
    rw [hcomp, ho, map_zero, Pi.zero_apply]
  obtain ⟨y, rfl⟩ := (hex z).mp hz
  clear hz ho
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    have : TensorProduct.piScalarRight R O O ι ((LinearMap.ker g).subtype.lTensor O (a ⊗ₜ c)) =
        a • fun t => algebraMap R O (c.1 t) := by
      funext t
      simp [Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c.1, fun k => congrFun c.2 k, rfl⟩)
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

theorem exists_integral_descent {LL : Type} [Field LL] [NumberField LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks]
    [Algebra Ks LL] (kKs : Ks →+* L0) (hk : ∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x)
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL) (hb : ∀ i, bs i ∈ WK) (hKi : LinearIndependent Ks bs)
    (hKs : Submodule.span Ks (Set.range bs) = WK) (hLi : LinearIndependent LL bs)
    (hLs : Submodule.span LL (Set.range bs) = ⊤) {O K : Type}
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
    (rd : L0 →+* K) (hrd : ∀ s, algebraMap Ks K s = rd (kKs s)) :
    ∃ Φ : WL →+ K ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange K fr (Φ x)) ∧
      (∀ w : WK, Φ (w : WL) = (1 : K) ⊗ₜ[Ks] w) ∧
      (∀ (a : 𝓞 LL) (w : WK), ∃ o : O, Φ ((a : LL) • (w : WL)) = algebraMap O K o • ((1 : K) ⊗ₜ[Ks] w)) ∧
      (∀ c : 𝓞 L0, ∃ o : O, algebraMap O K o = rd c) ∧
      ∃ W0 : AddSubgroup WL, (∀ w : WK, (w : WL) ∈ W0) ∧ (∀ (c : L0), ∀ x ∈ W0, (c : LL) • x ∈ W0) ∧
        ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → κ → WL), (∀ t a, v t a ∈ W0) → ∀ o : ι → O,
          (∀ a, ∑ t, algebraMap O K (o t) • Φ (v t a) = 0) →
          o ∈ Submodule.span O {x : ι → O | ∃ c : ι → 𝓞 L0, (∀ a, ∑ t, ((c t : L0) : LL) • v t a = 0) ∧
            ∀ t, algebraMap O K (x t) = rd (c t)} := by
  obtain ⟨lam, hl1, hlx, hlint⟩ := exists_integral_reading (O := O) L0 rd
  have hl0 : ∀ c : L0, lam c = rd c := fun c => by simpa [hl1] using hlx c 1
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ K ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, lam (B.repr x k) • ((1 : K) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, lam (B.repr x k) • ((1 : K) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add, add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have hco : ∀ w : WK, ∃ s : Fin n → Ks, w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) ∧
      ∀ (l : LL) k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
    intro w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    refine ⟨s, by apply Subtype.ext; simp [hs], fun l k => ?_⟩
    have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
      rw [← hs, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hB, mul_smul, algebraMap_smul]
    rw [this, B.repr_sum_self]
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = lam l • ((1 : K) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hw, hrep⟩ := hco w
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hlx, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul K (s k), smul_smul, mul_comm]
  have hint : ∀ c : 𝓞 L0, ∃ o : O, algebraMap O K o = rd c := fun c =>
    IsIntegrallyClosed.isIntegral_iff.mp ((RingOfIntegers.isIntegral_coe c).map rd.toIntAlgHom).tower_top
  refine ⟨Φ, ?_, ?_, ?_, ?_, hint, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hlx, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hl1, one_smul] at this
    exact this
  · intro a w
    obtain ⟨o, ho⟩ := hlint a
    exact ⟨o, by rw [key, ho]⟩
  refine ⟨{ carrier := {x | ∀ k, B.repr x k ∈ L0}
            add_mem' := fun hx hy k => by rw [map_add, Finsupp.add_apply]; exact add_mem (hx k) (hy k)
            zero_mem' := fun k => by rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
            neg_mem' := fun hx k => by rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx k) }, ?_, ?_, ?_⟩
  · intro w k
    obtain ⟨s, -, hrep⟩ := hco w
    have := hrep 1 k
    rw [one_smul, one_mul, ← hk] at this
    rw [this]
    exact (kKs (s k)).2
  · intro c x hx k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem c.2 (hx k)
  intro ι κ _ _ v hv o ho
  let α : ι × κ × Fin n → L0 := fun p => ⟨B.repr (v p.1 p.2.1) p.2.2, hv p.1 p.2.1 p.2.2⟩
  have hα : ∀ t a k, B.repr (v t a) k = (α (t, a, k) : LL) := fun _ _ _ => rfl
  have hli : LinearIndependent K fun k => ((1 : K) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK) : K ⊗[Ks] WK) := by
    have h1 : LinearIndependent Ks fun k => (⟨bs k, hb k⟩ : WK) := LinearIndependent.of_comp WK.subtype hKi
    have h2 : ⊤ ≤ Submodule.span Ks (Set.range fun k => (⟨bs k, hb k⟩ : WK)) := by
      intro w _
      obtain ⟨s, hw, -⟩ := hco w
      rw [hw]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have h3 := ((Module.Basis.mk h1 h2).baseChange K).linearIndependent
    convert h3 using 1
    funext k
    simp
  have hrel : ∀ a k, ∑ t, algebraMap O K (o t) * rd (α (t, a, k)) = 0 := by
    intro a
    refine Fintype.linearIndependent_iff.mp hli _ ?_
    rw [← ho a]
    simp only [hΦ, hα, hl0, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  choose s0 hs0 using hint
  have hinj := IsFractionRing.injective O K
  let s : 𝓞 L0 →+* O :=
    { toFun := s0
      map_one' := hinj (by rw [hs0]; simp)
      map_mul' := fun x y => hinj (by rw [map_mul, hs0, hs0, hs0]; simp)
      map_zero' := hinj (by rw [hs0]; simp)
      map_add' := fun x y => hinj (by rw [map_add, hs0, hs0, hs0]; simp) }
  letI : Algebra (𝓞 L0) O := s.toAlgebra
  have hs : ∀ c : 𝓞 L0, algebraMap O K (algebraMap (𝓞 L0) O c) = rd c := hs0
  have hsinj : Function.Injective (algebraMap (𝓞 L0) O) := by
    intro x y hxy
    have := congrArg (algebraMap O K) hxy
    rw [hs, hs] at this
    exact RingOfIntegers.ext (rd.injective this)
  haveI : FaithfulSMul (𝓞 L0) O := (faithfulSMul_iff_algebraMap_injective _ _).mpr hsinj
  haveI : Module.IsTorsionFree (𝓞 L0) O := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.Flat (𝓞 L0) O := inferInstance
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L0)) α
  choose A hA using hd
  have hA' : ∀ p, (A p : L0) = ((d : 𝓞 L0) : L0) * α p := fun p => (hA p).trans (Algebra.smul_def _ _)
  have hd0 : ((d : 𝓞 L0) : L0) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero d)
  have hsol := mem_span_solutions (fun t (q : κ × Fin n) => A (t, q)) o (by
    rintro ⟨a, k⟩
    apply hinj
    simp only [map_sum, map_mul, hs, hA', map_zero]
    have := congrArg (rd ((d : 𝓞 L0) : L0) * ·) (hrel a k)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => by ring)
  refine Submodule.span_mono ?_ hsol
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, fun a => B.repr.injective (Finsupp.ext fun k => ?_), fun t => hs _⟩
  have h1 := congrArg (fun z : 𝓞 L0 => (z : L0)) (hc (a, k))
  simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, map_zero] at h1
  simp only [← RingOfIntegers.coe_eq_algebraMap, hA'] at h1
  have h2 : ∑ t, (c t : L0) * α (t, a, k) = 0 := by
    apply mul_left_cancel₀ hd0
    rw [mul_zero, ← h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  have h3 := congrArg (fun z : L0 => (z : LL)) h2
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul, hα, map_zero, Finsupp.zero_apply]
  simpa using h3

theorem normV_isUnit (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (w : PlE D.host) (hw : w ∉ T.S0 i) :
    IsUnit ((normV w : ℕ) : T.O i) := by
  classical
  have hl : (T.l i).Prime := (T.lPrime i).out
  have hN : ¬ (T.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : T.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    refine hw (T.twistExcludedPlaces_contains_residueChar i ?_)
    show ((T.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[T.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := (hu.map (algebraMap ℤ_[T.l i] (T.O0 i))).map (algebraMap (T.O0 i) (T.O i))
  rwa [map_natCast, map_natCast] at this

theorem hL_goodL (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hkP : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ In.Sb) (y : S.WL j) (hy : y ∈ goodL D S In.θ j) :
    In.hL j k P y ∈ goodL D S In.θ j := by
  refine (In.span j h1 h2).trans (b := _) (c := (goodL D S In.θ j).comap (In.hL j k P)) ?_ hy
  refine iSup₂_le fun σ _ z hz => ?_
  have hz2 := hz.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hz2
  rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.mp (hz2 k P hkP)]
  exact Submodule.smul_mem _ _ hz.1

def eqL (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    Option ↥(Formalism.IndefR.NX.U D.nd) → Module.End D.what₂.LL (S.WL j)
  | none => (∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) - 1
  | some u => actL D S j u - (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • 1

theorem mem_goodL_iff (D : D7) (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ)
    (y : S.WL j) : y ∈ goodL D S θ j ↔ ∀ a, eqL D S θ j a y = 0 := by
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf, Option.forall]
  simp only [Module.End.mem_eigenspace_iff, eqL, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero, one_smul]

def eqT (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool) :
    Option ↥(Formalism.IndefR.NX.U D.nd) → Module.End (FractionRing (T.O i)) (FmT D T S i j b)
  | none => eGT D T S In.rho In.chi i j b - 1
  | some u => (actGT D T S In.rho In.chi i j b u).toLinearMap -
      readT D T i b ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0) • 1

theorem eqL_rational (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (W0 : AddSubgroup (S.WL j)) (hW : ∀ w : ↥(WKr D S j), (w : S.WL j) ∈ W0)
    (hc : ∀ (c : ↥D.LL0), ∀ x ∈ W0, (c : D.what₂.LL) • x ∈ W0) (a : Option ↥(Formalism.IndefR.NX.U D.nd)) (w : ↥(WKr D S j)) :
    eqL D S In.θ j a w ∈ W0 := by
  have hact : ∀ g, actL D S j g w ∈ W0 := by
    intro g
    have e1 : actL D S j g w = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
        (S.A j).ρ (S.eG.symm g) w := by
      simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
    rw [e1]
    exact hc _ _ (hW ⟨_, stabR D S In.rho j _ _ w.2⟩)
  cases a with
  | none =>
    haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
    simp only [eqL, finsum_eq_sum_of_fintype, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact sub_mem (sum_mem fun g _ => hc _ _ (hact g)) (hW w)
  | some u =>
    simp only [eqL, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact sub_mem (hact u) (hc _ _ (hW w))

local instance algOKT (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) : Algebra (T.O i) (KT D T i b) :=
  inferInstanceAs (Algebra (T.O i) (FractionRing (T.O i)))

local instance fracKT (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool) : IsFractionRing (T.O i) (KT D T i b) :=
  inferInstanceAs (IsFractionRing (T.O i) (FractionRing (T.O i)))

theorem descend_integral (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ Φ : S.WL j →+ FmT D T S i j b, (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) ∧
      (∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x)) ∧
      (∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w) ∧
      (∀ (a : 𝓞 D.what₂.LL) (w : ↥(WKr D S j)), ∃ o : T.O i, Φ ((a : D.what₂.LL) • (w : S.WL j)) = o • Φ w) ∧
      ∃ W0 : AddSubgroup (S.WL j), (∀ w : ↥(WKr D S j), (w : S.WL j) ∈ W0) ∧
        (∀ (c : ↥D.LL0), ∀ x ∈ W0, (c : D.what₂.LL) • x ∈ W0) ∧
        ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → κ → S.WL j), (∀ t a, v t a ∈ W0) → ∀ o : ι → T.O i,
          (∀ a, ∑ t, o t • Φ (v t a) = 0) →
          o ∈ Submodule.span (T.O i) {x : ι → T.O i | ∃ c : ι → 𝓞 ↥D.LL0,
            (∀ a, ∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • v t a = 0) ∧
            ∀ t, algebraMap (T.O i) (FractionRing (T.O i)) (x t) = readT D T i b (c t)} := by
  obtain ⟨n, bs, hb, hKi, hKs, hLi, hLs⟩ := In.ks j h1 h2
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  obtain ⟨Φ, p1, p2, p3, p4, -, p5⟩ := exists_integral_descent D.LL0 S.kKs S.kKs_spec (WKr D S j) bs (fun k => hW ▸ hb k) hKi
    (hW ▸ hKs) hLi hLs (O := T.O i) (K := KT D T i b) (readK D T i b) (fun s => rfl)
  refine ⟨Φ, p1, p2, p3, fun a w => ?_, p5⟩
  obtain ⟨o, ho⟩ := p4 a w
  refine ⟨o, ho.trans ?_⟩
  rw [← p3]
  rfl

end GlobalTheory.HeightCounting.HeckeLat

open GlobalTheory.HeightCounting.HeckeLat in

theorem GlobalTheory.HeightCounting.FormsStep.hkStab_all : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P ⟨h1, h2, hk1, hk2, hsp, hP⟩ x hx
  obtain ⟨Φ, hc, hf, hw, hint, W0, hW0, hW0c, hrel⟩ := descend_integral D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  have hPb : P ∉ In.Sb := fun h => hP (by
    rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
    exact Or.inr (Finset.mem_coe.mpr (hSb h)))
  have hMW : ∀ y ∈ (S.A j).MK, y ∈ WKr D S j := fun y hy => by
    rw [WKr_of D S h1 h2]; exact hy.1

  have hML : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), Φ y ∈ BsupT D T S i j b := by
    have key : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), ∀ a : 𝓞 D.what₂.LL,
        Φ (a • y) ∈ BsupT D T S i j b := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        obtain ⟨o, ho⟩ := hint a ⟨y, hMW y hy⟩
        rw [← algebraMap_smul D.what₂.LL a y]
        refine ho ▸ Submodule.smul_mem _ o ?_
        exact Submodule.subset_span ⟨⟨y, hMW y hy⟩, hy, hw _⟩
      | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro a; rw [smul_add, map_add]; exact add_mem (hy a) (hz a)
      | smul a' y _ hy => intro a; rw [smul_smul]; exact hy _
    intro y hy
    simpa using key y hy 1
  have hhr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  have hkΦ : ∀ y, hkT D T S In i j b k P (Φ y) = ((cHkT D T i b P : T.O i) ^ k) • Φ (In.hL j k P y) := by
    intro y
    rw [← algebraMap_smul (FractionRing (T.O i)), map_pow, hf _ _ hhr]
    rfl
  obtain ⟨n, hn⟩ := In.hL_int j k P h1 h2 hsp hPb hk2
  obtain ⟨u, hu⟩ := (normV_isUnit D T i P hP).pow n
  have hstep : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), y ∈ goodL D S In.θ j →
      hkT D T S In i j b k P (Φ y) ∈ BI D T S In i j b := by
    intro y hy hg
    rw [hkΦ]
    refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
    · have h3 := hML _ (hn y hy hg)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (T.O i), Nat.cast_pow, ← hu] at h3
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : T.O i) h3
      rwa [smul_smul, Units.inv_mul, one_smul] at h4
    · exact descend_mem_V0T D T S In i j b Φ hc ha he _ (hL_goodL D S In j k P h1 h2 ⟨hk1, hk2, hsp, hPb⟩ y hg)
  have hET : ∀ a y, Φ (eqL D S In.θ j a y) = eqT D T S In i j b a (Φ y) := by
    intro a y
    cases a with
    | none => simp only [eqL, eqT, LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    | some u =>
      simp only [eqL, eqT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, ha, hc,
        LinearEquiv.coe_coe]
  have hx0 : ∀ a, eqT D T S In i j b a x = 0 := by
    intro a
    have h3 := goodTwistSideForms_le_span_goodLiftForms D S In T i j b h1 h2 (eIdem_all D) Φ hc ha he hw hx.2
    refine (Submodule.span_le (p := LinearMap.ker (eqT D T S In i j b a))).mpr ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hET, (mem_goodL_iff D S In.θ j y).mp hy a, map_zero]
  obtain ⟨m, o, g, rfl⟩ := Submodule.mem_span_set'.mp hx.1
  choose w hwM hwg using fun t => (g t).2
  have hg : ∀ t, (g t : FmT D T S i j b) = Φ (w t) := fun t => (hwg t).trans (hw _).symm
  simp only [hg] at hx0 ⊢
  haveI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hsol := hrel (fun t a => eqL D S In.θ j a (w t)) (fun t a => eqL_rational D S In j h1 h2 W0 hW0 hW0c a (w t)) o (by
    intro a
    rw [← hx0 a, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hET, LinearMap.map_smul_of_tower])
  clear hx0 hx
  induction hsol using Submodule.span_induction with
  | mem o ho =>
    obtain ⟨c, hc0, hco⟩ := ho
    have h3 : ∑ t, o t • Φ (w t) = Φ (∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • (w t : S.WL j)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc, ← hco, algebraMap_smul]
    rw [h3]
    refine hstep _ (Submodule.sum_mem _ fun t _ => ?_) ((mem_goodL_iff D S In.θ j _).mpr fun a => ?_)
    · let a : 𝓞 D.what₂.LL := ⟨((c t : ↥D.LL0) : D.what₂.LL),
        (RingOfIntegers.isIntegral_coe (c t)).map (algebraMap ↥D.LL0 D.what₂.LL).toIntAlgHom⟩
      have h4 := Submodule.smul_mem _ a (Submodule.subset_span (R := 𝓞 D.what₂.LL) (s := ((S.A j).MK : Set (S.WL j))) (hwM t))
      rwa [← algebraMap_smul D.what₂.LL a] at h4
    · rw [map_sum]
      simpa only [map_smul] using hc0 a
  | zero => simp
  | add o o' _ _ ho ho' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
    exact add_mem ho ho'
  | smul r o _ ho =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ ho
