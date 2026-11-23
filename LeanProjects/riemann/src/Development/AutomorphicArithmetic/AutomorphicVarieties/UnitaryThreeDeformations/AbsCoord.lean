import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LengthLeCotLenOfInjectiveTangentMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsWeightedEquationsPresentingKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsCoverWithDistinctOrbitRepresentatives
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.SmoothPtWeightedGradedAlgebraBasePoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.SpansCotOfLinearTermsNondegenerate
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.IsWRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

namespace UpperTheory.V.UnitaryThreeInertia.Abs

section Transfer

variable {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) [Field K] [Algebra O K]

private theorem ex_pt (ξ : FA O W.wt →ₐ[O] K) (h : OnS (RingHom.ker (toA W)) ξ) :
    ∃ ξ' : W.A →ₐ[O] K, ∀ f, ξ' (toA W f) = ξ f := by
  have h' : ∀ f ∈ RingHom.ker (toA W), ξ f = 0 := h
  let e := Ideal.quotientKerAlgEquivOfSurjective (toA_surjective W)
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker (toA W)) ξ h').comp e.symm.toAlgHom, fun f => ?_⟩
  have hf : e.symm (toA W f) = Ideal.Quotient.mk (RingHom.ker (toA W)) f := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  show Ideal.Quotient.liftₐ (RingHom.ker (toA W)) ξ h' (e.symm (toA W f)) = ξ f
  rw [hf]
  rfl

private theorem ex_der (D : FA O W.wt →ₗ[O] K) (h : ∀ f ∈ RingHom.ker (toA W), D f = 0) :
    ∃ D' : W.A →ₗ[O] K, ∀ f, D' (toA W f) = D f := by
  have hle : LinearMap.ker (toA W).toLinearMap ≤ LinearMap.ker D := by
    intro f hf
    exact LinearMap.mem_ker.2 (h f (RingHom.mem_ker.2 (LinearMap.mem_ker.1 hf)))
  let e := (toA W).toLinearMap.quotKerEquivOfSurjective (toA_surjective W)
  refine ⟨((LinearMap.ker (toA W).toLinearMap).liftQ D hle).comp e.symm.toLinearMap, fun f => ?_⟩
  have hf : e.symm (toA W f) = Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf, Submodule.liftQ_apply]

private theorem zero_iff (ξ : FA O W.wt →ₐ[O] K) (ξ' : W.A →ₐ[O] K) (h : ∀ f, ξ' (toA W f) = ξ f) (j : ℤ) :
    (∀ f ∈ Fgr O W.wt j, ξ f = 0) ↔ ∀ x (hx : x ∈ W.part j), ξ' ⟨x, W.part_le_A hx⟩ = 0 := by
  constructor
  · intro hz x hx
    obtain ⟨f, hf, hf2⟩ := exists_toA W hx
    have e := h f
    rw [hf2] at e
    exact e.trans (hz f hf)
  · intro hz f hf
    rw [← h f]
    exact hz _ (toA_mem W hf)

private theorem lin_zero (D : FA O W.wt →ₗ[O] K) (h : ∀ j, ∀ f ∈ Fgr O W.wt j, D f = 0) : D = 0 := by
  classical
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply, ← DirectSum.sum_support_decompose (Fgr O W.wt) f, map_sum]
  exact Finset.sum_eq_zero fun i _ => h i _ (SetLike.coe_mem _)

private theorem alg_ext (ξ ξ' : FA O W.wt →ₐ[O] K) (h : ∀ j, ∀ f ∈ Fgr O W.wt j, ξ f = ξ' f) : ξ = ξ' := by
  classical
  refine AlgHom.ext fun f => ?_
  rw [← DirectSum.sum_support_decompose (Fgr O W.wt) f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i _ (SetLike.coe_mem _)

end Transfer

theorem coord_count (hM : LemmaM) (hM' : LemmaM') (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
    (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ) (hv : IsNVal O K v)
    (R : Type) [CommRing R] [Algebra O R] (W : WPres O ℤ R) (h : W.HasOrigin)
    (𝒮 : ℤ → Submodule O R) [SetLike.GradedMonoid 𝒮] (h𝒮 : ∀ j, W.part j = 𝒮 j)
    (hwt : ∀ s, -2 ≤ W.wt s ∧ W.wt s ≤ 2)
    (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O) (hf : ∀ j i, f j i ∈ wtPart O W.wt j)
    (hker : RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)))
    (hb : ∀ j : ℤ, (b j : ℤ) + (if j = -1 then -1 else if j = 1 ∨ j = 2 then 1 else 0) ≤ Nat.card {i // W.wt i = j})
    (m1 : ∀ j : ℤ, j ≤ 0 → ∀ d : W.σ → O, (∀ i, W.wt i ≠ j → d i = 0) →
      (∀ f, W.π f = 0 → ∑ i, coeff (Finsupp.single i 1) f * d i = 0) → d = 0)
    (m2 : Module.Finite O (𝒮 0))
    (m3 : ∀ ξ : gradedSub 𝒮 →ₐ[O] K, (∀ j < 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) →
      (∀ j > 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) →
      ∀ j x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = algebraMap O K (W.origin h x))
    (m4 : ∀ ξ : gradedSub 𝒮 →ₐ[O] K, ¬ (∀ j < 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) →
      ¬ (∀ j > 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) →
      ∀ D ∈ PtDer ξ K, ∃ c : K, ∀ (j : ℤ) x (hx : x ∈ 𝒮 j), D ⟨x, le_iSup 𝒮 j hx⟩ = c * j * ξ ⟨x, le_iSup 𝒮 j hx⟩)
    (a : R) (ha : a ∈ 𝒮 0) (ha0 : W.origin h a = 0)
    (m5 : ∀ ξ : gradedSub 𝒮 →ₐ[O] K, ¬ (∀ j < 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) →
      ¬ (∀ j > 0, ∀ x (hx : x ∈ 𝒮 j), ξ ⟨x, le_iSup 𝒮 j hx⟩ = 0) → ξ ⟨a, le_iSup 𝒮 0 ha⟩ ≠ 0) :
    ∃ (n : ℕ) (ξ : Fin n → (gradedSub 𝒮 →ₐ[O] K)) (V : ℕ),
      (∀ i, ¬ (∀ j < 0, ∀ x (hx : x ∈ 𝒮 j), ξ i ⟨x, le_iSup 𝒮 j hx⟩ = 0) ∧
        ¬ (∀ j > 0, ∀ x (hx : x ∈ 𝒮 j), ξ i ⟨x, le_iSup 𝒮 j hx⟩ = 0)) ∧
      (∀ i i' (t : Kˣ), (∀ (j : ℤ) x (hx : x ∈ 𝒮 j),
        ξ i' ⟨x, le_iSup 𝒮 j hx⟩ = ((t ^ j : Kˣ) : K) * ξ i ⟨x, le_iSup 𝒮 j hx⟩) → i = i') ∧
      (∀ c : O, c ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M] (d : M →+ (W.σ → O ⧸ Ideal.span {c})),
        Function.Injective d → (∀ μ i, W.wt i ≠ -1 → d μ i = 0) →
        (∀ μ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d μ i = 0) → Module.length O M ≤ V) ∧
      (V : ℝ) ≤ 2 * ∑ i, v (ξ i ⟨a, le_iSup 𝒮 0 ha⟩) := by
  have e𝒮 : 𝒮 = W.part := (funext h𝒮).symm
  subst e𝒮
  have hle : gradedSub W.part ≤ W.A := by
    intro y hy
    have hy' : y ∈ ⨆ j, W.part j := hy
    exact (iSup_le fun j z hz => W.part_le_A hz : (⨆ j, W.part j) ≤ Subalgebra.toSubmodule W.A) hy'
  have negT : ∀ (ξ : FA O W.wt →ₐ[O] K) (ξ' : W.A →ₐ[O] K), (∀ g, ξ' (toA W g) = ξ g) →
      ((∀ j < 0, ∀ x (hx : x ∈ W.part j), (ξ'.comp (Subalgebra.inclusion hle)) ⟨x, le_iSup W.part j hx⟩ = 0) ↔
        NegZero (Fgr O W.wt) ξ) := by
    intro ξ ξ' h1
    exact forall_congr' fun j => imp_congr_right fun _ => (zero_iff W ξ ξ' h1 j).symm
  have posT : ∀ (ξ : FA O W.wt →ₐ[O] K) (ξ' : W.A →ₐ[O] K), (∀ g, ξ' (toA W g) = ξ g) →
      ((∀ j > 0, ∀ x (hx : x ∈ W.part j), (ξ'.comp (Subalgebra.inclusion hle)) ⟨x, le_iSup W.part j hx⟩ = 0) ↔
        PosZero (Fgr O W.wt) ξ) := by
    intro ξ ξ' h1
    exact forall_congr' fun j => imp_congr_right fun _ => (zero_iff W ξ ξ' h1 j).symm
  have hW : IsWRing (Fgr O W.wt) (x0 O W.wt) := by
    haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
    exact isWRing O (MvPowerSeries W.σ O) (WPres.free O W.wt)
      (fun g hg => by
        have hg0 : g = 0 := hg
        simp [hg0]) hwt
  have hcard0 : ∀ j, (j < -2 ∨ 2 < j) → Nat.card {i // W.wt i = j} = 0 := by
    intro j hj
    exact Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨i, hi⟩ => by
      have := hwt i
      omega⟩)
  have hbz : ∀ j, (j < -2 ∨ 2 < j) → b j = 0 := by
    intro j hj
    have := hb j
    rw [hcard0 j hj] at this
    split_ifs at this <;> omega
  by_cases hr0 : Nat.card {i // W.wt i = -1} = 0
  · refine ⟨0, Fin.elim0, 0, fun i => i.elim0, fun i => i.elim0, ?_, by simp⟩
    intro c hc M _ _ d hd hsupp _
    have : Subsingleton M := ⟨fun μ ν => hd (funext fun i => by
      by_cases hi : W.wt i = -1
      · exact absurd hr0 (Nat.card_ne_zero.2 ⟨⟨⟨i, hi⟩⟩, inferInstance⟩)
      · rw [hsupp μ i hi, hsupp ν i hi])⟩
    rw [Module.length_eq_zero]
    exact zero_le
  have hb1 := hb 1
  have hb2 := hb 2
  have hbm1 := hb (-1)
  have hbm2 := hb (-2)
  have hb0 := hb 0
  simp only [show (1 : ℤ) ≠ -1 by norm_num, show (2 : ℤ) ≠ -1 by norm_num, show (-2 : ℤ) ≠ -1 by norm_num,
    show (0 : ℤ) ≠ -1 by norm_num, show ¬((-2 : ℤ) = 1 ∨ (-2 : ℤ) = 2) by norm_num,
    show ¬((0 : ℤ) = 1 ∨ (0 : ℤ) = 2) by norm_num, true_or, or_true, if_true, if_false] at hb1 hb2 hbm1 hbm2 hb0
  obtain ⟨Q, hQ, hQrel⟩ := exists_weighted_equations_presenting_ker O R W h b f hf hker (Nat.card {i // W.wt i = -1}) (Nat.card {i // W.wt i = -2})
    (Nat.card {i // W.wt i = 1} - 1) (Nat.card {i // W.wt i = 2} - 1) (Nat.card {i // W.wt i = 0})
    (by omega) (by omega) (by omega) (by omega) (by omega) hbz
  have hmd : mDims (Nat.card {i // W.wt i = -1}) (Nat.card {i // W.wt i = -2})
      (Nat.card {i // W.wt i = 1} - 1) (Nat.card {i // W.wt i = 2} - 1) (Nat.card {i // W.wt i = 0}) =
      fun j => Nat.card {i // W.wt i = j} := by
    funext j
    unfold mDims
    split_ifs with h1 h2 h3 h4 h5
    · subst h1; rfl
    · subst h2; rfl
    · subst h3; omega
    · subst h4; omega
    · subst h5; rfl
    · exact (hcard0 j (by omega)).symm
  have hM1 : M1 Q := by
    refine ⟨by omega, hmd ▸ smoothPt_weightedGradedAlgebra_basePoint O W.σ W.wt, ?_, ?_, ?_⟩
    · exact spansCot_of_linear_terms_nondegenerate O W.σ W.wt (-1) _ Q.F Q.hF (fun k => hW.fixed (-1) (by norm_num) _ (Q.hF k))
        (fun d hd hk => m1 (-1) (by norm_num) d hd ((hQrel O d).1 hd hk))
    · exact spansCot_of_linear_terms_nondegenerate O W.σ W.wt (-2) _ Q.G Q.hG (fun k => hW.fixed (-2) (by norm_num) _ (Q.hG k))
        (fun d hd hk => m1 (-2) (by norm_num) d hd ((hQrel O d).2.1 hd hk))
    · exact spansCot_of_linear_terms_nondegenerate O W.σ W.wt 0 _ Q.Z (fun k => (Q.hZ k).1) (fun k => (Q.hZ k).2)
        (fun d hd hk => m1 0 le_rfl d hd ((hQrel O d).2.2 hd hk))
  have hM2 : M2 (Fgr O W.wt) Q.ideal := by
    haveI := m2
    unfold M2
    rw [hQ]
    let eq := Ideal.quotientKerAlgEquivOfSurjective (toA_surjective W)
    let φ : W.part 0 →ₗ[O] FA O W.wt ⧸ RingHom.ker (toA W) :=
      eq.symm.toLinearMap ∘ₗ
        LinearMap.codRestrict (Subalgebra.toSubmodule W.A) (W.part 0).subtype (fun y => W.part_le_A y.2)
    have key : Submodule.map (Ideal.Quotient.mkₐ O (RingHom.ker (toA W))).toLinearMap (Fgr O W.wt 0) =
        Submodule.map φ ⊤ := by
      apply le_antisymm
      · rintro y ⟨g, hg, rfl⟩
        refine ⟨⟨_, toA_mem W hg⟩, trivial, ?_⟩
        show eq.symm _ = _
        rw [AlgEquiv.symm_apply_eq]
        rfl
      · rintro y ⟨⟨z, hz⟩, -, rfl⟩
        obtain ⟨g, hg, hg2⟩ := exists_toA W hz
        refine ⟨g, hg, ?_⟩
        show _ = eq.symm _
        rw [eq_comm, AlgEquiv.symm_apply_eq]
        exact hg2.symm
    rw [key]
    exact Module.Finite.fg_top.map φ
  have hM3 : M3 (Fgr O W.wt) K (x0 O W.wt) Q.ideal := by
    intro x₁ hon hneg hpos hne1
    exfalso
    apply hne1
    rw [hQ] at hon
    obtain ⟨ξ', h1⟩ := ex_pt W x₁ hon
    have e := m3 (ξ'.comp (Subalgebra.inclusion hle)) ((negT x₁ ξ' h1).2 hneg) ((posT x₁ ξ' h1).2 hpos)
    refine alg_ext W _ _ fun j g hg => ?_
    rw [← h1 g]
    have e2 := e j _ (toA_mem W hg)
    rw [origin_toA] at e2
    exact e2
  obtain ⟨aF, haF0, haF⟩ := exists_toA W ha
  have hM4 : M4 (Fgr O W.wt) K Q.ideal := by
    intro ξ hon htw D hD D' hD' hDI hD'I
    rw [hQ] at hon hDI hD'I
    obtain ⟨ξ', h1⟩ := ex_pt W ξ hon
    have derT : ∀ D₀ : FA O W.wt →ₗ[O] K, D₀ ∈ PtDer ξ K → ∀ E : W.A →ₗ[O] K, (∀ g, E (toA W g) = D₀ g) →
        E ∘ₗ (Subalgebra.inclusion hle).toLinearMap ∈ PtDer (ξ'.comp (Subalgebra.inclusion hle)) K := by
      intro D₀ hD₀ E hE p q
      obtain ⟨fp, hfp⟩ := toA_surjective W (Subalgebra.inclusion hle p)
      obtain ⟨fq, hfq⟩ := toA_surjective W (Subalgebra.inclusion hle q)
      show E (Subalgebra.inclusion hle (p * q)) = ξ' (Subalgebra.inclusion hle p) • E (Subalgebra.inclusion hle q) +
        ξ' (Subalgebra.inclusion hle q) • E (Subalgebra.inclusion hle p)
      rw [map_mul, ← hfp, ← hfq, ← map_mul, hE, hE, hE, h1, h1]
      exact hD₀ fp fq
    obtain ⟨E1, hE1⟩ := ex_der W D hDI
    obtain ⟨E2, hE2⟩ := ex_der W D' hD'I
    have hng : ¬ (∀ j < 0, ∀ x (hx : x ∈ W.part j), (ξ'.comp (Subalgebra.inclusion hle)) ⟨x, le_iSup W.part j hx⟩ = 0) :=
      fun hh => htw.1 ((negT ξ ξ' h1).1 hh)
    have hps : ¬ (∀ j > 0, ∀ x (hx : x ∈ W.part j), (ξ'.comp (Subalgebra.inclusion hle)) ⟨x, le_iSup W.part j hx⟩ = 0) :=
      fun hh => htw.2 ((posT ξ ξ' h1).1 hh)
    obtain ⟨c1, hc1⟩ := m4 _ hng hps _ (derT D hD E1 hE1)
    obtain ⟨c2, hc2⟩ := m4 _ hng hps _ (derT D' hD' E2 hE2)
    have hDc : ∀ j g, g ∈ Fgr O W.wt j → D g = c1 * j * ξ g := fun j g hg => by
      rw [← hE1, ← h1]
      exact hc1 j _ (toA_mem W hg)
    have hD'c : ∀ j g, g ∈ Fgr O W.wt j → D' g = c2 * j * ξ g := fun j g hg => by
      rw [← hE2, ← h1]
      exact hc2 j _ (toA_mem W hg)
    by_cases hc : c1 = 0
    · refine ⟨1, 0, Or.inl one_ne_zero, lin_zero W _ fun j g hg => ?_⟩
      simp [hDc j g hg, hc]
    · refine ⟨c2, -c1, Or.inr (neg_ne_zero.2 hc), lin_zero W _ fun j g hg => ?_⟩
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul, hDc j g hg, hD'c j g hg]
      ring
  have hM5 : M5 (Fgr O W.wt) K (x0 O W.wt) Q.ideal aF := by
    refine ⟨haF0, ?_, fun ξ hon htw => ?_⟩
    · rw [← origin_toA W h aF, haF]
      exact ha0
    · rw [hQ] at hon
      obtain ⟨ξ', h1⟩ := ex_pt W ξ hon
      have e := m5 (ξ'.comp (Subalgebra.inclusion hle)) (fun hh => htw.1 ((negT ξ ξ' h1).1 hh))
        (fun hh => htw.2 ((posT ξ ξ' h1).1 hh))
      rw [← h1, haF]
      exact e
  obtain ⟨⟨T, hT⟩, hne, hbound⟩ := hM O K v hv (FA O W.wt) (Fgr O W.wt) (x0 O W.wt) hW _ _ _ _ _ Q aF hM1 hM2 hM3 hM4 hM5
  obtain ⟨T', hT', hdist⟩ := exists_cover_with_distinct_orbit_representatives O (FA O W.wt) K (Fgr O W.wt) Q.ideal T hT
  have hpt : ∀ ξ : T', ∃ ξ' : W.A →ₐ[O] K, ∀ g, ξ' (toA W g) = (ξ : FA O W.wt →ₐ[O] K) g :=
    fun ξ => ex_pt W ξ.1 (hQ ▸ (hT'.1 ξ.1 ξ.2).1)
  choose P hP using hpt
  have hFker : ∀ k, W.π (ser (Q.F k)) = 0 := fun k => by
    have h1 : Q.F k ∈ RingHom.ker (toA W) :=
      hQ ▸ Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨k, rfl⟩))))
    exact congrArg Subtype.val (RingHom.mem_ker.1 h1)
  refine ⟨T'.card, fun i => (P (T'.equivFin.symm i)).comp (Subalgebra.inclusion hle),
    (cotLen (x0 O W.wt) (Fgr O W.wt) (-1) Q.F).toNat, fun i => ?_, fun i i' t ht => ?_, ?_, ?_⟩
  · have htw := (hT'.1 _ (T'.equivFin.symm i).2).2
    exact ⟨fun hh => htw.1 ((negT _ _ (hP _)).1 hh), fun hh => htw.2 ((posT _ _ (hP _)).1 hh)⟩
  · have hs : (T'.equivFin.symm i').1 = act (Fgr O W.wt) (tz t) (T'.equivFin.symm i).1 :=
      alg_ext W _ _ fun j g hg => by
        rw [act_of_mem _ _ _ hg, ← hP _ g, ← hP _ g]
        exact ht j _ (toA_mem W hg)
    have e := hdist _ (T'.equivFin.symm i).2 _ (T'.equivFin.symm i').2 ⟨t, hs⟩
    exact T'.equivFin.symm.injective (Subtype.ext e)
  · intro c hc M _ _ d hd hsupp hrel
    rw [ENat.coe_toNat hne]
    exact length_le_cotLen_of_injective_tangent_map hM' O W.σ W.wt (-1) (by norm_num) _ Q.F Q.hF c hc M d hd hsupp
      (fun μ k => hrel μ _ (hFker k))
  · have hterm : ∀ ξ : T', ((P ξ).comp (Subalgebra.inclusion hle)) ⟨a, le_iSup W.part 0 ha⟩ = ξ.1 aF := by
      intro ξ
      rw [← hP ξ aF, haF]
      rfl
    simp_rw [hterm]
    rw [Equiv.sum_comp T'.equivFin.symm (fun x : T' => v (x.1 aF)), Finset.sum_coe_sort T' (fun ξ => v (ξ aF))]
    exact hbound T' hT'

end UpperTheory.V.UnitaryThreeInertia.Abs
