import Formalism.LogFactorialIndices.StatementIdx
import Lemmata.DiscreteValuationQuotients.LenQuotSpan
import Lemmata.GeneralBFactSecondExtra.Key

open Module Submodule

noncomputable section

namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant

theorem addVal_prod {O ι : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, IsDiscreteValuationRing.addVal_mul, ih]

theorem length_quot_range {O M : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (φ : M →ₗ[O] M) (hφ : Function.Injective φ) :
    Module.length O (M ⧸ LinearMap.range φ) = IsDiscreteValuationRing.addVal O (LinearMap.det φ) := by
  first | exact Bl.DiscreteValuationQuotients.goal1 .. | (apply Bl.DiscreteValuationQuotients.goal1 <;> assumption) | (intros; apply Bl.DiscreteValuationQuotients.goal1 <;> assumption)

theorem length_tower {O Y : Type*} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  first | exact Bl.general_b_fact_second'''.goal1 .. | (apply Bl.general_b_fact_second'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second'''.goal1 <;> assumption)

theorem arith (x y d va vb ve ve' : ℕ∞) (h1 : ve = x + d) (h2 : ve' = y + d)
    (h3 : ve + vb = ve' + va) (hve : ve ≠ ⊤) (hve' : ve' ≠ ⊤) (hva : va ≠ ⊤) (hvb : vb ≠ ⊤) :
    (x.toNat : ℤ) - y.toNat = va.toNat - vb.toNat := by
  subst h1 h2
  have hx : x ≠ ⊤ := fun h => hve (by simp [h])
  have hd : d ≠ ⊤ := fun h => hve (by simp [h])
  have hy : y ≠ ⊤ := fun h => hve' (by simp [h])
  lift x to ℕ using hx
  lift y to ℕ using hy
  lift d to ℕ using hd
  lift va to ℕ using hva
  lift vb to ℕ using hvb
  norm_cast at h3
  simp only [ENat.toNat_natCast]
  omega

theorem arith3 (p q p1 q1 p2 q2 p3 q3 : ℕ∞) (h : p + (q1 + q2 + q3) = q + (p1 + p2 + p3))
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : p1 ≠ ⊤) (hq1 : q1 ≠ ⊤) (hp2 : p2 ≠ ⊤) (hq2 : q2 ≠ ⊤)
    (hp3 : p3 ≠ ⊤) (hq3 : q3 ≠ ⊤) :
    (p.toNat : ℤ) - q.toNat =
      ((p1.toNat : ℤ) - q1.toNat) + ((p2.toNat : ℤ) - q2.toNat) + ((p3.toNat : ℤ) - q3.toNat) := by
  lift p to ℕ using hp
  lift q to ℕ using hq
  lift p1 to ℕ using hp1
  lift q1 to ℕ using hq1
  lift p2 to ℕ using hp2
  lift q2 to ℕ using hq2
  lift p3 to ℕ using hp3
  lift q3 to ℕ using hq3
  norm_cast at h
  simp only [ENat.toNat_natCast]
  omega

section Main

variable {O K Y ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup Y] [Module K Y] [Module O Y]
  [IsScalarTower O K Y] [Fintype ι] [DecidableEq ι]

theorem repr_of_mem_span (b : Basis ι K Y)
    (li : LinearIndependent O b) (z : Submodule.span O (Set.range b)) (i : ι) :
    b.repr z i = algebraMap O K ((Basis.span li).repr z i) := by
  have hz : (z : Y) = ∑ j, algebraMap O K ((Basis.span li).repr z j) • b j := by
    conv_lhs => rw [← (Basis.span li).sum_repr z]
    simp [Basis.span_apply, algebraMap_smul]
  rw [hz, b.repr_sum_self]

theorem len_span (b : Basis ι K Y) (w : ι → Y) (hw : ∀ j, w j ∈ Submodule.span O (Set.range b))
    (hdet : (b.toMatrix w).det ≠ 0) :
    ∃ e : O, algebraMap O K e = (b.toMatrix w).det ∧
      Module.length O (Submodule.span O (Set.range b) ⧸
        (Submodule.span O (Set.range w)).comap (Submodule.span O (Set.range b)).subtype) =
        IsDiscreteValuationRing.addVal O e := by
  set L := Submodule.span O (Set.range b) with hLdef
  have li : LinearIndependent O b :=
    LinearIndependent.restrict_scalars' (R := O) (K := K) b.linearIndependent
  let bO : Basis ι O L := Basis.span li
  have hrepr : ∀ (z : L) i, b.repr z i = algebraMap O K (bO.repr z i) :=
    fun z i => repr_of_mem_span b li z i
  have : Module.Free O L := Module.Free.of_basis bO
  have : Module.Finite O L := Module.Finite.of_basis bO
  let φ : L →ₗ[O] L := bO.constr O (fun j => ⟨w j, hw j⟩)
  have hφ : ∀ z : L, (φ z : Y) = ∑ j, bO.equivFun z j • w j := by
    intro z
    simp only [φ, Basis.constr_apply_fintype, Submodule.coe_sum, Submodule.coe_smul]
  have hwK : LinearIndependent K w :=
    ((b.is_basis_iff_det).2 (by rw [Basis.det_apply]; exact isUnit_iff_ne_zero.2 hdet)).1
  have hwO : LinearIndependent O w :=
    LinearIndependent.restrict_scalars' (R := O) (K := K) hwK
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h0 : ∑ j, bO.equivFun z j • w j = 0 := by rw [← hφ, hz]; rfl
    have h1 := Fintype.linearIndependent_iff.1 hwO _ h0
    apply bO.equivFun.injective
    funext j
    simp [h1 j]
  have hrange : LinearMap.range φ = (Submodule.span O (Set.range w)).comap L.subtype := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      show (φ z : Y) ∈ Submodule.span O (Set.range w)
      rw [hφ]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro hy
      have hy' : (y : Y) ∈ Submodule.span O (Set.range w) := hy
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy'
      refine ⟨bO.equivFun.symm g, Subtype.ext ?_⟩
      rw [hφ, LinearEquiv.apply_symm_apply, hg]
  have hH : ∀ i j, algebraMap O K (LinearMap.toMatrix bO bO φ i j) = b.toMatrix w i j := by
    intro i j
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp only [φ, Basis.constr_basis]
    exact (hrepr ⟨w j, hw j⟩ i).symm
  refine ⟨LinearMap.det φ, ?_, ?_⟩
  · rw [← LinearMap.det_toMatrix bO, RingHom.map_det]
    congr 1
    ext i j
    exact hH i j
  · rw [← hrange, length_quot_range φ hinj]

theorem idx_two_bases (b b' : Basis ι K Y) (a c0 : O) (ha : a ≠ 0) (hc0 : c0 ≠ 0)
    (h : algebraMap O K a = (b.toMatrix b').det * algebraMap O K c0) :
    idx O Y (Submodule.span O (Set.range b)) (Submodule.span O (Set.range b')) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O c0).toNat : ℤ) := by
  have hinjK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hM : (b.toMatrix b').det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact ha (hinjK (by rw [h, map_zero]))
  obtain ⟨⟨c, hc⟩, hcI⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : ι × ι => b.toMatrix b' p.1 p.2)
  have hc0' : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcI' : ∀ i j, ∃ o : O, algebraMap O K o = c • b.repr (b' j) i := by
    intro i j
    obtain ⟨o, ho⟩ := hcI (i, j)
    exact ⟨o, ho⟩
  choose o ho using hcI'
  let w : ι → Y := fun j => c • b' j
  have hw : ∀ j, w j ∈ Submodule.span O (Set.range b) := by
    intro j
    show c • b' j ∈ _
    rw [← b.sum_repr (b' j), Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← smul_assoc, ← ho i j, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hw' : ∀ j, w j ∈ Submodule.span O (Set.range b') :=
    fun j => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmat : ∀ e : Basis ι K Y, e.toMatrix w = algebraMap O K c • e.toMatrix b' := by
    intro e
    ext i j
    simp only [Basis.toMatrix_apply, w, Matrix.smul_apply, smul_eq_mul]
    rw [← algebraMap_smul K c (b' j), map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hcK : algebraMap O K c ≠ 0 := (map_ne_zero_iff _ hinjK).2 hc0'
  obtain ⟨e, he, hlen⟩ := len_span b w hw (by
    rw [hmat, Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hcK) hM)
  obtain ⟨e', he', hlen'⟩ := len_span b' w hw' (by
    rw [hmat, Matrix.det_smul, Basis.toMatrix_self, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hcK)
  have hE : Submodule.span O (Set.range w) ≤
      Submodule.span O (Set.range b) ⊓ Submodule.span O (Set.range b') :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ⟨hw j, hw' j⟩)
  have t1 := length_tower (Submodule.span O (Set.range b)) (Submodule.span O (Set.range b'))
    _ _ (fun y => Submodule.mem_inf) hE
  have t2 := length_tower (Submodule.span O (Set.range b')) (Submodule.span O (Set.range b))
    _ _ (fun y => by rw [Submodule.mem_inf, and_comm]) hE
  rw [hlen] at t1
  rw [hlen'] at t2
  have hrel : e * c0 = e' * a := by
    apply hinjK
    rw [map_mul, map_mul, he, he', h, hmat, hmat, Matrix.det_smul, Matrix.det_smul,
      Basis.toMatrix_self, Matrix.det_one]
    ring
  have hv := congrArg (IsDiscreteValuationRing.addVal O) hrel
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul] at hv
  have hne : ∀ x : O, x ≠ 0 → IsDiscreteValuationRing.addVal O x ≠ ⊤ :=
    fun x hx h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero, hmat, Matrix.det_smul] at he
    exact mul_ne_zero (pow_ne_zero _ hcK) hM he.symm
  have he0' : e' ≠ 0 := by
    rintro rfl
    rw [map_zero, hmat, Matrix.det_smul, Basis.toMatrix_self, Matrix.det_one, mul_one] at he'
    exact pow_ne_zero _ hcK he'.symm
  unfold idx qlen
  exact arith _ _ _ _ _ _ _ t1 t2 hv (hne _ he0) (hne _ he0') (hne _ ha) (hne _ hc0)

theorem idxDet_core {X : Type} [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b) :
    idx O Y (Submodule.span O (Set.range bY))
          ((Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O)) =
        ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by
  have hmap : (Submodule.span O (Set.range bX)).map ((f : X →ₗ[K] Y).restrictScalars O) =
      Submodule.span O (Set.range (bX.map f)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
  have hmat : LinearMap.toMatrix bX bY (f : X →ₗ[K] Y) = bY.toMatrix (bX.map f) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, Basis.map_apply]
  rw [hmap]
  rw [hmat] at h
  exact idx_two_bases bY (bX.map f) a b ha hb h

end Main

end Formalism.LatticeIndexTer.LatticeIndexDeterminant

namespace Formalism.LatticeIndexTer.LatticeIndexDeterminant

section Frac

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

theorem det_frac {X Y ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] (bX : Basis ι K X) (bY : Basis ι K Y) (f : X ≃ₗ[K] Y) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap O K a = (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det * algebraMap O K b := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective O
    (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hb0
  have hdet : (LinearMap.toMatrix bX bY (f : X →ₗ[K] Y)).det ≠ 0 :=
    (LinearEquiv.isUnit_det f bX bY).ne_zero
  refine ⟨a, b, ?_, hb0, ?_⟩
  · rintro rfl
    apply hdet
    rw [← hab, map_zero, zero_div]
  · rw [← hab, div_mul_cancel₀ _ hbK]

theorem index_scalar_multiple_eq {X ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module K X]
    [Module O X] [IsScalarTower O K X] (bN : Basis ι K X) (u : K) (hu : u ≠ 0) (a b : O)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : algebraMap O K a = u ^ Fintype.card ι * algebraMap O K b) :
    idx O X (Submodule.span O (Set.range bN))
        ((Submodule.span O (Set.range bN)).map ((u • LinearMap.id : X →ₗ[K] X).restrictScalars O)) =
      ((IsDiscreteValuationRing.addVal O a).toNat : ℤ) -
        ((IsDiscreteValuationRing.addVal O b).toNat : ℤ) := by
  let f : X ≃ₗ[K] X := LinearEquiv.smulOfNeZero K X u hu
  have hf : (f : X →ₗ[K] X) = u • LinearMap.id := by
    ext x
    rfl
  have hdet : (LinearMap.toMatrix bN bN (f : X →ₗ[K] X)).det = u ^ Fintype.card ι := by
    rw [hf, map_smul, LinearMap.toMatrix_id, Matrix.det_smul, Matrix.det_one, mul_one]
  rw [← hf]
  exact idxDet_core bN bN f a b ha hb (by rw [hdet]; exact h)

end Frac

end Formalism.LatticeIndexTer.LatticeIndexDeterminant

namespace Formalism.LatticeIndexTer

open Module

theorem lattice_index_eq_det_valuation : IdxDet := by
  intro O K X Y ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bX bY f a b ha hb h
  exact LatticeIndexDeterminant.idxDet_core bX bY f a b ha hb h

theorem lattice_index_three_term : ThreeIdx := by
  intro O K X₁ X₂ X₃ X₄ ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    b₁ b₂ b₃ b₄ θ' j θ a b ha hb h
  dsimp only
  obtain ⟨a1, c1, ha1, hc1, h1⟩ := LatticeIndexDeterminant.det_frac (O := O) b₁ b₂ θ'
  obtain ⟨a2, c2, ha2, hc2, h2⟩ := LatticeIndexDeterminant.det_frac (O := O) b₂ b₃ j
  obtain ⟨a3, c3, ha3, hc3, h3⟩ := LatticeIndexDeterminant.det_frac (O := O) b₃ b₄ θ
  rw [LatticeIndexDeterminant.idxDet_core b₁ b₂ θ' a1 c1 ha1 hc1 h1, LatticeIndexDeterminant.idxDet_core b₂ b₃ j a2 c2 ha2 hc2 h2,
    LatticeIndexDeterminant.idxDet_core b₃ b₄ θ a3 c3 ha3 hc3 h3]
  have hcomp : LinearMap.toMatrix b₁ b₄
      ((θ : X₃ →ₗ[K] X₄) ∘ₗ (j : X₂ →ₗ[K] X₃) ∘ₗ (θ' : X₁ →ₗ[K] X₂)) =
      LinearMap.toMatrix b₃ b₄ (θ : X₃ →ₗ[K] X₄) *
        (LinearMap.toMatrix b₂ b₃ (j : X₂ →ₗ[K] X₃) * LinearMap.toMatrix b₁ b₂ (θ' : X₁ →ₗ[K] X₂)) := by
    rw [LinearMap.toMatrix_comp b₁ b₃ b₄, LinearMap.toMatrix_comp b₁ b₂ b₃]
  rw [hcomp, Matrix.det_mul, Matrix.det_mul] at h
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hrel : a * (c1 * c2 * c3) = b * (a1 * a2 * a3) := by
    apply hinj
    simp only [map_mul]
    rw [h, h1, h2, h3]
    ring
  have hv := congrArg (IsDiscreteValuationRing.addVal O) hrel
  simp only [IsDiscreteValuationRing.addVal_mul] at hv
  have hne : ∀ x : O, x ≠ 0 → IsDiscreteValuationRing.addVal O x ≠ ⊤ :=
    fun x hx h => hx (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  exact LatticeIndexDeterminant.arith3 _ _ _ _ _ _ _ _ hv (hne _ ha) (hne _ hb) (hne _ ha1) (hne _ hc1)
    (hne _ ha2) (hne _ hc2) (hne _ ha3) (hne _ hc3)

theorem idxScale_of (hB : LatBasis) : IdxScale := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ s N hN
  obtain ⟨bN, rfl⟩ := hB O K X N hN
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖK : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ0
  have hu0 : algebraMap O K ϖ ^ (-s) ≠ 0 := zpow_ne_zero _ hϖK
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · rw [LatticeIndexDeterminant.index_scalar_multiple_eq bN _ hu0 1 (ϖ ^ (k * finrank K X)) one_ne_zero
      (pow_ne_zero _ hϖ0) (by
        rw [Fintype.card_fin, map_one, map_pow, zpow_neg, zpow_natCast, inv_pow, ← pow_mul,
          inv_mul_cancel₀ (pow_ne_zero _ hϖK)])]
    rw [IsDiscreteValuationRing.addVal_one, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
    simp
  · rw [LatticeIndexDeterminant.index_scalar_multiple_eq bN _ hu0 (ϖ ^ (k * finrank K X)) 1 (pow_ne_zero _ hϖ0) one_ne_zero (by
        rw [Fintype.card_fin, map_one, mul_one, map_pow, neg_neg, zpow_natCast, ← pow_mul])]
    rw [IsDiscreteValuationRing.addVal_one, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
    simp

theorem LatticeIndexDeterminant.lattice_span_of_basis : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Module.IsTorsionFree O K :=
    isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective O K)
  have : Submodule.IsLattice K A := ⟨hA.1, hA.2⟩
  let b := Module.Free.chooseBasis O A
  let bK := b.extendOfIsLattice K
  refine ⟨bK.reindex (bK.indexEquiv (Module.finBasis K X)), ?_⟩
  rw [Basis.range_reindex]
  have hr : Set.range bK = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [bK]
  rw [hr, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem lattice_index_scale : IdxScale := idxScale_of LatticeIndexDeterminant.lattice_span_of_basis

end Formalism.LatticeIndexTer
