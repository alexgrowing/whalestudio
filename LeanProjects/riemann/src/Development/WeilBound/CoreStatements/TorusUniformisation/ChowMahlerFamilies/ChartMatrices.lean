import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsFractionRingOfIntegers
import Development.WeilBound.CoreStatements.HodgeTatePoints.FreeOfFg
import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChart
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

section Pt

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']

theorem pt_swap (P : HTPoint C O c κ N V Ω') (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

theorem pt_tate (P : HTPoint C O c κ N V Ω') (m : Ix E N) :
    P.tate (dl m) = P.ρ (RingOfIntegers.basis E m.2) (P.t m.1) :=
  PositivityTheory.HtPt.Gd.tate_single P m.1 _

theorem pt_matrices {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω') {g : ℕ}
    (bo : Basis (Fin g) O P.om) :
    ∃ (Hm : Matrix (Fin g) (Ix E N) O) (Eg : Matrix (Ix E N) (Ix E N) O),
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', algebraMap O C (Eg m m') = P.e (P.tate (dl m)) (P.tate (dl m'))) ∧
      ∀ m, ∃ h : P.ht (P.tate (dl m)) ∈ P.om, ∀ k, Hm k m = bo.repr ⟨_, h⟩ k := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gb.isFractionRing_of_integers hv
  haveI := P.om_lat
  have hinj := hv.hom_inj
  have hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Ix E N =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
    rw [← Submodule.span_span_of_tower O C, ← P.free.2.2, P.free.2.1]
  let B : Basis (Ix E N) C V := Basis.mk P.free.1 hsp
  have hBt : ∀ m, P.tate (dl m) = B m := fun m => by rw [pt_tate, Basis.mk_apply]
  have hT : P.T = Submodule.span O (Set.range B) := by rw [Basis.coe_mk, ← P.free.2.2]
  have hB : ∀ q, B q ∈ P.T := fun q => by
    rw [hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  haveI : FiniteDimensional C V := Module.Finite.of_basis B
  have hnd : ∀ x, (∀ y, P.e x y = 0) → x = 0 := fun x hx =>
    P.nondeg x fun y => by rw [pt_swap, hx, neg_zero]
  have hei : Function.Injective (P.e : V →ₗ[C] Module.Dual C V) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hnd x fun y => by rw [hx]; rfl
  have hes := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hei
  have hE : ∀ m m', ∃ r : O, algebraMap O C r = P.e (B m) (B m') := fun m m' => by
    have := hB m'
    rw [← P.perfect] at this
    exact this _ (hB m)
  choose Eg hEg using hE
  choose w hw using fun m => hes (B.coord m)
  have hwT : ∀ m, w m ∈ P.T := fun m => by
    rw [← P.perfect]
    intro x hx
    rw [pt_swap, hw]
    refine neg_mem ?_
    rw [hT] at hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨a m, ?_⟩
    simp only [map_sum, LinearMap.map_smul_of_tower, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
    simp [Algebra.smul_def]
  choose Ei hEi using fun m => (Submodule.mem_span_range_iff_exists_fun O).1 (hT ▸ hwT m)
  let bC := bo.extendOfIsLattice C
  have hbC : ∀ (y : P.om) k, bC.repr (y : Ω') k = algebraMap O C (bo.repr y k) := fun y k => by
    have e : (y : Ω') = ∑ j, algebraMap O C (bo.repr y j) • bC j := by
      have := congrArg Subtype.val (bo.sum_repr y)
      rw [Submodule.coe_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [algebraMap_smul, Submodule.coe_smul, Basis.extendOfIsLattice_apply]
    rw [e, bC.repr_sum_self]
  let Hm : Matrix (Fin g) (Ix E N) O := fun k m => bo.repr ⟨P.ht (B m), P.ht_mem _ (hB m)⟩ k
  have hHm : ∀ k m, algebraMap O C (Hm k m) = bC.repr (P.ht (B m)) k := fun k m =>
    (hbC ⟨_, P.ht_mem _ (hB m)⟩ k).symm
  refine ⟨Hm, Matrix.of Eg, ?_, ?_, ⟨Matrix.of Ei, ?_, ?_⟩, fun m m' => by rw [hBt, hBt]; exact hEg m m',
    fun m => ⟨by rw [hBt]; exact P.ht_mem _ (hB m), fun k => by simp only [Hm, hBt]⟩⟩
  · have hsurj : LinearMap.range P.ht = ⊤ := by
      rw [eq_top_iff, ← bC.span_eq, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨x, -, hx⟩ := P.κ_mem _ (bo k).2
      refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
      rw [map_smul, hx, ← algebraMap_smul C κ, inv_smul_smul₀ P.κ_ne]
      exact (Basis.extendOfIsLattice_apply C bo k).symm
    have h1 := LinearMap.finrank_range_add_finrank_ker P.ht
    rw [hsurj, finrank_top, finrank_eq_card_basis bC, finrank_eq_card_basis B, Fintype.card_fin] at h1
    have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
      ext x
      rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, P.lagr]
      refine forall_congr' fun y => ?_
      rw [LinearMap.mem_ker]
      refine imp_congr_right fun _ => ?_
      change P.e y x = 0 ↔ _
      rw [pt_swap P y x, neg_eq_zero]
    have h2 := LinearMap.BilinForm.finrank_orthogonal (B := P.e) ⟨hnd, P.nondeg⟩ (LinearMap.ker P.ht)
    rw [horth, finrank_eq_card_basis B] at h2
    omega
  · ext m m'
    apply hinj
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply, map_neg, hEg]
    exact pt_swap P _ _
  · ext m m'
    apply hinj
    have h := congrArg (fun f : Module.Dual C V => f (B m')) (hw m)
    simp only [← hEi m, map_sum, LinearMap.sum_apply, LinearMap.map_smul_of_tower, LinearMap.smul_apply,
      Basis.coord_apply, Basis.repr_self, ← hEg] at h
    rw [Matrix.mul_apply, map_sum]
    simp only [Matrix.of_apply, map_mul, ← Algebra.smul_def]
    rw [h, Matrix.one_apply, Finsupp.single_apply]
    by_cases hm : m = m'
    · simp [hm]
    · simp [hm, Ne.symm hm]
  · ext k k'
    apply hinj
    let x : V := ∑ m, algebraMap O C (Hm k m) • w m
    have hx : P.e x = (bC.coord k) ∘ₗ P.ht := by
      refine B.ext fun m => ?_
      simp only [x, map_sum, map_smul, hw, LinearMap.sum_apply, LinearMap.smul_apply, Basis.coord_apply,
        Basis.repr_self, LinearMap.comp_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [hHm]
    have h0 : P.ht x = 0 := (P.lagr x).2 fun y hy => by rw [hx, LinearMap.comp_apply, hy, map_zero]
    have h1 := congrArg (fun z => bC.repr z k') h0
    simp only [x, ← hEi, map_sum, map_smul, LinearMap.map_smul_of_tower, Finsupp.coe_finset_sum, Finset.sum_apply,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    rw [Matrix.zero_apply, map_zero, ← h1]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hHm k' m', ← algebraMap_smul C (Ei m m'), map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

end Pt

theorem chart_matrices {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {p R N : ℕ} (hR : 1 ≤ R)
    {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω)
    {C O : Type} [Field C] [CommRing O] [Algebra O C] [Algebra A O] {κ : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    {v : Valuation C NNReal} (hv : v.Integers O) (P : HTPoint C O c κ N V Ω')
    (ι₀ : D.om →ₛₗ[algebraMap A O] Ω') (hr : D.ReducesTo (algebraMap A O) P ι₀) :
    ∃ (g : ℕ) (io : D.om →ₛₗ[algebraMap A O] (Fin g → O)) (Hm : Matrix (Fin g) (Ix E N) O)
      (Eg : Matrix (Ix E N) (Ix E N) O),
      Submodule.span O (Set.range io) = ⊤ ∧
      (∀ f : D.om →ₛₗ[algebraMap A O] C, ∃ ev : (Fin g → C) →ₗ[C] C,
        ∀ u, ev (fun k => algebraMap O C (io u k)) = f u) ∧
      Fintype.card (Ix E N) = g + g ∧ Egᵀ = -Eg ∧
      (∃ Ei : Matrix (Ix E N) (Ix E N) O, Ei * Eg = 1 ∧ Hm * Ei * Hmᵀ = 0) ∧
      (∀ m m', Eg m m' - ((D.e (dl m) (dl m')).val : O) ∈ Ideal.span {(p : O)}) ∧
      ∀ m k, Hm k m - io ⟨D.h (dl m), D.h_mem _⟩ k ∈ Ideal.span {(p : O)} := by
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI := PositivityTheory.HtPt.Gd.free_of_fg hv P.om P.om_lat.fg
  haveI : Module.Finite O P.om := Module.Finite.iff_fg.2 P.om_lat.fg
  let bo := Module.finBasis O P.om
  have hmem : ∀ u, ι₀ u ∈ P.om := fun u => by
    rw [← hr.span_eq]
    exact Submodule.subset_span ⟨u, rfl⟩
  let ι₁ : D.om →ₛₗ[algebraMap A O] P.om := ι₀.codRestrict P.om hmem
  let io : D.om →ₛₗ[algebraMap A O] (Fin _ → O) := bo.equivFun.toLinearMap.comp ι₁
  have hio : ∀ u k, io u k = bo.repr ⟨ι₀ u, hmem u⟩ k := fun _ _ => rfl
  obtain ⟨Hm, Eg, h1, h2, h3, h4, h5⟩ := pt_matrices hv P bo
  obtain ⟨j, hj, hjr, hjι⟩ := PositivityTheory.HtPt.Gb.bc_iso A K Ω D.om C v O hv Ω' P.om ι₀ D.om_lat D.om_proj P.om_lat
    hr.span_eq hr.rank_eq
  have hpR : ∀ z : O, (p : O) ^ R * z ∈ Ideal.span {(p : O)} := fun z =>
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ hR)
  refine ⟨_, io, Hm, Eg, ?_, fun f => ?_, h1, h2, h3, fun m m' => ?_, fun m k => ?_⟩
  · have h6 : Submodule.span O (Set.range ι₁) = ⊤ := by
      apply Submodule.map_injective_of_injective P.om.injective_subtype
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hr.span_eq
    have : Set.range io = bo.equivFun.toLinearMap '' Set.range ι₁ := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h6, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨jf, hjf, -⟩ := PositivityTheory.HtPt.Gb.exists_lift f
    let e : (O ⊗[A] D.om) ≃ₗ[O] P.om := (LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hjr)
    have he : ∀ u, e (1 ⊗ₜ u) = ⟨ι₀ u, hmem u⟩ := fun u => Subtype.ext (hjι u)
    refine ⟨Fintype.linearCombination C fun k => jf (e.symm (bo k)), fun u => ?_⟩
    rw [Fintype.linearCombination_apply, ← hjf, ← e.symm_apply_apply (1 ⊗ₜ u), he]
    conv_rhs => rw [← bo.sum_repr ⟨ι₀ u, hmem u⟩]
    simp only [map_sum, map_smul, hio, algebraMap_smul]
  · obtain ⟨z, hz⟩ := hr.e_eq (dl m) (dl m')
    rw [hv.hom_inj ((h4 m m').trans hz), add_sub_cancel_left]
    exact hpR z
  · obtain ⟨h, hk⟩ := h5 m
    obtain ⟨y, hy, hz⟩ := hr.ht_eq (dl m)
    have : (⟨ι₀ ⟨D.h (dl m), D.h_mem _⟩, hmem _⟩ : P.om) = ⟨_, h⟩ + (p : O) ^ R • ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact hz
    rw [hk, hio, this, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel_left]
    exact neg_mem (hpR _)

end PositivityTheory.Xgn.TestGroupPoint
