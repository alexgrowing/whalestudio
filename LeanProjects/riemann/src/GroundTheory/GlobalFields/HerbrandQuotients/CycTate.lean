import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract

namespace GroundTheory.Global

open GroundTheory.GroupCoh

section KerModRange

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

noncomputable def kerModRangeEquivOfSurjective {f g : A →+ A} (φ : f.ker →+ B)
    (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) :
    KerModRange f g ≃+ B :=
  (QuotientAddGroup.quotientAddEquivOfEq (by
      ext a
      rw [AddMonoidHom.mem_ker, hk, AddSubgroup.mem_addSubgroupOf])).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hs)

theorem kerModRangeEquivOfSurjective_mk {f g : A →+ A} (φ : f.ker →+ B)
    (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) (a : f.ker) :
    kerModRangeEquivOfSurjective φ hs hk (QuotientAddGroup.mk a : KerModRange f g) = φ a :=
  rfl

theorem addEquiv_symm_apply_comm {f : A →+ A} {f' : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (f a) = f' (e a)) (b : B) :
    e.symm.toAddMonoidHom (f' b) = f (e.symm.toAddMonoidHom b) := by
  apply e.injective
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, hf]

noncomputable def kerModRangeCongr {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) :
    KerModRange fA gA ≃+ KerModRange fB gB where
  toFun := KerModRange.map e.toAddMonoidHom hf hg
  invFun := KerModRange.map e.symm.toAddMonoidHom (addEquiv_symm_apply_comm e hf)
    (addEquiv_symm_apply_comm e hg)
  left_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.symm_apply_apply (a : A)))
  right_inv x := by
    induction x using QuotientAddGroup.induction_on with
    | H a => exact congrArg QuotientAddGroup.mk (Subtype.ext (e.apply_symm_apply (a : B)))
  map_add' := map_add _

theorem kerModRangeCongr_mk {fA gA : A →+ A} {fB gB : B →+ B} (e : A ≃+ B)
    (hf : ∀ a, e (fA a) = fB (e a)) (hg : ∀ a, e (gA a) = gB (e a)) (a : fA.ker) :
    kerModRangeCongr e hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      QuotientAddGroup.mk (kerMap e.toAddMonoidHom hf a) :=
  rfl

noncomputable def kerModRangePiEquiv {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i))
    (hG : ∀ x i, G x i = g i (x i)) :
    KerModRange F G ≃+ ∀ i, KerModRange (f i) (g i) :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.pi fun i => (QuotientAddGroup.mk' _).comp
      (((Pi.evalAddMonoidHom A i).comp F.ker.subtype).codRestrict (f i).ker fun x => by
        simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, Pi.evalAddMonoidHom_apply,
          AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]))
    (by
      intro y
      choose z hz using fun i => QuotientAddGroup.mk_surjective (y i)
      refine ⟨⟨fun i => z i, AddMonoidHom.mem_ker.2 (funext fun i => ?_)⟩, funext fun i => ?_⟩
      · rw [hF, AddMonoidHom.mem_ker.1 (z i).2, Pi.zero_apply]
      · rw [← hz i]
        rfl)
    (by
      intro x
      constructor
      · intro h
        have h' : ∀ i, (x : ∀ i, A i) i ∈ (g i).range := fun i => by
          have := congrFun h i
          rw [Pi.zero_apply] at this
          exact (KerModRange.mk_eq_zero_iff _).1 this
        choose y hy using fun i => AddMonoidHom.mem_range.1 (h' i)
        exact AddMonoidHom.mem_range.2 ⟨y, funext fun i => by rw [hG, hy]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        funext i
        rw [Pi.zero_apply]
        refine (KerModRange.mk_eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨y i, ?_⟩)
        show g i (y i) = (x : ∀ i, A i) i
        rw [← hG, hy])

theorem kerModRangePiEquiv_mk {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)]
    (F G : (∀ i, A i) →+ (∀ i, A i)) (f g : ∀ i, A i →+ A i) (hF : ∀ x i, F x i = f i (x i))
    (hG : ∀ x i, G x i = g i (x i)) (x : F.ker) (i : ι) :
    kerModRangePiEquiv F G f g hF hG (QuotientAddGroup.mk x : KerModRange F G) i =
      QuotientAddGroup.mk (⟨(x : ∀ i, A i) i, by
        rw [AddMonoidHom.mem_ker, ← hF, AddMonoidHom.mem_ker.1 x.2, Pi.zero_apply]⟩ : (f i).ker) :=
  rfl

end KerModRange

section Defs

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

def cycSubOne (ρ : Representation k G V) (σ : G) : V →+ V :=
  (ρ σ - 1 : Module.End k V).toAddMonoidHom

theorem cycSubOne_apply (ρ : Representation k G V) (σ : G) (x : V) :
    cycSubOne ρ σ x = ρ σ x - x :=
  rfl

theorem apply_eq_self_of_generator (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : V} (hx : ρ σ x = x) (g : G) : ρ g x = x := by
  have := hσ g
  rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy, hx]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, Module.End.mul_apply, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_ker_cycSubOne_iff (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : V) :
    x ∈ (cycSubOne ρ σ).ker ↔ ∀ g, ρ g x = x := by
  rw [AddMonoidHom.mem_ker, cycSubOne_apply, sub_eq_zero]
  exact ⟨fun h => apply_eq_self_of_generator ρ hσ h, fun h => h σ⟩

theorem apply_sub_self_mem_range_cycSubOne (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : V) :
    ρ g x - x ∈ (cycSubOne ρ σ).range := by
  have := hσ g
  rw [Subgroup.zpowers_eq_closure] at this
  induction this using Subgroup.closure_induction generalizing x with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨x, rfl⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by
      rw [map_mul, Module.End.mul_apply]; abel
    rw [this]
    exact add_mem (ha _) (hb _)
  | inv a _ ha =>
    have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      abel
    rw [this]
    exact neg_mem (ha _)

theorem range_cycSubOne_eq_closure (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne ρ σ).range = AddSubgroup.closure {y | ∃ g x, ρ g x - x = y} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact AddSubgroup.subset_closure ⟨σ, x, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨g, x, rfl⟩
    exact apply_sub_self_mem_range_cycSubOne ρ hσ g x

variable [Fintype G]

def cycNorm (ρ : Representation k G V) : V →+ V :=
  ρ.norm.toAddMonoidHom

theorem cycNorm_apply (ρ : Representation k G V) (x : V) : cycNorm ρ x = ∑ g : G, ρ g x := by
  simp [cycNorm, Representation.norm, LinearMap.sum_apply]

theorem cycSubOne_cycNorm (ρ : Representation k G V) (σ : G) (x : V) :
    cycSubOne ρ σ (cycNorm ρ x) = 0 := by
  rw [cycSubOne_apply, sub_eq_zero]
  exact ρ.self_norm_apply σ x

theorem cycNorm_cycSubOne (ρ : Representation k G V) (σ : G) (x : V) :
    cycNorm ρ (cycSubOne ρ σ x) = 0 := by
  rw [cycSubOne_apply, map_sub, sub_eq_zero]
  exact ρ.norm_self_apply σ x

abbrev CycTateZero (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycSubOne ρ σ) (cycNorm ρ)

abbrev CycTateNegOne (ρ : Representation k G V) (σ : G) : Type _ :=
  KerModRange (cycNorm ρ) (cycSubOne ρ σ)

noncomputable def cycHerbrand (ρ : Representation k G V) (σ : G) : ℚ :=
  herbrandQuotient (cycSubOne ρ σ) (cycNorm ρ)

theorem cycHerbrand_eq (ρ : Representation k G V) (σ : G) :
    cycHerbrand ρ σ = (Nat.card (CycTateZero ρ σ) : ℚ) / Nat.card (CycTateNegOne ρ σ) :=
  rfl

end Defs

section Congr

variable {k G V W : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

noncomputable def cycTateZeroCongr {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateZero ρ σ ≃+ CycTateZero ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycSubOne_apply, he])
    (fun v => by simp [cycNorm_apply, map_sum, he])

noncomputable def cycTateNegOneCongr {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    CycTateNegOne ρ σ ≃+ CycTateNegOne ρ' σ :=
  kerModRangeCongr e (fun v => by simp [cycNorm_apply, map_sum, he])
    (fun v => by simp [cycSubOne_apply, he])

theorem cycHerbrand_congr {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ := by
  rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr (cycTateZeroCongr e he σ).toEquiv,
    Nat.card_congr (cycTateNegOneCongr e he σ).toEquiv]

end Congr

section Pi

variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]

def piRep (ρ : ∀ i, Representation k G (V i)) : Representation k G (∀ i, V i) where
  toFun g := LinearMap.pi fun i => (ρ i g).comp (LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp]
theorem piRep_apply (ρ : ∀ i, Representation k G (V i)) (g : G) (x : ∀ i, V i) (i : ι) :
    piRep ρ g x i = ρ i g (x i) :=
  rfl

theorem cycSubOne_piRep_apply (ρ : ∀ i, Representation k G (V i)) (σ : G) (x : ∀ i, V i)
    (i : ι) : cycSubOne (piRep ρ) σ x i = cycSubOne (ρ i) σ (x i) :=
  rfl

variable [Fintype G]

theorem cycNorm_piRep_apply (ρ : ∀ i, Representation k G (V i)) (x : ∀ i, V i) (i : ι) :
    cycNorm (piRep ρ) x i = cycNorm (ρ i) (x i) := by
  rw [cycNorm_apply, cycNorm_apply, Finset.sum_apply]
  rfl

noncomputable def cycTateZeroPiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    CycTateZero (piRep ρ) σ ≃+ ∀ i, CycTateZero (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycSubOne_piRep_apply ρ σ) (cycNorm_piRep_apply ρ)

noncomputable def cycTateNegOnePiEquiv (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    CycTateNegOne (piRep ρ) σ ≃+ ∀ i, CycTateNegOne (ρ i) σ :=
  kerModRangePiEquiv _ _ _ _ (cycNorm_piRep_apply ρ) (cycSubOne_piRep_apply ρ σ)

theorem cycHerbrand_pi [Fintype ι] (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    cycHerbrand (piRep ρ) σ = ∏ i, cycHerbrand (ρ i) σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroPiEquiv ρ σ).toEquiv,
    Nat.card_congr (cycTateNegOnePiEquiv ρ σ).toEquiv, Nat.card_pi, Nat.card_pi,
    Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end Pi

end GroundTheory.Global
