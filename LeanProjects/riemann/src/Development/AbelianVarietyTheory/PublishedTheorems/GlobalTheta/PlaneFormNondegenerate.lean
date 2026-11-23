import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfPowClose

noncomputable section

open Filter Topology

namespace GlobalTheory.Published

@[ext] structure Heisenberg {F W : Type} [Field F] [AddCommGroup W] [Module F W] (B : LinearMap.BilinForm F W) : Type where

  vec : W

  cen : F

namespace Heisenberg

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}

instance : Mul (Heisenberg B) := ⟨fun g h => ⟨g.vec + h.vec, g.cen + h.cen + B g.vec h.vec / 2⟩⟩
instance : One (Heisenberg B) := ⟨⟨0, 0⟩⟩
instance : Inv (Heisenberg B) := ⟨fun g => ⟨-g.vec, -g.cen + B g.vec g.vec / 2⟩⟩

@[simp] theorem mul_vec (g h : Heisenberg B) : (g * h).vec = g.vec + h.vec := rfl
@[simp] theorem mul_cen (g h : Heisenberg B) : (g * h).cen = g.cen + h.cen + B g.vec h.vec / 2 := rfl
@[simp] theorem one_vec : (1 : Heisenberg B).vec = 0 := rfl
@[simp] theorem one_cen : (1 : Heisenberg B).cen = 0 := rfl
@[simp] theorem inv_vec (g : Heisenberg B) : g⁻¹.vec = -g.vec := rfl
@[simp] theorem inv_cen (g : Heisenberg B) : g⁻¹.cen = -g.cen + B g.vec g.vec / 2 := rfl

instance : Group (Heisenberg B) :=
  Group.ofLeftAxioms
    (fun a b c => by ext <;> simp [add_assoc]; ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp; ring)

instance [TopologicalSpace F] [TopologicalSpace W] : TopologicalSpace (Heisenberg B) :=
  TopologicalSpace.induced (fun g => (g.vec, g.cen)) inferInstance

theorem mul_eq_central_mul (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (g h : Heisenberg B) :
    g * h = (⟨0, B g.vec h.vec⟩ : Heisenberg B) * (h * g) := by
  ext
  · simp [add_comm]
  · simp [← hB.neg_eq g.vec h.vec]; field_simp; ring

theorem mul_ne_mul (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) {x y : W} (hxy : B x y ≠ 0) :
    (⟨x, 0⟩ : Heisenberg B) * ⟨y, 0⟩ ≠ ⟨y, 0⟩ * ⟨x, 0⟩ := by
  intro h
  rw [mul_eq_central_mul h2 hB, mul_eq_right] at h
  exact hxy (congrArg Heisenberg.cen h)

def IsIrrSmoothOf [TopologicalSpace F] [TopologicalSpace W] (ψ : AddChar F ℂ) {S : Type} [AddCommGroup S] [Module ℂ S]
    (ρ : Representation ℂ (Heisenberg B) S) : Prop :=
  PRep.IsSmooth ρ ∧ ρ.IsIrreducible ∧ ∀ (t : F) (v : S), ρ ⟨0, t⟩ v = ψ t • v

end Heisenberg

def StoneVonNeumann : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F], (2 : F) ≠ 0 →
  ∀ (W : Type) [AddCommGroup W] [Module F W] [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]
    (B : LinearMap.BilinForm F W), B.IsAlt → B.Nondegenerate →
  ∀ ψ : AddChar F ℂ, Continuous ψ → ψ ≠ 1 →
    (∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S) (ρ : Representation ℂ (Heisenberg B) S),
      Heisenberg.IsIrrSmoothOf ψ ρ) ∧
    ∀ (S S' : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S']
      (ρ : Representation ℂ (Heisenberg B) S) (ρ' : Representation ℂ (Heisenberg B) S'),
      Heisenberg.IsIrrSmoothOf ψ ρ → Heisenberg.IsIrrSmoothOf ψ ρ' → Nonempty (ρ.Equiv ρ')

namespace SvN

section Abstract

variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]

structure Alt (c : W → W → ℂ) : Prop where
  left : ∀ x y z, c (x + y) z = c x z * c y z
  right : ∀ x y z, c x (y + z) = c x y * c x z
  self : ∀ x, c x x = 1

variable {c : W → W → ℂ}

theorem Alt.anti (h : Alt c) (x y : W) : c x y * c y x = 1 := by
  have := h.self (x + y)
  rw [h.left, h.right, h.right, h.self, h.self] at this
  simpa using this

theorem Alt.ne (h : Alt c) (x y : W) : c x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.anti x y)

theorem Alt.zero_left (h : Alt c) (y : W) : c 0 y = 1 := by
  have := h.left 0 0 y
  rw [add_zero] at this
  exact (mul_eq_left₀ (h.ne 0 y)).1 this.symm

theorem Alt.zero_right (h : Alt c) (y : W) : c y 0 = 1 := by
  have := h.anti y 0
  rwa [h.zero_left, mul_one] at this

theorem Alt.sq_swap (h : Alt c) {x y : W} (hxy : c x y ^ 2 = 1) : c y x ^ 2 = 1 := by
  have := congrArg (· ^ 2) (h.anti x y)
  simpa [mul_pow, hxy] using this

def Alt.perp (h : Alt c) (T : Set W) : AddSubgroup W where
  carrier := {x | ∀ t ∈ T, c x t ^ 2 = 1}
  add_mem' := fun {a b} ha hb t ht => by rw [h.left, mul_pow, ha t ht, hb t ht, mul_one]
  zero_mem' := fun t _ => by rw [h.zero_left, one_pow]
  neg_mem' := fun {a} ha t ht => by
    have := congrArg (· ^ 2) (h.left a (-a) t)
    simpa [mul_pow, ha t ht, h.zero_left] using this.symm

theorem Alt.perp_perp_perp (h : Alt c) (T : Set W) (a : W) (ha : a ∈ h.perp (h.perp (h.perp T))) : a ∈ h.perp T :=
  fun t ht => ha t fun _ hx => h.sq_swap (hx t ht)

structure Ops (c : W → W → ℂ) (ρ : W → Module.End ℂ M) : Prop where
  zero : ∀ v, ρ 0 v = v
  mul : ∀ x y v, ρ x (ρ y v) = c x y • ρ (x + y) v

variable {ρ : W → Module.End ℂ M}

theorem Ops.comm (h : Alt c) (hρ : Ops c ρ) (x y : W) (v : M) : ρ x (ρ y v) = c x y ^ 2 • ρ y (ρ x v) := by
  rw [hρ.mul, hρ.mul, smul_smul, add_comm y x, pow_two, mul_assoc, h.anti, mul_one]

theorem Ops.eq_zero (h : Alt c) (hρ : Ops c ρ) {x : W} {v : M} (hv : ρ x v = 0) : v = 0 := by
  have := hρ.mul (-x) x v
  rw [hv, map_zero, neg_add_cancel, hρ.zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (h.ne _ _)

structure Splits (c : W → W → ℂ) (A : AddSubgroup W) (α : W → ℂ) : Prop where
  ne : ∀ a ∈ A, α a ≠ 0
  mul : ∀ a ∈ A, ∀ b ∈ A, α a * α b = c a b * α (a + b)

variable {A : AddSubgroup W} {α : W → ℂ}

theorem Splits.comp (hρ : Ops c ρ) (hα : Splits c A α) {a b : W} (ha : a ∈ A) (hb : b ∈ A) (m : M) :
    (α a)⁻¹ • ρ a ((α b)⁻¹ • ρ b m) = (α (a + b))⁻¹ • ρ (a + b) m := by
  rw [map_smul, hρ.mul, smul_smul, smul_smul]
  congr 1
  have := hα.mul a ha b hb
  have h1 := hα.ne a ha
  have h2 := hα.ne b hb
  have h3 := hα.ne _ (A.add_mem ha hb)
  field_simp
  linear_combination -this

theorem average (hρ : Ops c ρ) (hα : Splits c A α) (U : AddSubgroup W) (hU : ∀ u ∈ U, α u = 1)
    [Fintype (A ⧸ U.addSubgroupOf A)] (m : M) (hm : ∀ u ∈ U, ρ u m = m) (a : W) (ha : a ∈ A) :
    ρ a (∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m)
      = α a • ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 m := by
  rw [← inv_smul_eq_iff₀ (hα.ne a ha), map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) _ _ fun q => ?_
  rw [hα.comp hρ ha q.out.2]
  set p := (Equiv.addLeft ((⟨a, ha⟩ : A) : A ⧸ U.addSubgroupOf A)) q with hp
  have h1 : (p.out : A ⧸ U.addSubgroupOf A) = ((⟨a, ha⟩ + q.out : A) : A ⧸ U.addSubgroupOf A) := by
    simp [hp]
  have h2 : -p.out.1 + (a + q.out.1) ∈ U := by
    have := QuotientAddGroup.eq.1 h1
    exact this
  have h3 := hα.comp hρ p.out.2 (A.add_mem (A.neg_mem p.out.2) (A.add_mem ha q.out.2)) m
  rw [hm _ h2, hU _ h2, add_neg_cancel_left] at h3
  rw [← h3]; simp

theorem exists_eigen (h : Alt c) (hρ : Ops c ρ) (hα : Splits c A α) (T : Set W) (hU : ∀ u ∈ h.perp T, α u = 1)
    [Finite (A ⧸ (h.perp T).addSubgroupOf A)] (N : Submodule ℂ M) (hN : ∀ x, ∀ m ∈ N, ρ x m ∈ N)
    (v : M) (hvN : v ∈ N) (hv0 : v ≠ 0) (hv : ∀ u ∈ h.perp T, ρ u v = v) :
    ∃ e ∈ N, e ≠ 0 ∧ ∀ a ∈ A, ρ a e = α a • e := by
  classical
  set U := h.perp T with hUdef
  let := Fintype.ofFinite (A ⧸ U.addSubgroupOf A)
  by_contra hcon
  have hz : ∀ w ∈ h.perp U, ∑ q : A ⧸ U.addSubgroupOf A, c q.out.1 w ^ 2 • ((α q.out.1)⁻¹ • ρ q.out.1 v) = 0 := by
    intro w hw
    have hm : ∀ u ∈ U, ρ u (ρ w v) = ρ w v := fun u hu => by
      rw [hρ.comm h, h.sq_swap (hw u hu), one_smul, hv u hu]
    have h0 : ∑ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 (ρ w v) = 0 := by
      by_contra hne
      exact hcon ⟨_, N.sum_mem fun q _ => N.smul_mem _ (hN _ _ (hN _ _ hvN)), hne, average hρ hα U hU _ hm⟩
    refine hρ.eq_zero h (x := w) ?_
    rw [map_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hρ.comm h q.out.1 w, map_smul, map_smul, smul_comm]
  let χ : A ⧸ U.addSubgroupOf A → (Multiplicative (h.perp U) →* ℂ) := fun q =>
    { toFun := fun w => c q.out.1 w.toAdd.1 ^ 2
      map_one' := by simp [h.zero_right]
      map_mul' := fun x y => by simp [h.right, mul_pow] }
  have hχ : Function.Injective χ := by
    intro p q hpq
    rw [← p.out_eq, ← q.out_eq]
    refine QuotientAddGroup.eq.2 (h.perp_perp_perp T _ fun w hw => ?_)
    have h1 : c p.out.1 w ^ 2 = c q.out.1 w ^ 2 := DFunLike.congr_fun hpq (Multiplicative.ofAdd ⟨w, hw⟩)
    have h2 := h.left (-p.out.1) p.out.1 w
    rw [neg_add_cancel, h.zero_left] at h2
    show c (-p.out.1 + q.out.1) w ^ 2 = 1
    rw [h.left, mul_pow, ← h1, ← mul_pow, ← h2, one_pow]
  have hli := (linearIndependent_monoidHom (Multiplicative (h.perp U)) ℂ).comp χ hχ
  have hq : ∀ q : A ⧸ U.addSubgroupOf A, (α q.out.1)⁻¹ • ρ q.out.1 v = 0 := by
    intro q
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
    refine Fintype.linearIndependent_iff.1 hli (fun q => φ ((α q.out.1)⁻¹ • ρ q.out.1 v)) ?_ q
    funext w
    have := congrArg φ (hz w.toAdd.1 w.toAdd.2)
    rw [map_sum, map_zero] at this
    rw [Finset.sum_apply, Pi.zero_apply, ← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [φ.map_smul (c q.out.1 w.toAdd.1 ^ 2), smul_eq_mul, mul_comm]
    rfl
  have := (smul_eq_zero.1 (hq 0)).resolve_left (inv_ne_zero (hα.ne _ (Quotient.out (0 : A ⧸ U.addSubgroupOf A)).2))
  exact hv0 (hρ.eq_zero h this)

theorem eq_zero_of_sum {ι : Type} (s : Finset ι) (β : ι → W → ℂ) (hβ : ∀ i, ∃ a ∈ A, β i a ≠ α a) :
    ∀ (m : ι → M), (∀ i, ∀ a ∈ A, ρ a (m i) = β i a • m i) →
      (∀ a ∈ A, ρ a (∑ i ∈ s, m i) = α a • ∑ i ∈ s, m i) → ∑ i ∈ s, m i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _ _; simp
  | insert j s hj ih =>
    intro m hm hv
    obtain ⟨a, ha, hne⟩ := hβ j
    have key : ∑ i ∈ s, (β i a - β j a) • m i = (α a - β j a) • ∑ i ∈ insert j s, m i := by
      rw [sub_smul, ← hv a ha, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hj, hm j a ha, sub_self,
        zero_add]
      exact Finset.sum_congr rfl fun i _ => by rw [hm i a ha, sub_smul]
    have := ih (fun i => (β i a - β j a) • m i) (fun i b hb => by rw [map_smul, hm i b hb, smul_comm])
      (fun b hb => by rw [key, map_smul, hv b hb, smul_comm])
    rw [key] at this
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)

theorem eigen_line (h : Alt c) (hρ : Ops c ρ) (hα : Splits c A α) (hA : h.perp A ≤ A) {e : M}
    (he : ∀ a ∈ A, ρ a e = α a • e) {v : M} (hv : v ∈ Submodule.span ℂ (Set.range fun x => ρ x e))
    (hva : ∀ a ∈ A, ρ a v = α a • v) : ∃ r : ℂ, v = r • e := by
  classical
  obtain ⟨f, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  rw [Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ A)] at hva ⊢
  have h1 : ∑ x ∈ f.support with x ∈ A, f x • ρ x e = (∑ x ∈ f.support with x ∈ A, f x * α x) • e := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun x hx => by rw [he x (Finset.mem_filter.1 hx).2, smul_smul]
  rw [h1] at hva ⊢
  refine ⟨_, add_eq_left.2 ?_⟩
  have h2 : ∑ x ∈ f.support with x ∉ A, f x • ρ x e = ∑ x ∈ f.support.subtype (· ∉ A), f x.1 • ρ x.1 e :=
    (Finset.sum_subtype_eq_sum_filter fun x => f x • ρ x e).symm
  rw [h2] at hva ⊢
  refine eq_zero_of_sum (ρ := ρ) (A := A) (α := α) _ (fun x a => c a x.1 ^ 2 * α a) (fun x => ?_) _ (fun x a ha => ?_) fun a ha => ?_
  · by_contra hc
    push Not at hc
    exact x.2 (hA fun a ha => h.sq_swap ((mul_eq_right₀ (hα.ne a ha)).1 (hc a ha)))
  · rw [map_smul, hρ.comm h, he a ha, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1; ring
  · have := hva a ha
    rwa [map_add, map_smul, he a ha, smul_add, smul_comm, add_right_inj] at this

theorem exists_selfDual (h : Alt c) (L : AddSubgroup W) (hL : L ≤ h.perp L) :
    ∃ A : AddSubgroup W, L ≤ A ∧ A ≤ h.perp A ∧ h.perp A ≤ A := by
  obtain ⟨A, hLA, hA, hmax⟩ := zorn_le_nonempty₀ {A : AddSubgroup W | A ≤ h.perp A} (fun s hs hch y hy => by
    refine ⟨sSup s, fun a ha b hb => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨P, hP, ha⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 ha
    obtain ⟨Q, hQ, hb⟩ := (AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hb
    obtain ⟨R, hR, h1, h2⟩ := hch.directedOn P hP Q hQ
    exact hs hR (h1 ha) b (h2 hb)) L hL
  refine ⟨A, hLA, hA, fun x hx => ?_⟩
  have h1 : AddSubgroup.closure (insert x (A : Set W)) ≤ h.perp (insert x (A : Set W)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro a (rfl | ha) b (rfl | hb)
    · rw [h.self, one_pow]
    · exact hx b hb
    · exact h.sq_swap (hx a ha)
    · exact hA ha b hb
  have h2 : AddSubgroup.closure (insert x (A : Set W)) ≤ h.perp (AddSubgroup.closure (insert x (A : Set W))) :=
    (AddSubgroup.closure_le _).2 fun a ha b hb => h.sq_swap (h1 hb a ha)
  exact hmax h2 (fun a ha => AddSubgroup.subset_closure (Or.inr ha)) (AddSubgroup.subset_closure (Or.inl rfl))

@[ext] structure Tw {A : Type} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ) (hb : ∀ x y, b x y = b y x) where

  pt : A

  sc : Additive ℂˣ

instance {A : Type} [AddCommGroup A] (b : A →+ A →+ Additive ℂˣ) (hb : ∀ x y, b x y = b y x) : AddCommGroup (Tw b hb) :=
  letI : Add (Tw b hb) := ⟨fun g k => ⟨g.pt + k.pt, g.sc + k.sc + b g.pt k.pt⟩⟩
  letI : Zero (Tw b hb) := ⟨⟨0, 0⟩⟩
  letI : Neg (Tw b hb) := ⟨fun g => ⟨-g.pt, -g.sc + b g.pt g.pt⟩⟩
  { AddGroup.ofLeftAxioms (G := Tw b hb)
      (fun x y z => Tw.ext (add_assoc _ _ _) (by
        show x.sc + y.sc + b x.pt y.pt + z.sc + b (x.pt + y.pt) z.pt = x.sc + (y.sc + z.sc + b y.pt z.pt) + b x.pt (y.pt + z.pt)
        simp only [map_add, AddMonoidHom.add_apply]; abel))
      (fun x => Tw.ext (zero_add _) (by
        show 0 + x.sc + b 0 x.pt = x.sc
        simp))
      (fun x => Tw.ext (neg_add_cancel _) (by
        show -x.sc + b x.pt x.pt + x.sc + b (-x.pt) x.pt = 0
        simp only [map_neg, AddMonoidHom.neg_apply]; abel)) with
    add_comm := fun x y => Tw.ext (add_comm _ _) (by
      show x.sc + y.sc + b x.pt y.pt = y.sc + x.sc + b y.pt x.pt
      rw [hb, add_comm x.sc]) }

theorem baer_units : Module.Baer ℤ (Additive ℂˣ) := by
  let : DivisibleBy (Additive ℂˣ) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn z => by
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z.toMul : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact z.toMul.ne_zero (by rw [← hw, zero_pow hn])
    exact ⟨Additive.ofMul (Units.mk0 w hw0), Additive.toMul.injective (Units.ext (by simpa using hw))⟩
  let := AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)
  exact Module.Baer.of_divisible _

theorem exists_splits (h : Alt c) {L A : AddSubgroup W} (hLA : L ≤ A) (hL : ∀ x ∈ L, ∀ y ∈ L, c x y = 1) (hA : A ≤ h.perp A) :
    ∃ α : W → ℂ, Splits c A α ∧ ∀ x ∈ L, α x = 1 := by
  classical
  let b : A →+ A →+ Additive ℂˣ := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (Units.mk0 (c x y) (h.ne _ _)))
      fun y z => Additive.toMul.injective (Units.ext (by simp [h.right])))
    fun x y => by
      ext z
      simp [h.left]
  have hbv : ∀ x y, ((b x y).toMul : ℂ) = c x y := fun x y => rfl
  have hb : ∀ x y, b x y = b y x := fun x y => Additive.toMul.injective (Units.ext (by
    rw [hbv, hbv]
    exact mul_left_cancel₀ (h.ne x y) (by rw [h.anti, ← pow_two]; exact hA x.2 y y.2)))
  let f : L × Additive ℂˣ →+ Tw b hb := AddMonoidHom.mk' (fun p => ⟨⟨p.1, hLA p.1.2⟩, p.2⟩) fun p q => Tw.ext rfl (by
    show p.2 + q.2 = p.2 + q.2 + b _ _
    rw [left_eq_add]
    exact Additive.toMul.injective (Units.ext (hL _ p.1.2 _ q.1.2)))
  have hf : Function.Injective f := fun p q hpq =>
    Prod.ext (Subtype.ext (congrArg (fun g : Tw b hb => g.pt.1) hpq)) (congrArg Tw.sc hpq)
  obtain ⟨g, hg⟩ := baer_units.extension_property_addMonoidHom f hf (AddMonoidHom.snd _ _)
  have hg' : ∀ p, g (f p) = p.2 := fun p => DFunLike.congr_fun hg p
  refine ⟨fun x => if hx : x ∈ A then ((g ⟨⟨x, hx⟩, 0⟩).toMul : ℂ) else 1, ⟨fun a ha => ?_, fun a ha a' ha' => ?_⟩, fun x hx => ?_⟩
  · simp [ha]
  · rw [dif_pos ha, dif_pos ha', dif_pos (A.add_mem ha ha')]
    have h1 : (⟨⟨a, ha⟩, 0⟩ + ⟨⟨a', ha'⟩, 0⟩ : Tw b hb) = f (0, b ⟨a, ha⟩ ⟨a', ha'⟩) + ⟨⟨a + a', A.add_mem ha ha'⟩, 0⟩ :=
      Tw.ext (Subtype.ext (zero_add _).symm) (by
        show 0 + 0 + b ⟨a, ha⟩ ⟨a', ha'⟩ = b ⟨a, ha⟩ ⟨a', ha'⟩ + 0 + b 0 _
        simp)
    have h2 := congrArg (fun t => ((g t).toMul : ℂ)) h1
    simpa only [map_add, toMul_add, Units.val_mul, hg', hbv] using h2
  · beta_reduce
    rw [dif_pos (hLA hx)]
    exact congrArg (fun t : Additive ℂˣ => (t.toMul : ℂ)) (hg' (⟨x, hx⟩, 0))

def transl (c : W → W → ℂ) (x : W) : Module.End ℂ (W → ℂ) where
  toFun f z := c z x * f (z + x)
  map_add' f g := by funext z; simp [mul_add]
  map_smul' r f := by funext z; simp; ring

theorem ops_transl (h : Alt c) : Ops c (transl c) where
  zero v := by funext z; simp [transl, h.zero_right]
  mul x y v := by funext z; simp [transl, h.left, h.right, add_assoc]; ring

theorem transl_indicator (hα : Splits c A α) (a : W) (ha : a ∈ A) :
    transl c a ((A : Set W).indicator α) = α a • (A : Set W).indicator α := by
  funext z
  show c z a * (A : Set W).indicator α (z + a) = α a * (A : Set W).indicator α z
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem (A.add_mem hz ha), Set.indicator_of_mem hz, mul_comm (α a), hα.mul z hz a ha]
  · have : z + a ∉ A := fun h => hz (by simpa using A.sub_mem h ha)
    simp [hz, this]

end Abstract

section Local

theorem eq_one_of_pow_near {u : ℂ} (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1 / 2) : u = 1 := by
  first
  | exact @_root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close
  | exact _root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close
  | (apply _root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqOneOfPowerClose.eq_one_of_pow_close ..)

theorem finite_quot {W : Type} [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] (A U : AddSubgroup W)
    (hU : (U : Set W) ∈ 𝓝 0) {K : Set W} (hK : IsCompact K) (hA : (A : Set W) ⊆ K) : Finite (A ⧸ U.addSubgroupOf A) := by
  have := QuotientAddGroup.discreteTopology (U.isOpen_of_mem_nhds hU)
  have hfin : ((QuotientAddGroup.mk : W → W ⧸ U) '' K).Finite := (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image (f := fun q : A ⧸ U.addSubgroupOf A => (q.out.1 : W ⧸ U))
    (hfin.subset ?_) fun p _ q _ hpq => ?_)
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨_, hA q.out.2, rfl⟩
  · rw [← p.out_eq, ← q.out_eq]
    have := QuotientAddGroup.eq.1 hpq
    exact QuotientAddGroup.eq.2 this

open ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_int : IsCompact (𝒪[F] : Set F) := IsNonarchimedeanLocalField.isCompact_closedBall F 1

theorem int_mem_nhds : (𝒪[F] : Set F) ∈ 𝓝 (0 : F) :=
  (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.2 ⟨1, one_ne_zero, fun _ hx => le_of_lt (α := ValueGroupWithZero F) hx⟩

theorem exists_ne_zero {p : F → Prop} (hp : ∀ᶠ r in 𝓝 (0 : F), p r) : ∃ r, r ≠ 0 ∧ p r := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 hp
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  refine ⟨y * r, mul_ne_zero (by simpa using hγ) hr, hs ?_⟩
  show valuation F (y * r) < valuation F y
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1

theorem eventually_psi {ψ : AddChar F ℂ} (hψ : Continuous ψ) : ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ 𝒪[F], ψ (o * z) = 1 := by
  have h1 : ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ (𝒪[F] : Set F), ‖ψ (o * z) - 1‖ < 1 / 2 := by
    refine isCompact_int.eventually_forall_of_forall_eventually fun o _ => ?_
    have hc : Continuous fun z : F × F => ‖ψ (z.2 * z.1) - 1‖ := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h1] with z hz o ho
  refine eq_one_of_pow_near fun n => ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← mul_assoc]
  exact hz _ (mul_mem (natCast_mem _ n) ho)

theorem eventually_psi' {ψ : AddChar F ℂ} (hψ : Continuous ψ) : ∀ᶠ z in 𝓝 (0 : F), ψ z = 1 := by
  filter_upwards [eventually_psi hψ] with z hz
  simpa using hz 1 (one_mem _)

variable {W : Type} [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem alt_psi (hB : B.IsAlt) (ψ : AddChar F ℂ) : Alt fun x y => ψ (B x y / 2) where
  left x y z := by rw [← AddChar.map_add_eq_mul, ← add_div]; simp
  right x y z := by rw [← AddChar.map_add_eq_mul, ← add_div]; simp
  self x := by rw [hB.self_eq_zero]; simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem psi_sq (h2 : (2 : F) ≠ 0) (ψ : AddChar F ℂ) (t : F) : ψ (t / 2) ^ 2 = ψ t := by
  rw [pow_two, ← AddChar.map_add_eq_mul]; congr 1; field_simp; ring

variable [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]

theorem exists_data (h2 : (2 : F) ≠ 0) (hB : B.IsAlt) (hn : B.Nondegenerate) {ψ : AddChar F ℂ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) :
    ∃ (A : AddSubgroup W) (α : W → ℂ), Splits (fun x y => ψ (B x y / 2)) A α ∧ (alt_psi hB ψ).perp A ≤ A ∧
      (∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1) ∧
      (∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A)) ∧
      ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1 := by
  classical
  have := IsModuleTopology.topologicalAddGroup F W
  have := IsModuleTopology.toContinuousSMul (R := F) (A := W)
  set h := alt_psi hB ψ
  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (AddChar.ext _ _ hc)
  have ht0 : t₀ ≠ 0 := by rintro rfl; simp at ht₀
  let b := Module.finBasis F W
  let b' := B.dualBasis hn b
  have hcB : Continuous fun p : W × W => B p.1 p.2 := IsModuleTopology.continuous_bilinear_of_finite_left B
  have hcw : ∀ w, Continuous fun u => B u w := fun w => hcB.comp (f := fun u => (u, w)) (by fun_prop)
  let K : Set W := b'.equivFun.symm '' Set.pi Set.univ fun _ => (𝒪[F] : Set F)
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_int).image
    (IsModuleTopology.continuous_of_linearMap b'.equivFun.symm.toLinearMap)
  let T : F → Set W := fun s => {t | ∃ i, ∃ o ∈ 𝒪[F], t = (s * o) • b i}
  have hmem : ∀ s x, x ∈ h.perp (T s) ↔ ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
    intro s x
    have e : ∀ i o, ψ (B x ((s * o) • b i) / 2) ^ 2 = ψ (o * (s * B x (b i))) := fun i o => by
      rw [psi_sq h2, map_smul, smul_eq_mul]; congr 1; ring
    constructor
    · intro hx i o ho
      rw [← e]; exact hx _ ⟨i, o, ho, rfl⟩
    · rintro hx _ ⟨i, o, ho, rfl⟩
      exact (e i o).trans (hx i o ho)
  have fA : ∀ r, r ≠ 0 → ∀ x ∈ h.perp (T (t₀ / r)), ∃ y ∈ K, x = r • y := by
    intro r hr x hx
    refine ⟨r⁻¹ • x, ⟨fun i => r⁻¹ * B x (b i), fun i _ => ?_, ?_⟩, by rw [smul_inv_smul₀ hr]⟩
    · by_contra hc
      have hz : r⁻¹ * B x (b i) ≠ 0 := fun h0 => hc (by beta_reduce; rw [h0]; exact zero_mem _)
      have hi : (r⁻¹ * B x (b i))⁻¹ ∈ 𝒪[F] := ((valuation F).valuationSubring.mem_or_inv_mem _).resolve_left hc
      have := (hmem _ x).1 hx i _ hi
      apply ht₀
      rw [← this]; congr 1
      have := right_ne_zero_of_mul hz
      field_simp
    · rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [b']
  have fB : ∀ s, (h.perp (T s) : Set W) ∈ 𝓝 0 := by
    intro s
    have : ∀ᶠ x in 𝓝 (0 : W), ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
      refine eventually_all.2 fun i => ?_
      have hc : Continuous fun x => s * B x (b i) := continuous_const.mul (hcw _)
      exact (hc.tendsto' 0 0 (by simp)).eventually (eventually_psi hψ)
    filter_upwards [this] with x hx using (hmem s x).2 hx
  have fC : ∀ N ∈ 𝓝 (0 : W), ∀ C, IsCompact C → ∃ r : F, r ≠ 0 ∧ ∀ y ∈ C, r • y ∈ N := by
    intro N hN C hC
    refine exists_ne_zero (hC.eventually_forall_of_forall_eventually fun y _ => ?_)
    exact (continuous_smul.tendsto' ((0 : F), y) 0 (by simp)).eventually hN
  obtain ⟨r, hr, hrK⟩ : ∃ r : F, r ≠ 0 ∧ ∀ p ∈ K ×ˢ K, ψ (r * r * B p.1 p.2 / 2) = 1 := by
    refine exists_ne_zero ((hK.prod hK).eventually_forall_of_forall_eventually fun p _ => ?_)
    have hc : Continuous fun z : F × W × W => z.1 * z.1 * B z.2.1 z.2.2 / 2 :=
      ((continuous_fst.mul continuous_fst).mul (hcB.comp continuous_snd)).div_const 2
    exact (hc.tendsto' (0, p) 0 (by simp)).eventually (eventually_psi' hψ)
  set L := h.perp (T (t₀ / r))
  have hL : ∀ x ∈ L, ∀ y ∈ L, ψ (B x y / 2) = 1 := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := fA r hr x hx
    obtain ⟨y', hy', rfl⟩ := fA r hr y hy
    rw [← hrK (x', y') ⟨hx', hy'⟩]; congr 2; simp; ring
  obtain ⟨A, hLA, hA, hA'⟩ := exists_selfDual h L fun x hx y hy => by simp only [hL x hx y hy, one_pow]
  obtain ⟨α, hα, hαL⟩ := exists_splits h hLA hL hA
  obtain ⟨s, hs, hsL⟩ := fC _ (fB (t₀ / r)) (⋃ i, (fun o : F => o • b i) '' (𝒪[F] : Set F))
    (isCompact_iUnion fun i => isCompact_int.image (by fun_prop))
  have hAK : (A : Set W) ⊆ (fun y => (t₀ / s) • y) '' K := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := fA (t₀ / s) (div_ne_zero ht0 hs) a (by
      rintro _ ⟨i, o, ho, rfl⟩
      refine hA ha _ (hLA ?_)
      rw [div_div_cancel₀ ht0, mul_smul]
      exact hsL _ (Set.mem_iUnion.2 ⟨i, o, ho, rfl⟩))
    exact ⟨y, hy, rfl⟩
  refine ⟨A, α, hα, hA', ?_, fun N hN => ?_, fun w => ?_⟩
  · filter_upwards [fB (t₀ / r)] with u hu using ⟨hLA hu, hαL u hu⟩
  · obtain ⟨q, hq, hqN⟩ := fC N hN K hK
    refine ⟨T (t₀ / q), fun x hx => ?_, finite_quot A _ (fB _) (hK.image (by fun_prop)) hAK⟩
    obtain ⟨y, hy, rfl⟩ := fA q hq x hx
    exact hqN y hy
  · filter_upwards [((hcw w).tendsto' 0 0 (by simp)).eventually (eventually_psi' hψ)] with u hu
    rw [psi_sq h2, hu]

end Local

section Group

open Heisenberg

variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}

theorem apply_eq (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) (g : Heisenberg B) (v : M) : π g v = ψ g.cen • π ⟨g.vec, 0⟩ v := by
  rw [← hπ, ← Module.End.mul_apply, ← map_mul]
  congr 2
  ext <;> simp

theorem ops_of_central (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) : Ops (fun x y => ψ (B x y / 2)) fun x => π ⟨x, 0⟩ where
  zero v := by rw [hπ]; simp
  mul x y v := by rw [← Module.End.mul_apply, ← map_mul, apply_eq hπ]; simp

def funRep (hB : B.IsAlt) (ψ : AddChar F ℂ) : Representation ℂ (Heisenberg B) (W → ℂ) where
  toFun g := ψ g.cen • transl (fun x y => ψ (B x y / 2)) g.vec
  map_one' := LinearMap.ext fun v => by simp [(ops_transl (alt_psi hB ψ)).zero]
  map_mul' g k := LinearMap.ext fun v => by
    simp only [mul_cen, mul_vec, AddChar.map_add_eq_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul,
      (ops_transl (alt_psi hB ψ)).mul, smul_smul]
    congr 1; ring

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]

theorem _root_.GlobalTheory.Published.Heisenberg.isTopologicalGroup : IsTopologicalGroup (Heisenberg B) := by
  have := IsModuleTopology.topologicalAddGroup F W
  have hcB : Continuous fun p : W × W => B p.1 p.2 := IsModuleTopology.continuous_bilinear_of_finite_left B
  have h0 : Continuous fun g : Heisenberg B => (g.vec, g.cen) := continuous_induced_dom
  have h1 : Continuous (Heisenberg.vec : Heisenberg B → W) := h0.fst
  have h2 : Continuous (Heisenberg.cen : Heisenberg B → F) := h0.snd
  exact
    { continuous_mul := continuous_induced_rng.2 (((h1.comp continuous_fst).add (h1.comp continuous_snd)).prodMk
        (((h2.comp continuous_fst).add (h2.comp continuous_snd)).add
          ((hcB.comp ((h1.comp continuous_fst).prodMk (h1.comp continuous_snd))).div_const 2)))
      continuous_inv := continuous_induced_rng.2 (h1.neg.prodMk (h2.neg.add ((hcB.comp (h1.prodMk h1)).div_const 2))) }

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [IsModuleTopology F W] in
theorem eventually_fix (hs : PRep.IsSmooth π) (v : M) : ∀ᶠ u in 𝓝 (0 : W), π ⟨u, 0⟩ v = v := by
  have hc : Continuous fun u : W => (⟨u, 0⟩ : Heisenberg B) := continuous_induced_rng.2 (continuous_id.prodMk continuous_const)
  exact ((hs v).preimage hc).mem_nhds (show π 1 v = v by simp)

theorem isSmooth_of_eventually (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v)
    (hs : ∀ v, ∀ᶠ u in 𝓝 (0 : W), π ⟨u, 0⟩ v = v) : PRep.IsSmooth π := by
  intro v
  have := Heisenberg.isTopologicalGroup (B := B)
  have h0 : Continuous fun g : Heisenberg B => (g.vec, g.cen) := continuous_induced_dom
  let S : Subgroup (Heisenberg B) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {x y} hx hy => by
        show π (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        show π x⁻¹ v = v
        conv_lhs => rw [← show π x v = v from hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  filter_upwards [(h0.fst.tendsto' 1 0 rfl).eventually (hs v), (h0.snd.tendsto' 1 0 rfl).eventually (eventually_psi' hψ)]
    with g h1 h2
  show π g v = v
  rw [apply_eq hπ, h1, h2, one_smul]

variable (hB : B.IsAlt) {A : AddSubgroup W} {α : W → ℂ} (hα : Splits (fun x y => ψ (B x y / 2)) A α)
  (hA : (alt_psi hB ψ).perp A ≤ A) (h1 : ∀ᶠ u in 𝓝 (0 : W), u ∈ A ∧ α u = 1)
  (h2 : ∀ N ∈ 𝓝 (0 : W), ∃ T, ((alt_psi hB ψ).perp T : Set W) ⊆ N ∧ Finite (A ⧸ ((alt_psi hB ψ).perp T).addSubgroupOf A))
  (h3 : ∀ w, ∀ᶠ u in 𝓝 (0 : W), ψ (B u w / 2) ^ 2 = 1)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [IsModuleTopology F W] in
include hα h1 h2 in
theorem exists_eigen_mem (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) (hs : PRep.IsSmooth π) (P : Subrepresentation π) (hP : P ≠ ⊥) :
    ∃ e ∈ P.toSubmodule, e ≠ 0 ∧ ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e := by
  have : P.toSubmodule ≠ ⊥ := fun h => hP (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
  obtain ⟨T, hT, hfin⟩ := h2 _ (h1.and (eventually_fix hs v))
  exact exists_eigen (alt_psi hB ψ) (ops_of_central hπ) hα T (fun u hu => (hT hu).1.2) P.toSubmodule
    (fun x m hm => P.apply_mem_toSubmodule _ hm) v hv hv0 fun u hu => (hT hu).2

include hα hA h1 h2 h3 in

theorem irr_of_span (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) {e : M} (he0 : e ≠ 0)
    (he : ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e) (hsp : Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e) = ⊤) : IsIrrSmoothOf ψ π := by
  have hs : PRep.IsSmooth π := by
    refine isSmooth_of_eventually hψ hπ fun v => ?_
    have hv : v ∈ Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e) := hsp ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨x, rfl⟩ := hx
      filter_upwards [h1, h3 x] with u hu hu'
      have := (ops_of_central hπ).comm (alt_psi hB ψ) u x e
      beta_reduce at this ⊢
      rw [this, hu', he u hu.1, hu.2, one_smul, one_smul]
    | zero => simp
    | add a b _ _ ha hb => filter_upwards [ha, hb] with u ha hb using by rw [map_add, ha, hb]
    | smul r a _ ha => filter_upwards [ha] with u ha using by rw [map_smul, ha]
  refine ⟨hs, ?_, hπ⟩
  have : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun h => he0 (by
    have : e ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ Submodule.mem_top
    exact this)⟩
  refine ⟨fun P => or_iff_not_imp_left.2 fun hP => ?_⟩
  obtain ⟨e', hP', he0', he'⟩ := exists_eigen_mem hB hα h1 h2 hπ hs P hP
  obtain ⟨r, rfl⟩ := eigen_line (alt_psi hB ψ) (ops_of_central hπ) hα hA he (v := e') (hsp ▸ Submodule.mem_top) he'
  have heP : e ∈ P.toSubmodule := (Submodule.smul_mem_iff _ (left_ne_zero_of_smul he0')).1 hP'
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 ?_)
  rw [← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact P.apply_mem_toSubmodule _ heP

include hα hA h1 h2 h3 in

theorem exists_irr_sub (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v) {e : M} (he0 : e ≠ 0)
    (he : ∀ a ∈ A, π ⟨a, 0⟩ e = α a • e) :
    ∃ P : Subrepresentation π, e ∈ P.toSubmodule ∧ IsIrrSmoothOf ψ P.toRepresentation := by
  let N := Submodule.span ℂ (Set.range fun x => π ⟨x, 0⟩ e)
  have hN : ∀ g, ∀ v ∈ N, π g v ∈ N := by
    intro g v hv
    have : N.map (π g) ≤ N := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      beta_reduce
      rw [← Module.End.mul_apply, ← map_mul, apply_eq hπ]
      exact N.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    exact this ⟨v, hv, rfl⟩
  have heN : e ∈ N := Submodule.subset_span ⟨0, (ops_of_central hπ).zero e⟩
  refine ⟨⟨N, fun g v hv => hN g v hv⟩, heN, irr_of_span hB hα hA h1 h2 h3 hψ (fun t v => Subtype.ext (hπ t v.1)) (e := ⟨e, heN⟩)
    (fun h => he0 (congrArg Subtype.val h)) (fun a ha => Subtype.ext (he a ha)) ?_⟩
  apply Submodule.map_injective_of_injective N.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

end Group

end SvN

theorem StoneVonNeumann_holds : StoneVonNeumann := by
  intro F _ _ _ _ h2 W _ _ _ _ _ B hB hn ψ hψ hψ1
  obtain ⟨A, α, hα, hA, k1, k2, k3⟩ := SvN.exists_data h2 hB hn hψ hψ1
  constructor
  · obtain ⟨P, -, hP⟩ := SvN.exists_irr_sub (π := SvN.funRep hB ψ) hB hα hA k1 k2 k3 hψ
      (fun t v => by simp [SvN.funRep, (SvN.ops_transl (SvN.alt_psi hB ψ)).zero]) (e := (A : Set W).indicator α)
      (fun h => hα.ne 0 A.zero_mem (by simpa using congrFun h 0))
      (fun a ha => by simpa [SvN.funRep] using SvN.transl_indicator hα a ha)
    exact ⟨_, _, _, _, hP⟩
  · intro S S' _ _ _ _ ρ ρ' hρ hρ'
    have i1 := hρ.2.1
    have i2 := hρ'.2.1
    obtain ⟨e, -, he0, he⟩ := SvN.exists_eigen_mem hB hα k1 k2 hρ.2.2 hρ.1 ⊤ top_ne_bot
    obtain ⟨e', -, he0', he'⟩ := SvN.exists_eigen_mem hB hα k1 k2 hρ'.2.2 hρ'.1 ⊤ top_ne_bot
    obtain ⟨P, heP, hP⟩ := SvN.exists_irr_sub (π := ρ.prod ρ') hB hα hA k1 k2 k3 hψ
      (fun t v => Prod.ext (hρ.2.2 t v.1) (hρ'.2.2 t v.2)) (e := (e, e'))
      (fun h => he0 (congrArg Prod.fst h)) (fun a ha => Prod.ext (he a ha) (he' a ha))
    have i3 := hP.2.1
    let f : P.toRepresentation.IntertwiningMap ρ :=
      ⟨(LinearMap.fst ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    let f' : P.toRepresentation.IntertwiningMap ρ' :=
      ⟨(LinearMap.snd ℂ S S').comp P.toSubmodule.subtype, fun g => LinearMap.ext fun v => rfl⟩
    have hf := (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right fun h =>
      he0 (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ => k ⟨_, heP⟩) h)
    have hf' := (Representation.IsIrreducible.bijective_or_eq_zero f').resolve_right fun h =>
      he0' (congrArg (fun k : P.toRepresentation.IntertwiningMap ρ' => k ⟨_, heP⟩) h)
    exact ⟨(f.ofBijective hf).symm.trans (f'.ofBijective hf')⟩

namespace SvN

open ValuativeRel

theorem exists_char (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  let O : AddSubgroup F := (𝒪[F]).toAddSubgroup
  have hx : r⁻¹ ∉ O := fun h => by
    have h' : valuation F r⁻¹ ≤ 1 := h
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 (by simpa using hr))] at h'
    exact absurd hr1 (not_lt.2 h')
  have hx' : ((r⁻¹ : F) : F ⧸ O) ≠ 0 := fun h => hx ((QuotientAddGroup.eq_zero_iff _).1 h)
  obtain ⟨g, hg⟩ : ∃ g : F ⧸ O →+ Additive ℂˣ, g (r⁻¹ : F) ≠ 0 := by
    obtain ⟨χ, hχ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx'
    let j : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) := QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
      rintro _ ⟨k, rfl⟩
      exact ⟨k, by simp⟩)
    have hj : ∀ x, j x = 0 → x = 0 := by
      intro x
      induction x using QuotientAddGroup.induction_on with
      | H q =>
        intro h
        obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 (show ((q : ℝ) : AddCircle (1 : ℝ)) = 0 from h)
        refine (QuotientAddGroup.eq_zero_iff _).2 ⟨k, ?_⟩
        have : ((k : ℚ) : ℝ) = q := by simpa using hk
        simpa using (by exact_mod_cast this : (k : ℚ) = q)
    refine ⟨AddMonoidHom.mk' (fun x => Additive.ofMul (Circle.toUnits (AddCircle.toCircle (j (χ x))))) fun a b => by
      rw [map_add, map_add, AddCircle.toCircle_add, map_mul, ofMul_mul], fun h => hχ (hj _ ?_)⟩
    refine AddCircle.injective_toCircle one_ne_zero (Subtype.ext ?_)
    rw [AddCircle.toCircle_zero]
    exact congrArg (fun t : Additive ℂˣ => (t.toMul : ℂ)) h
  have := QuotientAddGroup.discreteTopology (O.isOpen_of_mem_nhds int_mem_nhds)
  refine ⟨{ toFun := fun t => ((g t).toMul : ℂ), map_zero_eq_one' := by simp, map_add_eq_mul' := fun a b => by simp }, ?_, fun h => hg ?_⟩
  · exact (continuous_of_discreteTopology (f := fun q : F ⧸ O => ((g q).toMul : ℂ))).comp QuotientAddGroup.continuous_mk
  · exact Additive.toMul.injective (Units.ext (DFunLike.congr_fun h r⁻¹))

def planeForm (F : Type) [Field F] : LinearMap.BilinForm F (F × F) :=
  LinearMap.mk₂ F (fun x y => x.1 * y.2 - x.2 * y.1) (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

theorem planeForm_isAlt (F : Type) [Field F] : (planeForm F).IsAlt := fun x => by simp [planeForm, mul_comm]

theorem planeForm_nondegenerate (F : Type) [Field F] : (planeForm F).Nondegenerate := by
  constructor <;> intro x hx <;> have h1 := hx (1, 0) <;> have h2 := hx (0, 1) <;> simp [planeForm] at h1 h2 <;>
    exact Prod.ext (by assumption) (by assumption)

theorem plane_model (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (h2 : (2 : F) ≠ 0) :
    (∃ g k : Heisenberg (planeForm F), g * k ≠ k * g) ∧
    ∃ ψ : AddChar F ℂ, Continuous ψ ∧ ψ ≠ 1 ∧ ∃ (S : Type) (_ : AddCommGroup S) (_ : Module ℂ S)
      (ρ : Representation ℂ (Heisenberg (planeForm F)) S), Heisenberg.IsIrrSmoothOf ψ ρ := by
  refine ⟨⟨_, _, Heisenberg.mul_ne_mul h2 (planeForm_isAlt F) (x := (1, 0)) (y := (0, 1)) (by simp [planeForm])⟩, ?_⟩
  obtain ⟨ψ, h, h'⟩ := exists_char F
  exact ⟨ψ, h, h', (StoneVonNeumann_holds F h2 (F × F) _ (planeForm_isAlt F) (planeForm_nondegenerate F) ψ h h').1⟩

end SvN

end GlobalTheory.Published

end
