import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBaseChangeQuotientOfMapMaximalIdeal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SelmerLevel

section Comp

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
  (b : Module.Basis ι O O')

structure Comp (A A' : Type) [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A'] where
  inc : A →+ A'
  p : ι → A' →+ A
  sum_p : ∀ x, ∑ a, b a • inc (p a x) = x
  p_inc : ∀ a c x, p a (c • inc x) = b.repr c a • x

def Comp.self : Comp b O O' where
  inc := (algebraMap O O').toAddMonoidHom
  p a := (b.coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm]
  p_inc a c x := by
    have : c • (algebraMap O O').toAddMonoidHom x = x • c := by simp [Algebra.smul_def, mul_comm]
    rw [this]; simp [mul_comm]

variable {b} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']

namespace Comp

variable (S : Comp b A A')

theorem ext_p {x y : A'} (h : ∀ a, S.p a x = S.p a y) : x = y := by
  rw [← S.sum_p x, ← S.sum_p y]; simp [h]

theorem p_inc' (a : ι) (x : A) : S.p a (S.inc x) = b.repr 1 a • x := by
  rw [← S.p_inc, one_smul]

theorem p_sum (m : ι → A) (a : ι) : S.p a (∑ a', b a' • S.inc (m a')) = m a := by
  classical
  simp [map_sum, S.p_inc, Finsupp.single_apply]

theorem inc_smul (o : O) (x : A) : S.inc (o • x) = algebraMap O O' o • S.inc x := by
  refine S.ext_p fun a => ?_
  rw [S.p_inc', S.p_inc, Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply,
    smul_eq_mul, smul_smul, mul_comm]

theorem p_smul (a : ι) (o : O) (x : A') : S.p a (algebraMap O O' o • x) = o • S.p a x := by
  classical
  conv_lhs => rw [← S.sum_p x]
  simp [Finset.smul_sum, smul_smul, S.p_inc, ← Algebra.smul_def, Finsupp.single_apply]

include S in
theorem length_eq : Module.length O' A' = Module.length O' (O' ⊗[O] A) := by
  letI : Module O A' := Module.compHom A' (algebraMap O O')
  haveI : IsScalarTower O O' A' := ⟨fun o c x => by
    change (o • c) • x = algebraMap O O' o • c • x
    rw [Algebra.smul_def, mul_smul]⟩
  let f : A →ₗ[O] A' := { S.inc with map_smul' := S.inc_smul }
  let F : O' ⊗[O] A →ₗ[O'] A' := f.liftBaseChange O'
  have hF : ∀ c x, F (c ⊗ₜ x) = c • S.inc x := fun c x => LinearMap.liftBaseChange_tmul _ _ _ _
  have hl : ∀ t, ∑ a, b a ⊗ₜ[O] S.p a (F t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [hF, S.p_inc, ← TensorProduct.smul_tmul]
      rw [← TensorProduct.sum_tmul, b.sum_repr]
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]
  refine (LinearEquiv.ofBijective F ⟨fun s t h => ?_, fun x => ⟨∑ a, b a ⊗ₜ[O] S.p a x, ?_⟩⟩).length_eq.symm
  · rw [← hl s, ← hl t, h]
  · simp only [map_sum, hF, S.sum_p]

def pi (X : Type) : Comp b (X → A) (X → A') where
  inc := AddMonoidHom.compLeft S.inc X
  p a := AddMonoidHom.compLeft (S.p a) X
  sum_p x := by funext g; simp [S.sum_p]
  p_inc a c x := by funext g; simp [S.p_inc]

def Compat (N : Submodule O A) (N' : Submodule O' A') : Prop := ∀ x, x ∈ N' ↔ ∀ a, S.p a x ∈ N

variable {S}

theorem Compat.inc_mem {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') {x : A}
    (hx : x ∈ N) : S.inc x ∈ N' :=
  (h _).2 fun a => by rw [S.p_inc']; exact N.smul_mem _ hx

def Compat.sub {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') : Comp b N N' where
  inc := { toFun x := ⟨S.inc x, h.inc_mem x.2⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  p a := { toFun x := ⟨S.p a x, (h _).1 x.2 a⟩
           map_zero' := Subtype.ext (map_zero _)
           map_add' x y := Subtype.ext (map_add _ _ _) }
  sum_p x := Subtype.ext (by simpa using S.sum_p x)
  p_inc a c x := Subtype.ext (S.p_inc a c x)

def Compat.quot {N : Submodule O A} {N' : Submodule O' A'} (h : S.Compat N N') :
    Comp b (A ⧸ N) (A' ⧸ N') where
  inc := QuotientAddGroup.map N.toAddSubgroup N'.toAddSubgroup S.inc fun _ hx => h.inc_mem hx
  p a := QuotientAddGroup.map N'.toAddSubgroup N.toAddSubgroup (S.p a) fun x hx => (h x).1 hx a
  sum_p x := by
    obtain ⟨x, rfl⟩ := N'.mkQ_surjective x
    conv_rhs => rw [← S.sum_p x, map_sum]
    rfl
  p_inc a c x := by
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [← map_smul, ← S.p_inc]
    rfl

variable (S)

theorem compat_top : S.Compat ⊤ ⊤ := fun _ => by simp

theorem compat_bot : S.Compat ⊥ ⊥ := fun x => by
  simp only [Submodule.mem_bot]
  exact ⟨fun h a => by rw [h, map_zero], fun h => S.ext_p fun a => by rw [h, map_zero]⟩

theorem compat_span (T : Set A) : S.Compat (Submodule.span O T) (Submodule.span O' (S.inc '' T)) := by
  intro x
  constructor
  · intro hx
    have : ∀ c : O', ∀ a, S.p a (c • x) ∈ Submodule.span O T := by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        intro c a
        rw [S.p_inc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
      | zero => simp
      | add x y _ _ hx hy => intro c a; rw [smul_add, map_add]; exact add_mem (hx c a) (hy c a)
      | smul d x _ hx => intro c a; rw [smul_smul]; exact hx _ a
    simpa using this 1
  · intro hx
    have : ∀ y ∈ Submodule.span O T, S.inc y ∈ Submodule.span O' (S.inc '' T) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul d x _ hx => rw [S.inc_smul]; exact Submodule.smul_mem _ _ hx
    rw [← S.sum_p x]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (this _ (hx a))

section Coh

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  [TopologicalSpace A'] [DiscreteTopology A'] [IsTopologicalAddGroup A'] [ContinuousConstSMul O' A']
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {ρ : Representation O Γ A} {ρ' : Representation O' Γ A'}
  (he : ∀ a g m, S.p a (ρ' g m) = ρ g (S.p a m))
include he

theorem compatible_cocycles : (S.pi Γ).Compat (Z1 ρ) (Z1 ρ') := by
  intro f
  constructor
  · intro hf a
    refine ⟨(continuous_of_discreteTopology (f := S.p a)).comp hf.1, fun g h => ?_⟩
    change S.p a (f (g * h)) = S.p a (f g) + ρ g (S.p a (f h))
    rw [hf.2, map_add, he]
  · intro hf
    refine ⟨?_, fun g h => S.ext_p fun a => ?_⟩
    · have : f = fun g => ∑ a, b a • S.inc (S.p a (f g)) := by funext g; rw [S.sum_p]
      rw [this]
      exact continuous_finset_sum _ fun a _ =>
        ((continuous_of_discreteTopology (f := S.inc)).comp (hf a).1).const_smul (b a)
    · rw [map_add, he]; exact (hf a).2 g h

theorem compatible_coboundaries : (S.compatible_cocycles he).sub.Compat ((B1 ρ).comap (Z1 ρ).subtype)
    ((B1 ρ').comap (Z1 ρ').subtype) := by
  intro f
  simp only [Submodule.mem_comap, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩ a
    refine ⟨S.p a m, fun g => ?_⟩
    change S.p a (f.1 g) = _
    rw [← he, ← map_sub]; exact congrArg _ (hm g)
  · intro hf
    choose m hm using hf
    refine ⟨∑ a', b a' • S.inc (m a'), fun g => S.ext_p fun a => ?_⟩
    rw [map_sub, he, S.p_sum]
    exact hm a g

def h1 : Comp b (H1 ρ) (H1 ρ') := (S.compatible_coboundaries he).quot

theorem p_res {Δ : Type} [Group Δ] [TopologicalSpace Δ] (φ : Δ →* Γ) (hφ : Continuous φ) (a : ι)
    (x : H1 ρ') :
    (S.h1 (ρ := ρ.comp φ) (ρ' := ρ'.comp φ) (fun a g m => he a (φ g) m)).p a (resH1 ρ' φ hφ x) =
      resH1 ρ φ hφ ((S.h1 he).p a x) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

theorem compat_H1ur (J : Subgroup Γ) : (S.h1 he).Compat (H1ur ρ J) (H1ur ρ' J) := by
  intro x
  simp only [H1ur, LinearMap.mem_ker]
  refine ((S.h1 (ρ := ρ.comp J.subtype) (ρ' := ρ'.comp J.subtype)
    (fun a g m => he a _ m)).compat_bot (resH1 ρ' J.subtype continuous_subtype_val x)).trans
    (forall_congr' fun a => ?_)
  rw [← S.p_res he J.subtype continuous_subtype_val a x]
  exact Submodule.mem_bot _

theorem compat_Sel {I : Type} {Δ : I → Type} [∀ i, Group (Δ i)] [∀ i, TopologicalSpace (Δ i)]
    (φ : ∀ i, Δ i →* Γ) (hφ : ∀ i, Continuous (φ i)) (L : LocCond ρ φ) (L' : LocCond ρ' φ)
    (hL : ∀ i, (S.h1 (ρ := ρ.comp (φ i)) (ρ' := ρ'.comp (φ i))
      (fun a g m => he a (φ i g) m)).Compat (L i) (L' i)) :
    (S.h1 he).Compat (Sel ρ φ hφ L) (Sel ρ' φ hφ L') := by
  intro x
  simp only [mem_Sel, ← S.p_res he]
  exact ⟨fun h a i => (hL i _).1 (h i) a, fun h i => (hL i _).2 fun a => h a i⟩

end Coh

end Comp

end Comp

section Frac

variable {O O' : Type} [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O'] [Algebra O O']
  [FaithfulSMul O O'] [Module.Finite O O'] {ι : Type} [Fintype ι] (b : Module.Basis ι O O')

attribute [local instance] FractionRing.liftAlgebra

def fracBasis : Module.Basis ι (FractionRing O) (FractionRing O') :=
  b.localizationLocalization (FractionRing O) (nonZeroDivisors O) (FractionRing O')

def fracComp : Comp b (FractionRing O) (FractionRing O') where
  inc := (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom
  p a := ((fracBasis b).coord a).toAddMonoidHom
  sum_p x := by
    conv_rhs => rw [← (fracBasis b).sum_repr x]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Algebra.smul_def, mul_comm, fracBasis]
  p_inc a c x := by
    have : c • (algebraMap (FractionRing O) (FractionRing O')).toAddMonoidHom x =
        x • algebraMap O' (FractionRing O') c := by simp [Algebra.smul_def, mul_comm]
    rw [this]
    change (fracBasis b).repr (x • _) a = _
    rw [map_smul, Finsupp.smul_apply, fracBasis, Module.Basis.localizationLocalization_repr_algebraMap,
      Algebra.smul_def (b.repr c a), smul_eq_mul, mul_comm]

theorem fracComp_inc (x : FractionRing O) :
    (fracComp b).inc x = algebraMap (FractionRing O) (FractionRing O') x := rfl

theorem frac_compat : (fracComp b).Compat (LinearMap.range (Algebra.linearMap O (FractionRing O)))
    (LinearMap.range (Algebra.linearMap O' (FractionRing O'))) := by
  intro x
  constructor
  · rintro ⟨c, rfl⟩ a
    refine ⟨b.repr c a, ?_⟩
    have := (fracComp b).p_inc a c 1
    simpa [fracComp_inc, ← Algebra.algebraMap_eq_smul_one] using this.symm
  · intro h
    choose m hm using h
    rw [← (fracComp b).sum_p x]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ⟨algebraMap O O' (m a), ?_⟩
    rw [← hm, fracComp_inc]
    simp [← IsScalarTower.algebraMap_apply]

def divComp (r : ℕ) : Comp b (Fin r → KmodO O) (Fin r → KmodO O') := (frac_compat b).quot.pi (Fin r)

theorem divComp_inc {r : ℕ} (y : Fin r → FractionRing O) (j : Fin r) :
    (divComp b r).inc (fun j => Submodule.Quotient.mk (y j)) j =
      Submodule.Quotient.mk (algebraMap (FractionRing O) (FractionRing O') (y j)) := rfl

open Formalism.MainNotions.BlochKatoReduction

theorem divComp_equiv {Γ O₀ : Type} [Group Γ] [CommRing O₀] (φ : O₀ →+* O) {r : ℕ}
    (ρ : Γ →* GL (Fin r) O₀) (χ : Γ →* O₀ˣ) (a : ι) (g : Γ) (m : Fin r → KmodO O') :
    (divComp b r).p a (twRep ((algebraMap O O').comp φ) ρ χ 1 g m) =
      twRep φ ρ χ 1 g ((divComp b r).p a m) := by
  funext j
  change (frac_compat b).quot.p a ((((1 : O'ˣ)⁻¹ * (Units.map ((algebraMap O O').comp φ).toMonoidHom (χ g))⁻¹ : O'ˣ) : O') •
      ∑ k, algebraMap O O' (φ ((ρ g : Matrix (Fin r) (Fin r) O₀) j k)) • m k) =
    (((1 : Oˣ)⁻¹ * (Units.map φ.toMonoidHom (χ g))⁻¹ : Oˣ) : O) •
      ∑ k, (φ ((ρ g : Matrix (Fin r) (Fin r) O₀) j k)) • (frac_compat b).quot.p a (m k)
  have : (((1 : O'ˣ)⁻¹ * (Units.map ((algebraMap O O').comp φ).toMonoidHom (χ g))⁻¹ : O'ˣ) : O') =
      algebraMap O O' (((1 : Oˣ)⁻¹ * (Units.map φ.toMonoidHom (χ g))⁻¹ : Oˣ) : O) := by
    simp [← map_inv]
  rw [this, Comp.p_smul, map_sum]
  simp only [Comp.p_smul]

def fracClasses {Γ O₀ : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O₀] {O : Type} [CommRing O]
    [IsDomain O] (φ : O₀ →+* O) {r : ℕ} (ρ : Representation O Γ (Fin r → KmodO O)) {C : Type}
    (P : C → Prop) (Fr : C → Γ → Fin r → O₀ → O₀ → Prop) : Set (H1 ρ) :=
  {x | ∃ (z : Z1 ρ) (c : C) (y : Γ → Fin r → FractionRing O), P c ∧
    (∀ g a, ∃ n d : O₀, Fr c g a n d ∧
      algebraMap O (FractionRing O) (φ d) * y g a = algebraMap O (FractionRing O) (φ n)) ∧
    (∀ g a, (z : Γ → Fin r → KmodO O) g a = Submodule.Quotient.mk (y g a)) ∧
    x = Submodule.Quotient.mk z}

theorem fracClasses_eq {Γ O₀ : Type} [Group Γ] [TopologicalSpace Γ] [CommRing O₀] (φ : O₀ →+* O)
    (hφ : Function.Injective φ) {r : ℕ} (ρ : Representation O Γ (Fin r → KmodO O))
    (ρ' : Representation O' Γ (Fin r → KmodO O'))
    (he : ∀ a g m, (divComp b r).p a (ρ' g m) = ρ g ((divComp b r).p a m))
    (hu : ∃ a, IsUnit (b.repr 1 a)) {C : Type}
    (P : C → Prop) (Fr : C → Γ → Fin r → O₀ → O₀ → Prop) (hFr : ∀ c g a n d, Fr c g a n d → d ≠ 0) :
    fracClasses ((algebraMap O O').comp φ) ρ' P Fr =
      ((divComp b r).h1 he).inc '' fracClasses φ ρ P Fr := by
  ext x
  constructor
  · rintro ⟨z, c, y, hc, hy, hz, rfl⟩
    choose n d hF hy using hy
    have hd : ∀ g a, algebraMap O (FractionRing O) (φ (d g a)) ≠ 0 := fun g a => by
      simpa [map_eq_zero_iff φ hφ] using hFr _ _ _ _ _ (hF g a)
    let y₀ : Γ → Fin r → FractionRing O := fun g a =>
      algebraMap O (FractionRing O) (φ (n g a)) / algebraMap O (FractionRing O) (φ (d g a))
    have hy₀ : ∀ g a, algebraMap O (FractionRing O) (φ (d g a)) * y₀ g a =
        algebraMap O (FractionRing O) (φ (n g a)) := fun g a => mul_div_cancel₀ _ (hd g a)
    have hyy : ∀ g a, algebraMap (FractionRing O) (FractionRing O') (y₀ g a) = y g a := by
      intro g a
      have h1 := congrArg (algebraMap (FractionRing O) (FractionRing O')) (hy₀ g a)
      have h2 := hy g a
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply] at h2
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) (FractionRing O'),
        IsScalarTower.algebraMap_apply O (FractionRing O) (FractionRing O')] at h2
      rw [map_mul, ← h2] at h1
      exact mul_left_cancel₀ ((map_ne_zero _).2 (hd g a)) h1
    let z₀ : Γ → Fin r → KmodO O := fun g a => Submodule.Quotient.mk (y₀ g a)
    have hzz : ((divComp b r).pi Γ).inc z₀ = z := by
      funext g a
      rw [hz, ← hyy]
      rfl
    have hz₀ : z₀ ∈ Z1 ρ := by
      obtain ⟨a, u, hu⟩ := hu
      have := ((divComp b r).compatible_cocycles he z).1 z.2 a
      rw [← hzz, Comp.p_inc', ← hu] at this
      simpa [smul_smul] using (Z1 ρ).smul_mem (↑u⁻¹ : O) this
    refine ⟨Submodule.Quotient.mk ⟨z₀, hz₀⟩, ⟨⟨z₀, hz₀⟩, c, y₀, hc, fun g a => ⟨_, _, hF g a, hy₀ g a⟩,
      fun _ _ => rfl, rfl⟩, ?_⟩
    exact congrArg Submodule.Quotient.mk (Subtype.ext hzz)
  · rintro ⟨_, ⟨z, c, y, hc, hy, hz, rfl⟩, rfl⟩
    refine ⟨((divComp b r).compatible_cocycles he).sub.inc z, c,
      fun g a => algebraMap (FractionRing O) (FractionRing O') (y g a), hc, fun g a => ?_,
      fun g a => ?_, rfl⟩
    · obtain ⟨n, d, hF, hy⟩ := hy g a
      refine ⟨n, d, hF, ?_⟩
      have h1 := congrArg (algebraMap (FractionRing O) (FractionRing O')) hy
      simpa [← IsScalarTower.algebraMap_apply] using h1
    · change (frac_compat b).quot.inc (z.1 g a) = _
      rw [hz]
      rfl

end Frac

section Len

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] [FaithfulSMul O O'] [Module.Finite O O']
  {ι : Type} [Fintype ι] {b : Module.Basis ι O O'}

theorem exists_unit_repr_one (b : Module.Basis ι O O') : ∃ a, IsUnit (b.repr 1 a) := by
  by_contra h
  push Not at h
  have : (1 : O') ∈ IsLocalRing.maximalIdeal O' := by
    rw [← b.sum_repr 1]
    refine Ideal.sum_mem _ fun a _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ fun hu => h a (isUnit_of_map_unit _ _ hu)
  exact this isUnit_one

theorem lenN_eq {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O' A']
    (S : Comp b A A') (l : ℕ) : Formalism.MainNotions.BlochKatoReduction.Gen.lenN O' l A' = Formalism.MainNotions.BlochKatoReduction.Gen.lenN O l A := by
  have he := GlobalTheory.ramificationIdx_maximalIdeal_pos O O'
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.lenN
  rw [S.length_eq, GlobalTheory.length_baseChange_dvr, ← map_natCast (algebraMap O O'), GlobalTheory.addVal_algebraMap,
    ENat.toNat_mul, ENat.toNat_coe, ENat.toENNReal_mul, Nat.cast_mul, ENat.toENNReal_coe]
  exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast he.ne') (ENNReal.natCast_ne_top _)

end Len

section Main

open Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.GaloisCohomology

theorem compat_selAll {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {ι : Type} [Fintype ι]
    {b : Module.Basis ι O O'} {A A' : Type} [AddCommGroup A] [Module O A] [AddCommGroup A']
    [Module O' A'] (S : Comp b A A') [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [TopologicalSpace A'] [DiscreteTopology A']
    [IsTopologicalAddGroup A'] [ContinuousConstSMul O' A'] {F Ω : Type} [Field F] [NumberField F]
    [Field Ω] [Algebra F Ω] {ρ : Representation O (G F Ω) A} {ρ' : Representation O' (G F Ω) A'}
    (he : ∀ a g m, S.p a (ρ' g m) = ρ g (S.p a m)) (P : Places F Ω) (l : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (L : ∀ v, Submodule O (H1 (ρ.comp (Dec (F := F) (P.1 v)).subtype)))
    (L' : ∀ v, Submodule O' (H1 (ρ'.comp (Dec (F := F) (P.1 v)).subtype)))
    (hL : ∀ v, ((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      (S.h1 (ρ := ρ.comp (Dec (F := F) (P.1 v)).subtype) (ρ' := ρ'.comp (Dec (F := F) (P.1 v)).subtype)
        (fun a g m => he a _ m)).Compat (L v) (L' v)) :
    (S.h1 he).Compat (SelAll ρ P (bkCond ρ P l T L)) (SelAll ρ' P (bkCond ρ' P l T L')) := by
  refine Comp.compat_Sel _ he _ _ _ _ fun v => ?_
  unfold bkCond
  split_ifs with h1 h2
  · exact hL v h1
  · exact Comp.compat_top _
  · exact S.compat_H1ur _ _

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

open Classical in

def bkG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule O (H1 ((twRep φ (X.rhoS i s) (chiS i s) 1).comp (DecV N v).subtype)) :=
  if hv : v ∈ placesOver D.host.E (X.l i) then
    Submodule.span O (fracClasses φ _
      (fun c => c ∈ Formalism.WeaklyAdmissibleFiltrations.finiteCocycles (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      (fun c g a n d => IsFrac bkP i v hv (c ((bkP.br i v hv).e g) a) n d))
  else ⊥

def selG {O : Type} [CommRing O] [IsDomain O] (φ : X.O0 i →+* O)
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    Submodule O (H1 (twRep φ (X.rhoS i s) (chiS i s) 1)) :=
  SelAll _ N.plOm (bkCond _ N.plOm (X.l i) (Spl i ∪ ↑Q) (bkG bkP i s φ))

theorem selT_eq (k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    selT bkP i s k Q 1 = selG bkP i s (phiK X i k) Q := rfl

theorem lenN_selG {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [FaithfulSMul O O'] [Module.Finite O O']
    (φ : X.O0 i →+* O) (hφ : Function.Injective φ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (l : ℕ) :
    lenN O' l (selG bkP i s ((algebraMap O O').comp φ) Q) = lenN O l (selG bkP i s φ Q) := by
  let b := Module.Free.chooseBasis O O'
  have he := divComp_equiv b φ (X.rhoS i s) (chiS i s)
  refine lenN_eq (b := b) (Comp.Compat.sub (S := (divComp b D.R.r).h1 he) ?_) l
  refine compat_selAll _ he _ _ _ _ _ fun v h1 => ?_
  have hv : v ∈ placesOver D.host.E (X.l i) := h1
  unfold bkG
  rw [dif_pos hv, dif_pos hv, fracClasses_eq b φ hφ
    ((twRep φ (X.rhoS i s) (chiS i s) 1).comp (DecV N v).subtype)
    ((twRep ((algebraMap O O').comp φ) (X.rhoS i s) (chiS i s) 1).comp (DecV N v).subtype)
    (fun a g m => he a g.1 m) (exists_unit_repr_one b) _ _ ?_]
  · exact Comp.compat_span _ _
  · exact fun _ _ _ _ _ h => h.1

theorem sLen_eq (k : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    sLen bkP i s k Q 1 = lenN (X.O i) (X.l i) (selG bkP i s (algebraMap (X.O0 i) (X.O i)) Q) := by
  haveI := X.Ok_fin i k
  haveI : FaithfulSMul (X.O i) (X.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i k)
  exact lenN_selG bkP i s (O' := X.Ok i k) (algebraMap (X.O0 i) (X.O i)) (X.O_inj i) Q (X.l i)

end Main

theorem sLen_level_free (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k k' : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) i s k Q 1 =
      Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) i s k' Q 1 := by
  rw [sLen_eq, sLen_eq]

end GlobalTheory.SelmerLevel

end
