import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers

open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IsotOrth

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intF (F : Type) [Field F] [NumberField F] : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem _
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem _
  neg_mem' := fun {a} ha v => neg_mem (ha v)

theorem finite_intF_quot (M : ℕ) (hM : 0 < M) :
    Finite (intF F ⧸ Ideal.span {(M : intF F)}) := by
  obtain ⟨ho, hc⟩ := PI.IntAdCpctOpenWork.main F
  haveI : CompactSpace (intF F) := isCompact_iff_compactSpace.mp hc
  have hM0 : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (M : F)⁻¹
  have hcM : c * (M : FiniteAdeleRing (𝓞 F) F) = 1 := by
    have : (M : FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (M : F) := by simp
    rw [this, ← map_mul, inv_mul_cancel₀ hM0, map_one]
  have hopen : IsOpen (((Ideal.span {(M : intF F)}).toAddSubgroup : AddSubgroup (intF F)) : Set (intF F)) := by
    have h1 : IsOpen {x : intF F | c * (x : FiniteAdeleRing (𝓞 F) F) ∈ (intF F : Set _)} :=
      ho.preimage (continuous_const.mul continuous_subtype_val)
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, rfl⟩
      have : c * (((a * (M : intF F) : intF F)) : FiniteAdeleRing (𝓞 F) F) = a := by
        push_cast
        rw [mul_comm (a : FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcM, one_mul]
      rw [this]; exact a.2
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      push_cast
      rw [mul_comm, ← mul_assoc, mul_comm (M : FiniteAdeleRing (𝓞 F) F), hcM, one_mul]
  have := AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact this

def intT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  Subring.closure ({x | ∃ y : 𝓞 E, x = (y : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)} ∪
    {x | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ x = (1 : E) ⊗ₜ[F] a})

def jT : intF F →+* intT F E where
  toFun a := ⟨(1 : E) ⊗ₜ[F] (a : FiniteAdeleRing (𝓞 F) F), Subring.subset_closure (Or.inr ⟨a, a.2, rfl⟩)⟩
  map_one' := rfl
  map_mul' a b := Subtype.ext (by simp [Algebra.TensorProduct.tmul_mul_tmul])
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [TensorProduct.tmul_add])

def gT : 𝓞 E →+* intT F E where
  toFun y := ⟨(y : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F), Subring.subset_closure (Or.inl ⟨y, rfl⟩)⟩
  map_one' := rfl
  map_mul' a b := Subtype.ext (by simp [Algebra.TensorProduct.tmul_mul_tmul])
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [TensorProduct.add_tmul])

theorem exists_finite_class (M : ℕ) (hM : 0 < M) :
    ∃ (Q : Type) (_ : Finite Q) (c : intT F E → Q), ∀ a b, c a = c b →
      ∃ y : intT F E, a - b = (M : intT F E) * y := by
  letI : Algebra (intF F) (intT F E) := (jT (F := F) (E := E)).toAlgebra
  have hsmul : ∀ (a : intF F) (x : intT F E), a • x = jT a * x := fun a x => Algebra.smul_def a x
  obtain ⟨t, ht⟩ : (⊤ : Submodule ℤ (𝓞 E)).FG := Module.Finite.fg_top
  let s : Set (intT F E) := gT '' (t : Set (𝓞 E))
  have hs : s.Finite := t.finite_toSet.image _
  have hint : ∀ x ∈ s, IsIntegral (intF F) x := by
    rintro _ ⟨y, -, rfl⟩
    have h1 : IsIntegral ℤ (gT (F := F) y) :=
      IsIntegral.map (gT (F := F) (E := E)).toIntAlgHom (Algebra.IsIntegral.isIntegral y)
    exact h1.tower_top
  have hfg := fg_adjoin_of_finite hs hint
  have hg : ∀ y : 𝓞 E, gT (F := F) y ∈ Algebra.adjoin (intF F) s := by
    intro y
    have hy : y ∈ Submodule.span ℤ (t : Set (𝓞 E)) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [zsmul_eq_mul, map_mul, map_intCast]; exact mul_mem (intCast_mem _ a) hx
  have htop : ∀ x (hx : x ∈ intT F E), (⟨x, hx⟩ : intT F E) ∈ Algebra.adjoin (intF F) s := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
      · exact hg y
      · exact Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : intF F)
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hfin : Module.Finite (intF F) (intT F E) := by
    refine ⟨?_⟩
    have : (Algebra.adjoin (intF F) s).toSubmodule = ⊤ :=
      eq_top_iff.2 fun x _ => htop x.1 x.2
    rwa [this] at hfg
  set I : Ideal (intF F) := Ideal.span {(M : intF F)} with hI
  haveI : Finite (intF F ⧸ I) := finite_intF_quot M hM
  haveI : Finite (intT F E ⧸ I • (⊤ : Submodule (intF F) (intT F E))) := Module.finite_of_finite (intF F ⧸ I)
  refine ⟨_, this, Submodule.Quotient.mk, fun a b hab => ?_⟩
  have h := (Submodule.Quotient.eq _).1 hab
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨y, -, hy⟩ := h
  refine ⟨y, ?_⟩
  rw [← hy, hsmul]
  simp

end Fin

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open ReciprocityTheory.Aut

theorem cong_inv_mul {N : ℕ} {a b : GAf L n} (ha : a ∈ Umax L n) (hb : b ∈ Umax L n)
    (h : ∀ i j, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (a.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      (N : AL L) * y) : Cong L n N (a⁻¹ * b) := by
  refine ⟨mul_mem (inv_mem ha) hb, fun i j => ?_⟩
  choose y hy e using h
  have hai : a⁻¹ ∈ Umax L n := inv_mem ha
  refine ⟨∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j,
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hai i k) (hy k j), ?_⟩
  have h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    have : (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
    simpa using this
  have h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
        ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L))) := by
    rw [mul_sub, h0]
    rfl
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.sub_apply, Matrix.mul_apply] at h2
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, e k j]
  ring

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : Cong L n N a) : Cong L n N a⁻¹ := by
  have := cong_inv_mul (N := N) (b := 1) ha.1 (one_mem _) (fun i j => by
    obtain ⟨y, hy, e⟩ := ha.2 i j
    refine ⟨-y, neg_mem hy, ?_⟩
    have e' : (((1 : GAf L n)).1 : Matrix (Fin n) (Fin n) (AL L)) i j = (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by simp
    rw [e', mul_neg, ← e]; ring)
  simpa using this

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : Cong L n N a) (hb : Cong L n N b) : Cong L n N (a * b) := by
  have hi := cong_inv ha
  have := cong_inv_mul (N := N) hi.1 hb.1 (fun i j => by
    obtain ⟨y, hy, e⟩ := hb.2 i j
    obtain ⟨y', hy', e'⟩ := hi.2 i j
    refine ⟨y - y', sub_mem hy hy', ?_⟩
    rw [mul_sub, ← e, ← e']; ring)
  simpa using this

def congSub (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := ⟨one_mem _, fun i j => ⟨0, zero_mem _, by simp⟩⟩
  inv_mem' := cong_inv

theorem orbit_finite {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf L n →* Module.End ℂ A) {N : ℕ} (hN : 0 < N)
    (y : A) (hy : ∀ κ, Cong L n N κ → ρ κ y = y) :
    ((fun k : GAf L n => ρ k y) '' (Umax L n : Set (GAf L n))).Finite := by
  obtain ⟨Q, hQ, c, hc⟩ := exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L) N hN
  let cls : Umax L n → Fin n → Fin n → Q := fun κ i j => c ⟨(κ.1.1 : Matrix (Fin n) (Fin n) (AL L)) i j, κ.2 i j⟩
  have key : ∀ a b : Umax L n, cls a = cls b → ρ a.1 y = ρ b.1 y := by
    intro a b hab
    have hcong : Cong L n N (a.1⁻¹ * b.1) := cong_inv_mul a.2 b.2 (fun i j => by
      obtain ⟨z, hz⟩ := hc _ _ (congrFun (congrFun hab i) j).symm
      refine ⟨z.1, z.2, ?_⟩
      simpa using congrArg Subtype.val hz)
    have h1 := hy _ hcong
    rw [map_mul, Module.End.mul_apply] at h1
    have h2 := congrArg (ρ a.1) h1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h2
    exact h2.symm
  have hfin : (Set.range fun κ : Umax L n => ρ κ.1 y).Finite := by
    rw [← Set.finite_coe_iff]
    refine Finite.of_injective (fun z : Set.range (fun κ : Umax L n => ρ κ.1 y) => cls z.2.choose) ?_
    intro z w h
    have h3 := key _ _ h
    exact Subtype.ext (by rw [← z.2.choose_spec, ← w.2.choose_spec]; exact h3)
  refine hfin.subset ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

end Grp

section Abs

variable {G : Type} [Group G] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_proj (ρ : G →* Module.End ℂ V) (hunit : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (K : Subgroup G) (U Wf : Submodule ℂ V) [FiniteDimensional ℂ Wf]
    (hU : ∀ g, ∀ x ∈ U, ρ g x ∈ U) (hWU : Wf ≤ U) (hWfix : ∀ w ∈ Wf, ∀ k ∈ K, ρ k w = w)
    (hmemW : ∀ w ∈ U, (∀ k ∈ K, ρ k w = w) → w ∈ Wf)
    (horb : ∀ y ∈ U, ((fun k : G => ρ k y) '' (K : Set G)).Finite) (x : V) (hx : ∀ k ∈ K, ρ k x = x) :
    ∃ u ∈ U, ∀ y ∈ U, inner ℂ (x - u) y = 0 := by
  haveI : CompleteSpace Wf := FiniteDimensional.complete ℂ Wf
  have hu : Wf.starProjection x ∈ Wf := Wf.starProjection_apply_mem x
  refine ⟨Wf.starProjection x, hWU hu, ?_⟩
  set z := x - Wf.starProjection x with hz
  have hzW : z ∈ Wfᗮ := Wf.sub_starProjection_mem_orthogonal x
  have hzfix : ∀ k ∈ K, ρ k z = z := by
    intro k hk
    rw [hz, map_sub, hx k hk, hWfix _ hu k hk]
  intro y hy
  set O : Set V := (fun k : G => ρ k y) '' (K : Set G) with hOdef
  have hO : O.Finite := horb y hy
  set Y : Submodule ℂ V := Submodule.span ℂ O with hY
  haveI : FiniteDimensional ℂ Y := FiniteDimensional.span_of_finite ℂ hO
  haveI : CompleteSpace Y := FiniteDimensional.complete ℂ Y
  have hYU : Y ≤ U := Submodule.span_le.2 (by rintro _ ⟨k, _, rfl⟩; exact hU k y hy)
  have hYst : ∀ k ∈ K, ∀ v ∈ Y, ρ k v ∈ Y := by
    intro k hk v hv
    have : Y ≤ Y.comap (ρ k) := Submodule.span_le.2 (by
      rintro _ ⟨k', hk', rfl⟩
      refine Submodule.subset_span ⟨k * k', K.mul_mem hk hk', ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    exact this hv
  have hyY : y ∈ Y := Submodule.subset_span ⟨1, K.one_mem, by simp⟩
  set w := Y.starProjection z with hw
  have hwY : w ∈ Y := Y.starProjection_apply_mem z
  have hwfix : ∀ k ∈ K, ρ k w = w := by
    intro k hk
    symm
    refine Y.eq_starProjection_of_mem_of_inner_eq_zero (hYst k hk w hwY) fun v hv => ?_
    have e1 : z - ρ k w = ρ k (z - w) := by rw [map_sub, hzfix k hk]
    have e2 : v = ρ k (ρ k⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [e1, e2, hunit]
    exact Y.starProjection_inner_eq_zero z _ (hYst _ (K.inv_mem hk) v hv)
  have hwW : w ∈ Wf := hmemW w (hYU hwY) hwfix
  have h1 : inner ℂ w z = 0 := (Submodule.mem_orthogonal _ _).1 hzW w hwW
  have h2 : inner ℂ (z - w) w = 0 := Y.starProjection_inner_eq_zero z w hwY
  have h3 : inner ℂ z w = 0 := inner_eq_zero_symm.1 h1
  have hw0 : w = 0 := by
    rw [inner_sub_left, h3, zero_sub, neg_eq_zero, inner_self_eq_zero] at h2
    exact h2
  have h4 : inner ℂ (z - w) y = 0 := Y.starProjection_inner_eq_zero z y hyY
  rw [hw0, sub_zero] at h4
  exact h4

theorem orth_or_equiv (ρ : G →* Module.End ℂ V) (hunit : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    {X X' : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    (σ : G → Module.End ℂ X) (σ' : G → Module.End ℂ X')
    (hirr : ∀ W : Submodule ℂ X, (∀ g, ∀ f ∈ W, σ g f ∈ W) → W = ⊥ ∨ W = ⊤)
    (hirr' : ∀ W : Submodule ℂ X', (∀ g, ∀ f ∈ W, σ' g f ∈ W) → W = ⊥ ∨ W = ⊤)
    (Φ : X →ₗ[ℂ] V) (Φ' : X' →ₗ[ℂ] V) (hΦ : ∀ g f, Φ (σ g f) = ρ g (Φ f)) (hΦ' : ∀ g f, Φ' (σ' g f) = ρ g (Φ' f))
    (hproj : ∀ f, ∃ a, ∀ f', inner ℂ (Φ f - Φ' a) (Φ' f') = 0) :
    (∀ f f', inner ℂ (Φ f) (Φ' f') = 0) ∨ ∃ T : X ≃ₗ[ℂ] X', ∀ g f, T (σ g f) = σ' g (T f) := by
  have adj : ∀ g z y, inner ℂ (ρ g z) y = inner ℂ z (ρ g⁻¹ y) := by
    intro g z y
    have e2 : y = ρ g (ρ g⁻¹ y) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    conv_lhs => rw [e2]
    rw [hunit]
  let W : Submodule ℂ X :=
    { carrier := {f | ∀ f', inner ℂ (Φ f) (Φ' f') = 0}
      zero_mem' := fun f' => by simp
      add_mem' := fun {a b} ha hb f' => by rw [map_add, inner_add_left, ha, hb, add_zero]
      smul_mem' := fun c a ha f' => by rw [map_smul, inner_smul_left, ha, mul_zero] }
  have hWinv : ∀ g, ∀ f ∈ W, σ g f ∈ W := by
    intro g f hf f'
    rw [hΦ, adj, ← hΦ']
    exact hf _
  rcases hirr W hWinv with hW | hW
  swap
  · left
    intro f f'
    have : f ∈ W := hW ▸ Submodule.mem_top
    exact this f'
  have hkinv : ∀ g, ∀ f ∈ LinearMap.ker Φ', σ' g f ∈ LinearMap.ker Φ' := by
    intro g f hf
    rw [LinearMap.mem_ker] at hf ⊢
    rw [hΦ', hf, map_zero]
  rcases hirr' _ hkinv with hk | hk
  swap
  · left
    intro f f'
    have : f' ∈ LinearMap.ker Φ' := hk ▸ Submodule.mem_top
    rw [LinearMap.mem_ker.1 this, inner_zero_right]
  choose t ht using hproj
  have uniq : ∀ f a b, (∀ f', inner ℂ (Φ f - Φ' a) (Φ' f') = 0) → (∀ f', inner ℂ (Φ f - Φ' b) (Φ' f') = 0) → a = b := by
    intro f a b ha hb
    have h0 : inner ℂ (Φ' (a - b)) (Φ' (a - b)) = 0 := by
      have : Φ' (a - b) = (Φ f - Φ' b) - (Φ f - Φ' a) := by rw [map_sub]; abel
      have e : ∀ z, inner ℂ (Φ' (a - b)) (Φ' z) = 0 := fun z => by
        rw [this, inner_sub_left, ha, hb, sub_zero]
      exact e (a - b)
    have h1 : a - b ∈ LinearMap.ker Φ' := inner_self_eq_zero.1 h0
    rw [hk, Submodule.mem_bot] at h1
    exact sub_eq_zero.1 h1
  let T : X →ₗ[ℂ] X' :=
    { toFun := t
      map_add' := fun f g => uniq (f + g) _ _ (ht _) (fun f' => by
        have : Φ (f + g) - Φ' (t f + t g) = (Φ f - Φ' (t f)) + (Φ g - Φ' (t g)) := by
          rw [map_add, map_add]; abel
        rw [this, inner_add_left, ht, ht, add_zero])
      map_smul' := fun c f => uniq (c • f) _ _ (ht _) (fun f' => by
        have : Φ (c • f) - Φ' ((RingHom.id ℂ c) • t f) = c • (Φ f - Φ' (t f)) := by
          rw [map_smul, map_smul, RingHom.id_apply, smul_sub]
        rw [this, inner_smul_left, ht, mul_zero]) }
  have hTW : ∀ f, T f = 0 → f ∈ W := by
    intro f h f'
    have h1 := ht f f'
    have h2 : t f = 0 := h
    rw [h2, map_zero, sub_zero] at h1
    exact h1
  have hTeq : ∀ g f, T (σ g f) = σ' g (T f) := by
    intro g f
    refine uniq (σ g f) _ _ (ht _) (fun f' => ?_)
    have h2 : Φ (σ g f) - Φ' (σ' g (T f)) = ρ g (Φ f - Φ' (t f)) := by
      rw [hΦ, hΦ', map_sub]; rfl
    rw [h2, adj, ← hΦ']
    exact ht _ _
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    rw [← hW]
    exact hTW f hf
  have hrinv : ∀ g, ∀ f ∈ LinearMap.range T, σ' g f ∈ LinearMap.range T := by
    rintro g _ ⟨f, rfl⟩
    exact ⟨σ g f, hTeq g f⟩
  rcases hirr' _ hrinv with hr | hr
  · left
    intro f f'
    have : T f ∈ LinearMap.range T := ⟨f, rfl⟩
    rw [hr, Submodule.mem_bot] at this
    exact hTW f this f'
  · right
    exact ⟨LinearEquiv.ofBijective T ⟨hinj, LinearMap.range_eq_top.1 hr⟩, hTeq⟩

end Abs

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def coreOf {A : Type} [AddCommGroup A] [Module ℂ A] (C : Submodule ℂ A) (B : A → A → ℂ)
    (h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z)
    (h2 : ∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x))
    (h3 : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) : InnerProductSpace.Core ℂ C :=
  have hz : ∀ x ∈ C, B x 0 = 0 := fun x hx => by
    have := h1 x hx 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this
  have hadd : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, B x (y + z) = B x y + B x z := fun x hx y hy z hz' => by
    simpa using h1 x hx y hy z hz' 1
  have hsm : ∀ x ∈ C, ∀ y ∈ C, ∀ c : ℂ, B x (c • y) = c * B x y := fun x hx y hy c => by
    have := h1 x hx 0 C.zero_mem y hy c
    simpa [hz x hx] using this
  { inner := fun x y => B x y
    conj_inner_symm := fun x y => (h2 x x.2 y y.2).symm
    re_inner_nonneg := fun x => by
      by_cases hx : (x : A) = 0
      · have : B (x : A) x = 0 := by rw [hx]; exact hz 0 C.zero_mem
        simp [this]
      · exact (h3 x x.2 hx).le
    add_left := fun x y z => by
      show B ((x + y : C) : A) z = B x z + B y z
      rw [h2 _ (x + y).2 _ z.2]
      show starRingEnd ℂ (B z ((x : A) + y)) = _
      rw [hadd z z.2 x x.2 y y.2, map_add, ← h2 _ x.2 _ z.2, ← h2 _ y.2 _ z.2]
    smul_left := fun x y r => by
      show B ((r • x : C) : A) y = starRingEnd ℂ r * B x y
      rw [h2 _ (r • x).2 _ y.2]
      show starRingEnd ℂ (B y (r • (x : A))) = _
      rw [hsm y y.2 x x.2, map_mul, ← h2 _ x.2 _ y.2]
    definite := fun x h => by
      by_contra hx
      have h4 := h3 x x.2 (fun h0 => hx (Subtype.ext h0))
      have h5 : B (x : A) x = 0 := h
      simp [h5] at h4 }

def rhoC {G : Type} [Group G] {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : G →* Module.End ℂ A) (C : Submodule ℂ A)
    (hC : ∀ h, ∀ x ∈ C, ρ h x ∈ C) : G →* Module.End ℂ C where
  toFun g := (ρ g).restrict (hC g)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

def sg (π : FinTyp L n) (g : GAf L n) : Module.End ℂ π.S := (rt L n g).restrict (π.stable g)

theorem sg_irr (π : FinTyp L n) (W : Submodule ℂ π.S) (hW : ∀ g, ∀ f ∈ W, sg π g f ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hinv : ∀ h, ∀ f ∈ W.map π.S.subtype, rt L n h f ∈ W.map π.S.subtype := by
    rintro h _ ⟨f, hf, rfl⟩
    exact ⟨_, hW h f hf, rfl⟩
  rcases π.irr _ (Submodule.map_subtype_le _ _) hinv with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (x : GAf L n → ℂ) ∈ W.map π.S.subtype := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : GAf L n → ℂ) ∈ W.map π.S.subtype := by rw [h]; exact x.2
    obtain ⟨w, hw, e⟩ := this
    have : w = x := Subtype.ext e
    exact this ▸ hw

theorem orth_pair {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf L n →* Module.End ℂ A) (C : Submodule ℂ A)
    (B : A → A → ℂ)
    (h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z)
    (h2 : ∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x))
    (h3 : ∀ x ∈ C, x ≠ 0 → 0 < (B x x).re)
    (h4 : ∀ h, ∀ x ∈ C, ρ h x ∈ C)
    (h5 : ∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y)
    (h6 : ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Cong L n N κ → ρ κ x = x}))
    (π π' : FinTyp L n) (hni : ¬ π.Iso π')
    (Φ : π.S →ₗ[ℂ] A) (hΦ : IsEqvA ρ π Φ) (hΦC : LinearMap.range Φ ≤ C)
    (Φ' : π'.S →ₗ[ℂ] A) (hΦ' : IsEqvA ρ π' Φ') (hΦC' : LinearMap.range Φ' ≤ C) (f : π.S) (f' : π'.S) :
    B (Φ f) (Φ' f') = 0 := by
  let core := coreOf C B h1 h2 h3
  letI : NormedAddCommGroup C := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore core.toCore
  let ρC := rhoC ρ C h4
  have hunit : ∀ g (x y : C), inner ℂ (ρC g x) (ρC g y) = inner ℂ x y := fun g x y => h5 g x x.2 y y.2
  let Ψ : π.S →ₗ[ℂ] C := Φ.codRestrict C (fun f => hΦC ⟨f, rfl⟩)
  let Ψ' : π'.S →ₗ[ℂ] C := Φ'.codRestrict C (fun f => hΦC' ⟨f, rfl⟩)
  have hΨ : ∀ g f, Ψ (sg π g f) = ρC g (Ψ f) := fun g f => Subtype.ext (hΦ g f)
  have hΨ' : ∀ g f, Ψ' (sg π' g f) = ρC g (Ψ' f) := fun g f => Subtype.ext (hΦ' g f)
  have hproj : ∀ f, ∃ a, ∀ f', inner ℂ (Ψ f - Ψ' a) (Ψ' f') = 0 := by
    intro f
    obtain ⟨N, hN, hf⟩ := π.smooth f f.2
    set U := LinearMap.range Ψ' with hU
    set Wf : Submodule ℂ C := U ⊓ fixN ρC N with hWf
    haveI := h6 N hN
    let ι : Wf →ₗ[ℂ] ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Cong L n N κ → ρ κ x = x}) :=
      (C.subtype.comp Wf.subtype).codRestrict _ (fun w => Submodule.subset_span ⟨w.1.2, fun κ hκ => by
        have := congrArg Subtype.val (w.2.2 κ hκ)
        exact this⟩)
    have hι : Function.Injective ι := fun a b h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    haveI : FiniteDimensional ℂ Wf := FiniteDimensional.of_injective ι hι
    obtain ⟨u, ⟨a, rfl⟩, hu⟩ := exists_proj ρC hunit (congSub L n N) U Wf
      (by rintro g _ ⟨a, rfl⟩; exact ⟨sg π' g a, hΨ' g a⟩)
      inf_le_left (fun w hw k hk => hw.2 k hk) (fun w hw hfix => ⟨hw, fun κ hκ => hfix κ hκ⟩)
      (by
        rintro _ ⟨a, rfl⟩
        obtain ⟨N', hN', ha⟩ := π'.smooth a a.2
        refine (orbit_finite ρC hN' (Ψ' a) (fun κ hκ => ?_)).subset ?_
        · rw [← hΨ']
          congr 1
          exact Subtype.ext (ha κ hκ)
        · rintro _ ⟨k, hk, rfl⟩
          exact ⟨k, hk.1, rfl⟩)
      (Ψ f) (fun k hk => by
        rw [← hΨ]
        congr 1
        exact Subtype.ext (hf k hk))
    exact ⟨a, fun f' => hu _ ⟨f', rfl⟩⟩
  rcases orth_or_equiv ρC hunit (sg π) (sg π') (sg_irr π) (sg_irr π') Ψ Ψ' hΨ hΨ' hproj with h | ⟨T, hT⟩
  · exact h f f'
  · refine absurd ⟨T, fun h a b e => ?_⟩ hni
    have : b = sg π h a := Subtype.ext e
    rw [this, hT]
    rfl

def leftZ {A : Type} [AddCommGroup A] [Module ℂ A] (C : Submodule ℂ A) (B : A → A → ℂ)
    (h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z)
    (x : A) (hx : x ∈ C) : Submodule ℂ A where
  carrier := {y | y ∈ C ∧ B x y = 0}
  zero_mem' := ⟨C.zero_mem, by
    have := h1 x hx 0 C.zero_mem 0 C.zero_mem 1
    simp only [smul_zero, add_zero, one_mul] at this
    simpa using this⟩
  add_mem' := fun {a b} ha hb => ⟨C.add_mem ha.1 hb.1, by
    have := h1 x hx a ha.1 b hb.1 1
    rw [one_smul] at this
    rw [this, ha.2, hb.2]; simp⟩
  smul_mem' := fun c a ha => ⟨C.smul_mem c ha.1, by
    have h0 : B x 0 = 0 := by
      have := h1 x hx 0 C.zero_mem 0 C.zero_mem 1
      simp only [smul_zero, add_zero, one_mul] at this
      simpa using this
    have := h1 x hx 0 C.zero_mem a ha.1 c
    rw [zero_add] at this
    rw [this, h0, ha.2]; simp⟩

end Main

theorem isotIn_orthogonal : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Cong D.host.E n N κ → ρ κ x = x})) → ∀ π π' : FinTyp D.host.E n, ¬ π.Iso π' → ∀ x ∈ isotIn (D := D) ρ C π, ∀ y ∈ isotIn (D := D) ρ C π', B x y = 0 := by
  intro D n A _ _ ρ C B h1 h2 h3 h4 h5 h6 π π' hni x hx y hy
  have hC : ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≤ C := fun π => iSup₂_le fun Φ h => h.2

  have step1 : ∀ (Φ' : π'.S →ₗ[ℂ] A), IsEqvA ρ π' Φ' ∧ LinearMap.range Φ' ≤ C → ∀ f', B (Φ' f') x = 0 := by
    intro Φ' hΦ' f'
    have hyC : Φ' f' ∈ C := hΦ'.2 ⟨f', rfl⟩
    have hle : isotIn (D := D) ρ C π ≤ leftZ C B h1 (Φ' f') hyC := by
      refine iSup₂_le fun Φ hΦ => ?_
      rintro _ ⟨f, rfl⟩
      have hxC : Φ f ∈ C := hΦ.2 ⟨f, rfl⟩
      refine ⟨hxC, ?_⟩
      rw [h2 _ hyC _ hxC, orth_pair ρ C B h1 h2 h3 h4 h5 h6 π π' hni Φ hΦ.1 hΦ.2 Φ' hΦ'.1 hΦ'.2 f f', map_zero]
    exact (hle hx).2
  have hle : isotIn (D := D) ρ C π' ≤ leftZ C B h1 x (hC π hx) := by
    refine iSup₂_le fun Φ' hΦ' => ?_
    rintro _ ⟨f', rfl⟩
    have hyC : Φ' f' ∈ C := hΦ'.2 ⟨f', rfl⟩
    exact ⟨hyC, by rw [h2 _ (hC π hx) _ hyC, step1 Φ' hΦ' f', map_zero]⟩
  exact (hle hy).2

end GlobalTheory.IsotOrth
