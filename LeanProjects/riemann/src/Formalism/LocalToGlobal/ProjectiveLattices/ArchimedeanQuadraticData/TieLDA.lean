import Mathlib

namespace Formalism.L2.Pj.QAt.TieLDA

open TensorProduct Module

def tm (K K₁ : Type*) [Field K] [Field K₁] [Algebra K K₁] {U : Type*} [AddCommGroup U]
    [Module K U] (u : U) : K₁ ⊗[K] U :=
  (1 : K₁) ⊗ₜ[K] u

section Base

variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]

abbrev modT (T : Subring K₁) (U : Type*) [AddCommGroup U] [Module K U] :
    Module T (K₁ ⊗[K] U) :=
  Module.compHom _ T.subtype

attribute [local instance] modT

abbrev modR (R : Type*) [CommRing R] [Algebra R K] (U : Type*) [AddCommGroup U] [Module K U] :
    Module R (K₁ ⊗[K] U) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] modR

variable {U : Type*} [AddCommGroup U] [Module K U]

theorem smulT_def (T : Subring K₁) (t : T) (l : K₁ ⊗[K] U) : t • l = (t : K₁) • l := rfl

instance scalarT (T : Subring K₁) : IsScalarTower T K₁ (K₁ ⊗[K] U) :=
  ⟨fun t k l => by rw [smulT_def, Subring.smul_def, smul_eq_mul, mul_smul]⟩

theorem smulK_eq (k : K) (l : K₁ ⊗[K] U) : k • l = algebraMap K K₁ k • l := by
  induction l using TensorProduct.induction_on with
  | zero => simp
  | tmul a u =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def]
    rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

section R

variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]

theorem smulR_def (r : R) (l : K₁ ⊗[K] U) : r • l = algebraMap R K r • l := rfl

def tmR : U →ₗ[R] K₁ ⊗[K] U where
  toFun u := tm K K₁ u
  map_add' x y := tmul_add _ _ _
  map_smul' r u := by
    change (1 : K₁) ⊗ₜ[K] (r • u) = algebraMap R K r • ((1 : K₁) ⊗ₜ[K] u)
    rw [← algebraMap_smul K r u, tmul_smul]

variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))

include hRT in
theorem tower : IsScalarTower R T (K₁ ⊗[K] U) := by
  constructor
  intro r t l
  show ((r • t : T) : K₁) • l = algebraMap R K r • ((t : K₁) • l)
  rw [smulK_eq, smul_smul, Algebra.smul_def r t, Subring.coe_mul, hRT]

include hRT in
theorem tm_smul (r : R) (u : U) : tm K K₁ (r • u) = algebraMap R T r • tm K K₁ u := by
  have h := (tmR (K₁ := K₁) (K := K) (U := U) (R := R)).map_smul r u
  change tm K K₁ (r • u) = r • tm K K₁ u at h
  rw [h, smulR_def, smulT_def, hRT, smulK_eq]

noncomputable def Phi (X : Submodule R U) : T ⊗[R] X →ₗ[T] K₁ ⊗[K] U :=
  @LinearMap.liftBaseChange R X (K₁ ⊗[K] U) T _ _ _ _ _ _ _ _ (tower (U := U) T hRT)
    ((tmR (K₁ := K₁) (K := K) (U := U)).comp X.subtype)

theorem Phi_tmul (X : Submodule R U) (t : T) (x : X) :
    Phi T hRT X (t ⊗ₜ x) = (t : K₁) • tm K K₁ (x : U) := by
  unfold Phi
  erw [LinearMap.liftBaseChange_tmul]
  rfl

theorem Phi_range (X : Submodule R U) :
    LinearMap.range (Phi T hRT X) = Submodule.span T (tm K K₁ '' (X : Set U)) := by
  unfold Phi
  erw [LinearMap.range_liftBaseChange]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

include hRT in
theorem span_tm_span (G : Set U) :
    Submodule.span T (tm K K₁ '' (Submodule.span R G : Set U)) = Submodule.span T (tm K K₁ '' G) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      show (1 : K₁) ⊗ₜ[K] (0 : U) ∈ _
      rw [tmul_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      show (1 : K₁) ⊗ₜ[K] (y + z) ∈ _
      rw [tmul_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [tm_smul T hRT]
      exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]

include K in
theorem isTorsionFree_sub (X : Submodule R U) : Module.IsTorsionFree R X := by
  constructor
  intro r hr x y hxy
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  apply Subtype.ext
  have h1 : r • (x : U) = r • (y : U) := congrArg Subtype.val hxy
  rw [← algebraMap_smul K r (x : U), ← algebraMap_smul K r (y : U)] at h1
  exact smul_right_injective U hK h1

theorem Phi_injective (X : Submodule R U) (hX : X.FG) : Function.Injective (Phi T hRT X) := by
  classical
  haveI : Module.Finite R X := Module.Finite.iff_fg.2 hX
  haveI : Module.IsTorsionFree R X := isTorsionFree_sub (K := K) X
  haveI : Module.Free R X := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R X
  let v : Module.Free.ChooseBasisIndex R X → K₁ ⊗[K] U := fun i => tm K K₁ ((b i : X) : U)
  have hR : LinearIndependent R (fun i => ((b i : X) : U)) :=
    b.linearIndependent.map' X.subtype (Submodule.ker_subtype X)
  have hK : LinearIndependent K (fun i => ((b i : X) : U)) := (LinearIndependent.iff_fractionRing R K).1 hR
  have hK₁ : LinearIndependent K₁ v := Module.Flat.linearIndependent_one_tmul hK
  have hT : LinearIndependent T v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := (linearIndependent_iff'.1 hK₁) s (fun j => (g j : K₁)) (by exact hg) i hi
    exact Subtype.ext h1
  let b' := b.baseChange T
  have hcomp : (Phi T hRT X) ∘ₗ b'.repr.symm.toLinearMap = Finsupp.linearCombination T v := by
    refine Finsupp.lhom_ext' fun i => LinearMap.ext_ring ?_
    simp [b', v, Basis.baseChange_apply, Phi_tmul]
    first
      | exact (one_smul _ _).symm
      | (rw [smulT_def]; simp)
  have key : ∀ z, Finsupp.linearCombination T v (b'.repr z) = Phi T hRT X z := by
    intro z
    rw [← hcomp]
    simp
  intro z w hzw
  apply b'.repr.injective
  exact hT (by rw [key, key, hzw])

include hRT in
theorem length_quot_eq (X Y : Submodule R U) (hX : X.FG) (hYX : Y ≤ X) :
    Module.length T (↥(Submodule.span T (tm K K₁ '' (X : Set U))) ⧸
        (Submodule.span T (tm K K₁ '' (Y : Set U))).comap
          (Submodule.span T (tm K K₁ '' (X : Set U))).subtype) =
      Module.length T (T ⊗[R] (X ⧸ Y.comap X.subtype)) := by
  classical
  let Y' := Y.comap X.subtype
  let Ψ : T ⊗[R] X →ₗ[T] T ⊗[R] (X ⧸ Y') := Y'.mkQ.baseChange T
  have h1 : (Ψ : T ⊗[R] X → T ⊗[R] (X ⧸ Y')) = Y'.mkQ.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hΨ : Function.Surjective Ψ := by
    rw [h1]
    exact LinearMap.lTensor_surjective T (Submodule.mkQ_surjective Y')
  let ι' : T ⊗[R] Y' →ₗ[T] T ⊗[R] X := Y'.subtype.baseChange T
  have h2 : (ι' : T ⊗[R] Y' → T ⊗[R] X) = Y'.subtype.lTensor T := LinearMap.baseChange_eq_ltensor _
  have hker : LinearMap.ker Ψ = LinearMap.range ι' := by
    ext z
    have hex := lTensor_exact T (LinearMap.exact_subtype_mkQ Y') (Submodule.mkQ_surjective Y') z
    rw [LinearMap.mem_ker, LinearMap.mem_range, h1, hex, Set.mem_range, h2]
  let e1 : T ⊗[R] X ≃ₗ[T] Submodule.span T (tm K K₁ '' (X : Set U)) :=
    (LinearEquiv.ofInjective (Phi T hRT X) (Phi_injective T hRT X hX)).trans
      (LinearEquiv.ofEq _ _ (Phi_range T hRT X))
  have he1 : ∀ z, ((e1 z : Submodule.span T (tm K K₁ '' (X : Set U))) : K₁ ⊗[K] U) = Phi T hRT X z := by
    intro z
    rfl
  have hY : ∀ z, Phi T hRT X z ∈ Submodule.span T (tm K K₁ '' (Y : Set U)) ↔ z ∈ LinearMap.range ι' := by
    intro z
    constructor
    · intro hz
      have hle : Submodule.span T (tm K K₁ '' (Y : Set U)) ≤ (LinearMap.range ι').map (Phi T hRT X) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨ι' ((1 : T) ⊗ₜ ⟨⟨y, hYX hy⟩, hy⟩), ⟨_, rfl⟩, ?_⟩
        show Phi T hRT X ((1 : T) ⊗ₜ ⟨y, hYX hy⟩) = tm K K₁ y
        rw [Phi_tmul]
        simp
      obtain ⟨w, hw, hwz⟩ := hle hz
      rw [← Phi_injective T hRT X hX hwz]
      exact hw
    · rintro ⟨w, rfl⟩
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t y =>
        show Phi T hRT X (t ⊗ₜ (y : X)) ∈ _
        rw [Phi_tmul]
        exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), y.2, rfl⟩)
      | add a c ha hc =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ ha hc
  have hmap : ((Submodule.span T (tm K K₁ '' (Y : Set U))).comap
      (Submodule.span T (tm K K₁ '' (X : Set U))).subtype).map (e1.symm : _ →ₗ[T] _) = LinearMap.range ι' := by
    ext z
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_comap, Submodule.subtype_apply, he1]
    exact hY z
  exact ((Submodule.Quotient.equiv _ _ e1.symm hmap).trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (Ψ.quotKerEquivOfSurjective hΨ))).length_eq

include hRT in
theorem span_inf_eq (X : Submodule R U) (hX : X.FG) (W : Submodule K U) :
    Submodule.span T (Submodule.span K₁ (tm K K₁ '' (W : Set U)) : Set (K₁ ⊗[K] U)) ⊓
        Submodule.span T (tm K K₁ '' (X : Set U)) =
      Submodule.span T (tm K K₁ '' ((X ⊓ W.restrictScalars R : Submodule R U) : Set U)) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzW, hzX⟩ := hz
    let fR : U →ₗ[R] U ⧸ W := W.mkQ.restrictScalars R
    let Xb : Submodule R (U ⧸ W) := X.map fR
    let g : X →ₗ[R] Xb := fR.submoduleMap X
    have hg : Function.Surjective g := LinearMap.submoduleMap_surjective fR X
    have hz0 : W.mkQ.baseChange K₁ z = 0 := by
      refine Submodule.span_induction (p := fun z _ => W.mkQ.baseChange K₁ z = 0) ?_ ?_ ?_ ?_ hzW
      · intro y hy
        refine Submodule.span_induction (p := fun y _ => W.mkQ.baseChange K₁ y = 0) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨w, hw, rfl⟩
          show W.mkQ.baseChange K₁ ((1 : K₁) ⊗ₜ[K] w) = 0
          rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hw,
            TensorProduct.tmul_zero]
        · simp
        · intro a b _ _ ha hb
          rw [map_add, ha, hb, add_zero]
        · intro c a _ ha
          rw [map_smul, ha, smul_zero]
      · simp
      · intro a b _ _ ha hb
        rw [map_add, ha, hb, add_zero]
      · intro t a _ ha
        show W.mkQ.baseChange K₁ ((t : K₁) • a) = 0
        rw [map_smul, ha, smul_zero]
    have hzR : z ∈ LinearMap.range (Phi T hRT X) := by
      rw [Phi_range]
      exact hzX
    obtain ⟨w, rfl⟩ := hzR
    have hsq : ∀ w, Phi T hRT Xb (g.baseChange T w) = W.mkQ.baseChange K₁ (Phi T hRT X w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [LinearMap.baseChange_tmul, Phi_tmul, Phi_tmul]
        show (t : K₁) • tm K K₁ ((g x : Xb) : U ⧸ W) = W.mkQ.baseChange K₁ ((t : K₁) • (1 : K₁) ⊗ₜ[K] (x : U))
        rw [map_smul, LinearMap.baseChange_tmul]
        rfl
      | add a c ha hc =>
        rw [map_add, map_add, map_add, map_add, ha, hc]
    have hw0 : g.baseChange T w = 0 := by
      apply Phi_injective T hRT Xb (hX.map _)
      rw [hsq, map_zero]
      exact hz0
    have hex : Function.Exact (LinearMap.ker g).subtype g :=
      LinearMap.exact_iff.2 (Submodule.range_subtype _).symm
    have hw0' : g.lTensor T w = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor (A := T) g) w]
      exact hw0
    obtain ⟨v, rfl⟩ := (lTensor_exact T hex hg w).1 hw0'
    clear hzW hzX hz0 hw0 hw0'
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Phi_tmul]
      have hyW : ((y : X) : U) ∈ W := by
        have hy : g (y : X) = 0 := y.2
        have h' : W.mkQ ((y : X) : U) = 0 := congrArg Subtype.val hy
        exact (Submodule.Quotient.mk_eq_zero W).1 h'
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), ⟨(y : X).2, hyW⟩, rfl⟩)
    | add a c ha hc =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hc
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxW⟩, rfl⟩
    refine ⟨?_, Submodule.subset_span ⟨x, hxX, rfl⟩⟩
    exact Submodule.subset_span (Submodule.subset_span ⟨x, hxW, rfl⟩)

end R

end Base

section DVR

theorem length_self_eq_top (T : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] :
    Module.length T T = ⊤ := by
  by_contra h
  have hfin := Module.length_ne_top_iff.mp h
  have hart : IsArtinianRing T := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  exact IsDiscreteValuationRing.not_isField T (IsArtinianRing.isField_of_isDomain T)

theorem length_quot_span_pow {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {p : R} (hp : Irreducible p) (e : ℕ) : Module.length R (R ⧸ R ∙ p ^ e) = e := by
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {p} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp
  have h := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R e
  rw [hm, Ideal.span_singleton_pow] at h
  exact h

theorem length_tensor_eq_top {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra R T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] (h : Module.length R N = ⊤) :
    Module.length T (T ⊗[R] N) = ⊤ := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R N
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    have h1 := f.length_eq
    rw [h, Module.length_prod, (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
      Module.length_pi_of_fintype] at h1
    have h0 : Module.length R (Fin 0 →₀ R) = 0 := by
      first
        | exact Module.length_eq_zero_iff.2 inferInstance
        | exact Module.length_eq_zero
    rw [h0, zero_add] at h1
    have h2 : ∑ i, Module.length R (R ⧸ R ∙ p i ^ e i) = ((∑ i, e i : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => length_quot_span_pow (hp i) (e i)
    rw [h2] at h1
    exact ENat.coe_ne_top _ h1.symm
  · let g : N →ₗ[R] R := (Finsupp.lapply ⟨0, hn⟩) ∘ₗ (LinearMap.fst R _ _) ∘ₗ f.toLinearMap
    have hg : Function.Surjective g := by
      intro r
      refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ r, 0), ?_⟩
      simp [g]
    let φ : T ⊗[R] N →ₗ[T] T := (TensorProduct.AlgebraTensorModule.rid R T T).toLinearMap ∘ₗ g.baseChange T
    have hφ : Function.Surjective φ := by
      have hb : Function.Surjective (g.baseChange T) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective T hg
      exact (TensorProduct.AlgebraTensorModule.rid R T T).surjective.comp hb
    have hle := Module.length_le_of_surjective φ hφ
    rw [length_self_eq_top] at hle
    exact top_le_iff.1 hle

end DVR

end Formalism.L2.Pj.QAt.TieLDA
