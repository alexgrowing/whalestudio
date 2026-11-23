import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

def EndSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) : Prop :=
  ∀ φ : W →ₗ[L] W, ∃ X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)),
    ∀ w : W, X.mulVec (w : Fin a → L) = (φ w : Fin a → L)

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ} (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  refine MonoidHom.ext fun x => Units.ext ?_
  ext i k
  simp [mapRep]

theorem exists_finite_field {K : Type} [Field K] (S : Set (AlgebraicClosure K)) (hS : S.Finite) : ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (f : K' →+* AlgebraicClosure K), (∀ x : K, f (algebraMap K K' x) = algebraMap K (AlgebraicClosure K) x) ∧ S ⊆ Set.range f := by
  haveI := hS.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact ⟨IntermediateField.adjoin K S, inferInstance, inferInstance, hfd, (IntermediateField.adjoin K S).val.toRingHom,
    fun x => rfl, fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K S hx⟩, rfl⟩⟩

theorem mem_span_of_map_mem_span {L E ι : Type} [Field L] [Field E] [Fintype ι] (f : L →+* E) (S : Set (ι → L)) (y : ι → L) (h : (f ∘ y) ∈ Submodule.span E ((fun v => f ∘ v) '' S)) : y ∈ Submodule.span L S := by
  classical
  by_contra hy
  have hq : (Submodule.span L S).mkQ y ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual L ((ι → L) ⧸ Submodule.span L S), ψ ((Submodule.span L S).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  set l : (ι → L) →ₗ[L] L := ψ ∘ₗ (Submodule.span L S).mkQ with hl
  have hlS : ∀ s ∈ S, l s = 0 := by
    intro s hs
    simp [hl, (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hs)]
  let c : ι → L := fun i => l (fun j => if i = j then 1 else 0)
  have hlc : ∀ v, l v = ∑ i, v i * c i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ l v]
    simp [c, smul_eq_mul]
  let Λ : (ι → E) →ₗ[E] E := ∑ i, f (c i) • LinearMap.proj i
  have hΛ : ∀ v, Λ (f ∘ v) = f (l v) := by
    intro v
    simp [Λ, hlc, map_sum, mul_comm]
  have hker : Submodule.span E ((fun v => f ∘ v) '' S) ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    simp [hΛ, hlS s hs]
  have h1 := hker h
  rw [LinearMap.mem_ker, hΛ] at h1
  exact hψ ((map_eq_zero f).1 h1)

theorem mulVec_mem_of_mem_span {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) (hW : IsInv τ W) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ w ∈ W, X.mulVec w ∈ W := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g
  | zero => intro w _; simp
  | add x y _ _ hx hy => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hx w hw) (hy w hw)
  | smul c x _ hx => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hx w hw)

theorem isIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : IsIrrSub τ W := by
  classical
  refine ⟨hne, hinv, fun W' hle hinv' => ?_⟩
  by_cases h0 : W' = ⊥
  · exact Or.inl h0
  right
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff W').1 h0
  refine le_antisymm hle fun u hu => ?_
  have hx' : (⟨x, hle hx⟩ : W) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L W, φ ⟨x, hle hx⟩ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx' ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  obtain ⟨X, hX, hXw⟩ := hE (((φ ⟨x, hle hx⟩)⁻¹ • φ).smulRight (⟨u, hu⟩ : W))
  have h1 := hXw ⟨x, hle hx⟩
  simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ, one_smul] at h1
  rw [← h1]
  exact mulVec_mem_of_mem_span τ W' hinv' hX x hx

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem map_mulVec_mem_of_mem_span {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (U : Submodule E (Fin a → E)) (hU : IsInv (mapRep f τ) U) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ u ∈ U, (X.map f).mulVec u ∈ U := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hU g
  | zero => intro u _; rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]; exact U.zero_mem
  | add x y _ _ hx hy => intro u hu; rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]; exact U.add_mem (hx u hu) (hy u hu)
  | smul c x _ hx =>
    intro u hu
    have : (c • x).map f = f c • x.map f := by ext i j; simp
    rw [this, Matrix.smul_mulVec]; exact U.smul_mem _ (hx u hu)

theorem absIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : AbsIrrSub τ W := by
  unfold AbsIrrSub
  set f := algebraMap L (AlgebraicClosure L) with hf
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L))
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
    refine (Submodule.ne_bot_iff _).2 ⟨f ∘ v, Submodule.subset_span ⟨v, hv, rfl⟩, ?_⟩
    intro h
    apply hv0
    funext i
    have := congrFun h i
    simpa using this
  · intro g u hu
    show ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L)).mulVec u ∈ _
    rw [hrep]
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap]
      exact Submodule.subset_span ⟨_, hinv g v hv, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro U hU hinvU
    have key : ∀ φ : W →ₗ[L] W, ∃ M : Matrix (Fin a) (Fin a) L,
        (∀ u ∈ U, (M.map f).mulVec u ∈ U) ∧ ∀ w : W, M.mulVec w = (φ w : Fin a → L) := by
      intro φ
      obtain ⟨X, hX, hXw⟩ := hE φ
      exact ⟨X, map_mulVec_mem_of_mem_span f τ U hinvU hX, hXw⟩
    by_cases h0 : U = ⊥
    · exact Or.inl h0
    right
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).1 h0
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu0 (funext h)
    refine le_antisymm hU (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨M, h1, h2⟩ := key
      (((LinearMap.proj j : (Fin a → L) →ₗ[L] L).comp W.subtype).smulRight (⟨w, hw⟩ : W))
    have h3 : ∀ x ∈ Submodule.span (AlgebraicClosure L) ((fun v => f ∘ v) '' (W : Set (Fin a → L))),
        (M.map f).mulVec x = x j • (f ∘ w) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        rw [hmap]
        have := h2 ⟨v, hv⟩
        simp only at this
        rw [this]
        funext i
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, Pi.add_apply, add_smul]
      | smul c x _ hx => rw [Matrix.mulVec_smul, hx, Pi.smul_apply, smul_eq_mul, mul_smul]
    have h4 := h1 u hu
    rw [h3 u (hU hu)] at h4
    exact (U.smul_mem_iff hj).1 h4

theorem endSpanned_of_isoSub {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W U : Submodule L (Fin a → L)) (hW : IsInv τ W) (hiso : IsoSub τ W U) (hE : EndSpanned τ U) : EndSpanned τ W := by
  obtain ⟨e, he⟩ := hiso
  intro φ
  obtain ⟨X, hX, hXw⟩ := hE ((e : W →ₗ[L] U) ∘ₗ φ ∘ₗ (e.symm : U →ₗ[L] W))
  refine ⟨X, hX, fun w => ?_⟩
  have key : ∀ v : W, ∃ h : X.mulVec (v : Fin a → L) ∈ W, ((e ⟨_, h⟩ : U) : Fin a → L) = X.mulVec (e v : Fin a → L) := by
    clear hXw
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v
      exact ⟨hW g v v.2, he g v _⟩
    | zero =>
      intro v
      refine ⟨by simp, ?_⟩
      simp only [Matrix.zero_mulVec]
      have : (⟨0, W.zero_mem⟩ : W) = 0 := rfl
      rw [this, map_zero]; rfl
    | add x y hx' hy' hx hy =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      obtain ⟨h2, e2⟩ := hy v
      refine ⟨by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2, ?_⟩
      have : (⟨(x + y).mulVec v, by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := by
        ext1; simp [Matrix.add_mulVec]
      rw [this, map_add, Submodule.coe_add, e1, e2, Matrix.add_mulVec]
    | smul c x hx' hx =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      refine ⟨by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1, ?_⟩
      have : (⟨(c • x).mulVec v, by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1⟩ : W) = c • ⟨_, h1⟩ := by
        ext1; simp [Matrix.smul_mulVec]
      rw [this, map_smul, Submodule.coe_smul, e1, Matrix.smul_mulVec]
  obtain ⟨h, hk⟩ := key w
  have h2 := hXw (e w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
  rw [h2] at hk
  have := e.injective (Subtype.ext hk)
  exact congrArg Subtype.val this
end GlobalTheory.SplitField
