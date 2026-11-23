import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

noncomputable section

namespace GlobalTheory.SSListPf

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition
open scoped Matrix

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

def AInv {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (W : Submodule K V) : Prop :=
  ∀ g, ∀ v ∈ W, ρ g v ∈ W

def resEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply]
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

def quoEnd {V : Type} [AddCommGroup V] [Module K V] (ρ : Γ →* Module.End K V) (U : Submodule K V)
    (hU : AInv ρ U) : Γ →* Module.End K (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (hU g)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp
  map_mul' g h := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    simp [Module.End.mul_apply]

def matRep {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) : Γ →* GL (Fin m) K :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b : Module.End K V ≃ₐ[K] Matrix (Fin m) (Fin m) K) :
      Module.End K V →* Matrix (Fin m) (Fin m) K).comp ρ)

theorem matRep_val {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) = LinearMap.toMatrix b b (ρ g) := by
  simp only [matRep, MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, MonoidHom.coe_coe]
  rfl

theorem matRep_mulVec {V : Type} [AddCommGroup V] [Module K V] {m : ℕ} (ρ : Γ →* Module.End K V)
    (b : Module.Basis (Fin m) K V) (g : Γ) (y : V) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K) *ᵥ b.equivFun y = b.equivFun (ρ g y) := by
  rw [matRep_val, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (ρ g) y

theorem charpoly_matRep {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {m : ℕ}
    (ρ : Γ →* Module.End K V) (b : Module.Basis (Fin m) K V) (g : Γ) :
    ((matRep ρ b g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly = (ρ g).charpoly := by
  rw [matRep_val, LinearMap.charpoly_toMatrix]

theorem charpoly_res_quot {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (e : Module.End K V) (W : Submodule K V) (he : ∀ x ∈ W, e x ∈ W) :
    e.charpoly = (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let bW := Module.finBasis K W
  let bQ := Module.finBasis K (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K (V ⧸ W))) K := Matrix.of fun i l ↦
    (b.repr (e (b (Sum.inr l)))) (Sum.inl i)
  let D := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices h : LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, h, Matrix.charpoly_fromBlocks_zero₂₁,
      LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]
  ext u v
  cases u with
  | inl i =>
    cases v with
    | inl k0 =>
      simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A, LinearMap.toMatrix_apply]
      apply Module.Basis.sumQuot_repr_inl_of_mem
    | inr l => simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases v with
    | inl k0 =>
      suffices W.mkQ (e (bW k0)) = 0 by simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he _ (Submodule.coe_mem (bW k0))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

def Split {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Γ →* Module.End K V) : Prop :=
  ∃ L : List (Σ m : ℕ, Γ →* GL (Fin m) K), (∀ p ∈ L, 1 ≤ p.1 ∧ IsIrrSub p.2 ⊤) ∧
    ∀ g, (ρ g).charpoly = (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod

theorem split_zero {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : Module.finrank K V = 0) : Split ρ := by
  refine ⟨[], fun p hp => absurd hp List.not_mem_nil, fun g => ?_⟩
  rw [List.map_nil, List.prod_nil]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree, hV])

theorem split_irr {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (hV : 0 < Module.finrank K V)
    (hirr : ∀ W : Submodule K V, AInv ρ W → W = ⊥ ∨ W = ⊤) : Split ρ := by
  let b := Module.finBasis K V
  refine ⟨[⟨Module.finrank K V, matRep ρ b⟩], fun p hp => ?_, fun g => ?_⟩
  · rw [List.mem_singleton] at hp
    subst hp
    refine ⟨hV, ?_, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
    · intro h0
      have h1 : (fun _ => (1 : K)) ∈ (⊤ : Submodule K (Fin (Module.finrank K V) → K)) := Submodule.mem_top
      rw [h0, Submodule.mem_bot] at h1
      have h2 := congrFun h1 ⟨0, hV⟩
      simp at h2
    · have h1 : AInv ρ (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))) := by
        intro g y hy
        show b.equivFun (ρ g y) ∈ W'
        rw [← matRep_mulVec]
        exact hW' g _ hy
      have h2 : (W'.comap (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K))).map
          (b.equivFun : V →ₗ[K] (Fin (Module.finrank K V) → K)) = W' :=
        Submodule.map_comap_eq_of_surjective b.equivFun.surjective W'
      rcases hirr _ h1 with h3 | h3
      · left
        rw [← h2, h3, Submodule.map_bot]
      · right
        rw [← h2, h3, Submodule.map_top, LinearMap.range_eq_top.mpr b.equivFun.surjective]
  · rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact (charpoly_matRep ρ b g).symm

theorem split_step {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Γ →* Module.End K V) (W : Submodule K V) (hW : AInv ρ W)
    (h1 : Split (resEnd ρ W hW)) (h2 : Split (quoEnd ρ W hW)) : Split ρ := by
  refine ⟨h1.choose ++ h2.choose, fun p hp => ?_, fun g => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    · exact h1.choose_spec.1 p h
    · exact h2.choose_spec.1 p h
  · rw [List.map_append, List.prod_append, ← h1.choose_spec.2 g, ← h2.choose_spec.2 g]
    exact charpoly_res_quot (ρ g) W (hW g)

theorem split_all (d : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    Module.finrank K V = d → ∀ ρ : Γ →* Module.End K V, Split ρ := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hV ρ
  by_cases hex : ∃ W : Submodule K V, AInv ρ W ∧ W ≠ ⊥ ∧ W ≠ ⊤
  · have hW : AInv ρ hex.choose := hex.choose_spec.1
    have hb : hex.choose ≠ ⊥ := hex.choose_spec.2.1
    have ht : hex.choose ≠ ⊤ := hex.choose_spec.2.2
    have hlt : Module.finrank K hex.choose < d := by
      rw [← hV]; exact Submodule.finrank_lt ht
    have hpos : 0 < Module.finrank K hex.choose :=
      Nat.pos_of_ne_zero fun h => hb (Submodule.finrank_eq_zero.mp h)
    have hq : Module.finrank K (V ⧸ hex.choose) + Module.finrank K hex.choose = d := by
      rw [← hV]; exact Submodule.finrank_quotient_add_finrank _
    exact split_step ρ hex.choose hW (ih _ hlt hex.choose rfl (resEnd ρ hex.choose hW))
      (ih _ (by omega) (V ⧸ hex.choose) rfl (quoEnd ρ hex.choose hW))
  · push_neg at hex
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact split_zero ρ (hV.trans h0)
    · refine split_irr ρ (hV ▸ h0) fun W hW => ?_
      by_cases hb : W = ⊥
      · exact Or.inl hb
      · exact Or.inr (hex W hW hb)

end SSListPf

open Formalism.MainNotions.N Polynomial GlobalTheory.StringRepresentationDecomposition

theorem ssList_holds : SSList := by
  intro k _ Γ _ n ρ
  let ρE : Γ →* Module.End k (Fin n → k) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)) :
      Matrix (Fin n) (Fin n) k →* Module.End k (Fin n → k)).comp ((Units.coeHom _).comp ρ)
  have hρg : ∀ g, ρE g = Matrix.toLin' ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) k) := fun g => rfl
  have h := SSListPf.split_all n (Fin n → k) (by simp) ρE
  refine ⟨h.choose, h.choose_spec.1, fun g => ?_⟩
  rw [← h.choose_spec.2 g, hρg, Matrix.charpoly_toLin']

end GlobalTheory
