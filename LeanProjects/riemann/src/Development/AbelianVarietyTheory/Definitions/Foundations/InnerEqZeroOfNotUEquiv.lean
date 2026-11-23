import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP

noncomputable section

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.AutMult

section Hom

variable {G G' H H' K K' : Type} [Group G] [Group G'] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

structure IsIrrUnitary [TopologicalSpace G] (π : G →* (H →L[ℂ] H)) : Prop where

  complete : CompleteSpace H

  unitary : IsUnitaryRep π

  irred : IsTopIrreducible π

def homIn (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Submodule ℂ (H →L[ℂ] K) where
  carrier := {T | (∀ x, T x ∈ U) ∧ ∀ g x, T (π g x) = ρ g (T x)}
  add_mem' := fun h h' => ⟨fun x => U.add_mem (h.1 x) (h'.1 x), fun g x => by simp [h.2 g x, h'.2 g x]⟩
  zero_mem' := ⟨fun _ => U.zero_mem, fun g x => by simp⟩
  smul_mem' := fun c _ h => ⟨fun x => U.smul_mem c (h.1 x), fun g x => by simp [h.2 g x]⟩

def multIn (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Cardinal := Module.rank ℂ (homIn π ρ U)

def UEquiv (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) : Prop := ∃ e : H ≃ₗᵢ[ℂ] K, ∀ g x, e (π g x) = ρ g (e x)

def IsCopy (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) (W : Submodule ℂ K) : Prop :=
  ∃ hW : IsSubrep ρ W, UEquiv π hW.rep

def isoPart (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Submodule ℂ K :=
  (⨆ T ∈ homIn π ρ U, LinearMap.range (T : H →ₗ[ℂ] K)).topologicalClosure

def IsIsotypic (π : G →* (H →L[ℂ] H)) (ρ : G →* (K →L[ℂ] K)) : Prop := isoPart π ρ ⊤ = ⊤

variable {π : G →* (H →L[ℂ] H)} {π' : G →* (H' →L[ℂ] H')} {ρ : G →* (K →L[ℂ] K)} {ρ' : G →* (K' →L[ℂ] K')}
  {U U' W : Submodule ℂ K} {T T' : H →L[ℂ] K}

theorem mem_homIn : T ∈ homIn π ρ U ↔ (∀ x, T x ∈ U) ∧ ∀ g x, T (π g x) = ρ g (T x) := Iff.rfl

theorem mem_homIn_top : T ∈ homIn π ρ ⊤ ↔ ∀ g x, T (π g x) = ρ g (T x) := and_iff_right fun _ => trivial

theorem homIn_mono (h : U ≤ U') : homIn π ρ U ≤ homIn π ρ U' := fun _ hT => ⟨fun x => h (hT.1 x), hT.2⟩

theorem multIn_mono (h : U ≤ U') : multIn π ρ U ≤ multIn π ρ U' := Submodule.rank_mono (homIn_mono h)

theorem multIn_eq_zero_iff : multIn π ρ U = 0 ↔ homIn π ρ U = ⊥ := Submodule.rank_eq_zero

theorem multIn_lt_aleph0_iff : multIn π ρ U < Cardinal.aleph0 ↔ FiniteDimensional ℂ (homIn π ρ U) :=
  Module.rank_lt_aleph0_iff

variable (π) in

def homInEquiv (hU : IsSubrep ρ U) : homIn π ρ U ≃ₗ[ℂ]
    ContIntertwiningMap (.ofMonoidHom π : ContRepresentation ℂ G H) (.ofMonoidHom hU.rep : ContRepresentation ℂ G U) where
  toFun T := ⟨T.1.codRestrict U T.2.1, fun g => ContinuousLinearMap.ext fun x => Subtype.ext (T.2.2 g x)⟩
  invFun f := ⟨U.subtypeL ∘L f.toContinuousLinearMap, fun x => (f.toContinuousLinearMap x).2,
    fun g x => congrArg Subtype.val (DFunLike.congr_fun (f.isIntertwining' g) x)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem multIn_eq_rank (hU : IsSubrep ρ U) : multIn π ρ U = Module.rank ℂ
    (ContIntertwiningMap (.ofMonoidHom π : ContRepresentation ℂ G H) (.ofMonoidHom hU.rep : ContRepresentation ℂ G U)) :=
  (homInEquiv π hU).rank_eq

theorem multIn_rep (hU : IsSubrep ρ U) : multIn π hU.rep ⊤ = multIn π ρ U :=
  LinearEquiv.rank_eq
    { toFun := fun T => ⟨U.subtypeL ∘L T.1, fun x => (T.1 x).2, fun g x => congrArg Subtype.val (T.2.2 g x)⟩
      invFun := fun T => ⟨T.1.codRestrict U T.2.1, fun _ => trivial, fun g x => Subtype.ext (T.2.2 g x)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem UEquiv.refl (π : G →* (H →L[ℂ] H)) : UEquiv π π := ⟨.refl ℂ H, fun _ _ => rfl⟩

theorem UEquiv.symm (h : UEquiv π ρ) : UEquiv ρ π :=
  let ⟨e, he⟩ := h
  ⟨e.symm, fun g x => e.injective (by rw [he, e.apply_symm_apply, e.apply_symm_apply])⟩

theorem UEquiv.trans (h : UEquiv π ρ) (h' : UEquiv ρ ρ') : UEquiv π ρ' :=
  let ⟨e, he⟩ := h
  let ⟨e', he'⟩ := h'
  ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem UEquiv.comp (h : UEquiv π ρ) (j : G' →* G) : UEquiv (π.comp j) (ρ.comp j) := h.imp fun _ he g => he (j g)

theorem UEquiv.multIn_eq (h : UEquiv π π') : multIn π ρ U = multIn π' ρ U := by
  have key : ∀ {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H']
      [InnerProductSpace ℂ H'] {π : G →* (H →L[ℂ] H)} {π' : G →* (H' →L[ℂ] H')}, UEquiv π π' →
      multIn π' ρ U ≤ multIn π ρ U := fun {H H'} _ _ _ _ π π' ⟨e, he⟩ =>
    LinearMap.rank_le_of_injective (M := homIn π' ρ U) (M₁ := homIn π ρ U)
      { toFun := fun T => ⟨T.1 ∘L (e : H →L[ℂ] H'), fun x => T.2.1 _, fun g x => (congrArg T.1 (he g x)).trans (T.2.2 g _)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      fun T T' h => Subtype.ext (ContinuousLinearMap.ext fun y => by
        obtain ⟨x, rfl⟩ := e.surjective y
        exact DFunLike.congr_fun (congrArg Subtype.val h) x)
  exact le_antisymm (key h.symm) (key h)

theorem homIn_comp {j : G' →* G} (hj : Function.Surjective j) : homIn (π.comp j) (ρ.comp j) U = homIn π ρ U :=
  Submodule.ext fun T => and_congr_right fun _ => (hj.forall (p := fun g => ∀ x, T (π g x) = ρ g (T x))).symm

theorem isSubrep_comp {j : G' →* G} (hj : Function.Surjective j) : IsSubrep (ρ.comp j) U ↔ IsSubrep ρ U :=
  and_congr_right fun _ => (hj.forall (p := fun g => ∀ v ∈ U, ρ g v ∈ U)).symm

theorem UEquiv.isTopIrreducible (h : UEquiv π ρ) (hπ : IsTopIrreducible π) : IsTopIrreducible ρ := by
  obtain ⟨e, he⟩ := h
  have := hπ.1
  refine ⟨e.injective.nontrivial, fun W hW => ?_⟩
  have hs := Submodule.comap_injective_of_surjective (f := (e.toLinearEquiv : H →ₗ[ℂ] K)) e.surjective
  exact (hπ.2 (W.comap (e.toLinearEquiv : H →ₗ[ℂ] K)) ⟨hW.1.preimage e.continuous, fun g x hx =>
    show e (π g x) ∈ W from he g x ▸ hW.2 g _ hx⟩).imp
    (fun h => hs (h.trans (by simp))) fun h => hs (h.trans (by simp))

theorem IsCopy.isIrredSubrep (h : IsCopy π ρ W) (hπ : IsTopIrreducible π) : IsIrredSubrep ρ W :=
  let ⟨hW, e⟩ := h
  hW.isIrredSubrep_iff.2 (e.isTopIrreducible hπ)

theorem isCopy_iff [CompleteSpace H] : IsCopy π ρ W ↔
    ∃ e : H →ₗᵢ[ℂ] K, (∀ g x, e (π g x) = ρ g (e x)) ∧ LinearMap.range e.toLinearMap = W := by
  constructor
  · rintro ⟨hW, e, he⟩
    refine ⟨W.subtypeₗᵢ.comp e.toLinearIsometry, fun g x => congrArg Subtype.val (he g x), le_antisymm ?_ fun y hy => ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact (e x).2
    · exact ⟨e.symm ⟨y, hy⟩, by simp⟩
  · rintro ⟨e, he, rfl⟩
    refine ⟨⟨e.isometry.isClosedEmbedding.isClosed_range, ?_⟩, e.equivRange, fun g x => Subtype.ext (he g x)⟩
    rintro g _ ⟨x, rfl⟩
    exact ⟨π g x, he g x⟩

theorem apply_mem_isoPart (hT : T ∈ homIn π ρ U) (x : H) : T x ∈ isoPart π ρ U :=
  Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem T (Submodule.mem_iSup_of_mem hT ⟨x, rfl⟩))

theorem isoPart_le (hW : IsClosed (W : Set K)) (h : ∀ T ∈ homIn π ρ U, ∀ x, T x ∈ W) : isoPart π ρ U ≤ W :=
  Submodule.topologicalClosure_minimal _ (iSup₂_le fun T hT => by rintro _ ⟨x, rfl⟩; exact h T hT x) hW

theorem isoPart_le_self (hU : IsClosed (U : Set K)) : isoPart π ρ U ≤ U := isoPart_le hU fun _ hT => hT.1

theorem isSubrep_isoPart : IsSubrep ρ (isoPart π ρ U) :=
  ⟨Submodule.isClosed_topologicalClosure _, fun g _ hv =>
    isoPart_le (W := (isoPart π ρ U).comap (ρ g : K →ₗ[ℂ] K))
      ((Submodule.isClosed_topologicalClosure _).preimage (ρ g).continuous)
      (fun T hT x => show ρ g (T x) ∈ _ from hT.2 g x ▸ apply_mem_isoPart hT _) hv⟩

theorem IsIsotypic.refl (π : G →* (H →L[ℂ] H)) : IsIsotypic π π :=
  eq_top_iff.2 fun x _ => apply_mem_isoPart (T := .id ℂ H) (mem_homIn_top.2 fun _ _ => rfl) x

theorem IsIsotypic.homIn_ne_bot [Nontrivial K] (h : IsIsotypic π ρ) : homIn π ρ ⊤ ≠ ⊥ := fun e =>
  (top_ne_bot (α := Submodule ℂ K)) (le_bot_iff.1 (h ▸ isoPart_le (by simp) fun T hT x => by
    rw [e, Submodule.mem_bot] at hT; simp [hT]))

variable (H) in
open Classical in

def unitVec : H := if h : ∃ x : H, ‖x‖ = 1 then h.choose else 0

variable (H) in

theorem norm_unitVec [Nontrivial H] : ‖unitVec H‖ = 1 := by
  have h : ∃ x : H, ‖x‖ = 1 := exists_norm_eq H zero_le_one
  rw [unitVec, dif_pos h]
  exact h.choose_spec

variable (H K) in

def beForm : (H →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] K) →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun T T' => ⟪T' (unitVec H), T (unitVec H)⟫_ℂ)
    (fun _ _ _ => inner_add_right _ _ _) (fun _ _ _ => inner_smul_right _ _ _)
    (fun _ _ _ => inner_add_left _ _ _) (fun _ _ _ => inner_smul_left _ _ _)

abbrev be (T T' : H →L[ℂ] K) : ℂ := beForm H K T T'

theorem be_def (T T' : H →L[ℂ] K) : be T T' = ⟪T' (unitVec H), T (unitVec H)⟫_ℂ := rfl

theorem be_conj_symm (T T' : H →L[ℂ] K) : conj (be T' T) = be T T' := inner_conj_symm _ _

theorem be_self (T : H →L[ℂ] K) : be T T = (‖T (unitVec H)‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _

variable [TopologicalSpace G]

theorem inner_map_map (hρ : IsUnitaryRep ρ) (g : G) (x y : K) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(ρ g : K →ₗ[ℂ] K), hρ.norm_apply g⟩ : K →ₗᵢ[ℂ] K).inner_map_map x y

theorem isUnitaryRep_comp [TopologicalSpace G'] (hρ : IsUnitaryRep ρ) {j : G' →* G} (hj : Continuous j) :
    IsUnitaryRep (ρ.comp j) := ⟨fun g => hρ.norm_apply (j g), fun v => (hρ.continuous_apply v).comp hj⟩

theorem IsIrrUnitary.comp [TopologicalSpace G'] (hπ : IsIrrUnitary π) {j : G' →* G} (hc : Continuous j)
    (hj : Function.Surjective j) : IsIrrUnitary (π.comp j) :=
  ⟨hπ.complete, isUnitaryRep_comp hπ.unitary hc, hπ.irred.1, fun W hW => hπ.irred.2 W ((isSubrep_comp hj).1 hW)⟩

theorem isIrrUnitary_rep [CompleteSpace K] (hρ : IsUnitaryRep ρ) (hW : IsIrredSubrep ρ W) : IsIrrUnitary hW.1.rep :=
  ⟨hW.1.completeSpace, hW.1.isUnitaryRep hρ, hW.1.isIrredSubrep_iff.1 hW⟩

theorem isIrrUnitary_charRep {χ : G →* Circle} (hχ : Continuous χ) : IsIrrUnitary (charRep χ) :=
  ⟨inferInstance, isUnitaryRep_charRep hχ, inferInstance, fun W _ => eq_bot_or_eq_top W⟩

variable [CompleteSpace K]

omit [TopologicalSpace G] in

theorem inner_eq_be_of_norm [CompleteSpace H] (h1 : ∀ g x, ‖π g x‖ = ‖x‖) (h2 : IsTopIrreducible π)
    (h3 : ∀ g x, ‖ρ g x‖ = ‖x‖) (hT : T ∈ homIn π ρ U) (hT' : T' ∈ homIn π ρ U') (x y : H) :
    ⟪T' y, T x⟫_ℂ = be T T' * ⟪y, x⟫_ℂ := by
  letI : TopologicalSpace G := ⊥
  haveI : DiscreteTopology G := ⟨rfl⟩
  have hπ : IsUnitaryRep π := ⟨h1, fun _ => continuous_of_discreteTopology⟩
  have hρ : IsUnitaryRep ρ := ⟨h3, fun _ => continuous_of_discreteTopology⟩
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur H G π h1 (fun S hS h => h2.2 S ⟨hS, h⟩) (T'.adjoint ∘L T) fun g => by
    refine ContinuousLinearMap.ext fun x => ext_inner_left ℂ fun y => ?_
    change ⟪y, π g (T'.adjoint (T x))⟫_ℂ = ⟪y, T'.adjoint (T (π g x))⟫_ℂ
    rw [← inv_inv g, ← hπ.inner_apply_left, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right, hT.2, hT'.2, hρ.inner_apply_left]
  have key : ∀ x y, ⟪T' y, T x⟫_ℂ = c * ⟪y, x⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, show T'.adjoint (T x) = c • x from DFunLike.congr_fun hc x,
      inner_smul_right]
  have := h2.1
  rw [be_def, key, key, inner_self_eq_norm_sq_to_K, norm_unitVec]
  simp

theorem inner_eq_be (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) (hT : T ∈ homIn π ρ U) (hT' : T' ∈ homIn π ρ U')
    (x y : H) : ⟪T' y, T x⟫_ℂ = be T T' * ⟪y, x⟫_ℂ :=
  have := hπ.complete
  inner_eq_be_of_norm hπ.unitary.norm_apply hπ.irred hρ.norm_apply hT hT' x y

theorem inner_apply_eq_be (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) (hT : T ∈ homIn π ρ U) (hT' : T' ∈ homIn π ρ U')
    (g : G) (x y : H) : ⟪T' y, ρ g (T x)⟫_ℂ = be T T' * ⟪y, π g x⟫_ℂ := by
  rw [← hT.2, inner_eq_be hπ hρ hT hT']

theorem norm_apply_eq (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) (hT : T ∈ homIn π ρ U) (x : H) :
    ‖T x‖ = ‖T (unitVec H)‖ * ‖x‖ := by
  have h := inner_eq_be hπ hρ hT hT x x
  rw [be_self, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1
    (Complex.ofReal_injective (by push_cast; exact h))

theorem be_self_pos (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) (hT : T ∈ homIn π ρ U) (h0 : T ≠ 0) :
    0 < (be T T).re :=
  (re_inner_self_pos (𝕜 := ℂ)).2 fun e => h0 (ContinuousLinearMap.ext fun x => norm_eq_zero.1 (by
    rw [norm_apply_eq hπ hρ hT, e, norm_zero, zero_mul]))

theorem isCopy_range (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) (hT : T ∈ homIn π ρ U) (h0 : T ≠ 0) :
    IsCopy π ρ (LinearMap.range (T : H →ₗ[ℂ] K)) := by
  have := hπ.complete
  have hc : ‖T (unitVec H)‖ ≠ 0 := fun e => h0 (ContinuousLinearMap.ext fun x => norm_eq_zero.1 (by
    rw [norm_apply_eq hπ hρ hT, e, zero_mul]))
  refine isCopy_iff.2 ⟨⟨(‖T (unitVec H)‖ : ℂ)⁻¹ • (T : H →ₗ[ℂ] K), fun x => ?_⟩, fun g x => ?_,
    LinearMap.range_smul _ _ (inv_ne_zero (by exact_mod_cast hc))⟩
  · simp [norm_smul, norm_apply_eq hπ hρ hT x, hc]
  · simp [hT.2]

theorem multIn_ne_zero_iff (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) : multIn π ρ U ≠ 0 ↔ ∃ W ≤ U, IsCopy π ρ W := by
  have := hπ.complete
  have := hπ.irred.1
  rw [Ne, multIn_eq_zero_iff, ← Ne, Submodule.ne_bot_iff]
  refine ⟨fun ⟨T, hT, h0⟩ => ⟨_, by rintro _ ⟨x, rfl⟩; exact hT.1 x, isCopy_range hπ hρ hT h0⟩, fun ⟨W, hW, h⟩ => ?_⟩
  obtain ⟨e, he, rfl⟩ := isCopy_iff.1 h
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  exact ⟨e.toContinuousLinearMap, ⟨fun x => hW ⟨x, rfl⟩, he⟩,
    fun h0 => hx (e.injective ((DFunLike.congr_fun h0 x).trans (map_zero e).symm))⟩

theorem homIn_le_iff (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) :
    homIn π ρ U ≤ homIn π ρ U' ↔ ∀ W ≤ U, IsCopy π ρ W → W ≤ U' := by
  have := hπ.complete
  refine ⟨fun h W hW hc => ?_, fun h T hT => ?_⟩
  · obtain ⟨e, he, rfl⟩ := isCopy_iff.1 hc
    rintro _ ⟨x, rfl⟩
    exact (h (x := e.toContinuousLinearMap) ⟨fun x => hW ⟨x, rfl⟩, he⟩).1 x
  · by_cases h0 : T = 0
    · exact h0 ▸ zero_mem _
    · exact ⟨fun x => h _ (by rintro _ ⟨x, rfl⟩; exact hT.1 x) (isCopy_range hπ hρ hT h0) ⟨x, rfl⟩, hT.2⟩

theorem homIn_disc (hπ : IsIrrUnitary π) (hρ : IsUnitaryRep ρ) : homIn π ρ (disc ρ) = homIn π ρ ⊤ :=
  le_antisymm (homIn_mono le_top) ((homIn_le_iff hπ hρ).2 fun _ _ h => (h.isIrredSubrep hπ.irred).le_disc)

theorem uEquiv_of_multIn_ne_zero (hπ : IsIrrUnitary π) (hρ : IsIrrUnitary ρ) (h : multIn π ρ ⊤ ≠ 0) : UEquiv π ρ := by
  have := hπ.complete
  obtain ⟨W, -, hW⟩ := (multIn_ne_zero_iff hπ hρ.unitary).1 h
  have h1 := (hρ.irred.2 W hW.1).resolve_left (hW.isIrredSubrep hπ.irred).2.1
  obtain ⟨e, he, h2⟩ := isCopy_iff.1 hW
  exact ⟨.ofSurjective e (LinearMap.range_eq_top.1 (h2.trans h1)), he⟩

omit [CompleteSpace K] in

theorem multIn_self (hπ : IsIrrUnitary π) : multIn π π ⊤ = 1 := by
  have := hπ.complete
  have := hπ.irred.1
  have h1 : ContinuousLinearMap.id ℂ H ∈ homIn π π ⊤ := mem_homIn_top.2 fun _ _ => rfl
  have : homIn π π ⊤ = ℂ ∙ ContinuousLinearMap.id ℂ H := by
    refine le_antisymm (fun T hT => Submodule.mem_span_singleton.2 ⟨be T (.id ℂ H), ContinuousLinearMap.ext fun x =>
      ext_inner_left ℂ fun y => ?_⟩) ((Submodule.span_singleton_le_iff_mem _ _).2 h1)
    exact (inner_smul_right _ _ _).trans (inner_eq_be hπ hπ.unitary hT h1 x y).symm
  rw [multIn, this, ← Module.finrank_eq_rank, finrank_span_singleton (show ContinuousLinearMap.id ℂ H ≠ 0 from one_ne_zero),
    Nat.cast_one]

theorem inner_eq_zero_of_not_uEquiv (hπ : IsIrrUnitary π) (hπ' : IsIrrUnitary π') (hρ : IsUnitaryRep ρ)
    (h : ¬ UEquiv π π') (hT : T ∈ homIn π ρ U) {S : H' →L[ℂ] K} (hS : S ∈ homIn π' ρ U') (x : H) (y : H') :
    ⟪S y, T x⟫_ℂ = 0 := by
  have := hπ'.complete
  have h1 : S.adjoint ∘L T ∈ homIn π π' ⊤ := mem_homIn_top.2 fun g x => ext_inner_left ℂ fun y => by
    change ⟪y, S.adjoint (T (π g x))⟫_ℂ = ⟪y, π' g (S.adjoint (T x))⟫_ℂ
    rw [← inv_inv g, ← hπ'.unitary.inner_apply_left, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right, hT.2, hS.2, hρ.inner_apply_left]
  rw [multIn_eq_zero_iff.1 (not_not.1 (mt (uEquiv_of_multIn_ne_zero hπ hπ') h)), Submodule.mem_bot] at h1
  rw [← ContinuousLinearMap.adjoint_inner_right, show S.adjoint (T x) = 0 from DFunLike.congr_fun h1 x, inner_zero_right]

theorem IsIsotypic.uEquiv [Nontrivial K] (hπ : IsIrrUnitary π) (hπ' : IsIrrUnitary π') (hρ : IsUnitaryRep ρ)
    (h : IsIsotypic π ρ) (h' : IsIsotypic π' ρ) : UEquiv π π' := by
  by_contra hn
  refine h'.homIn_ne_bot (eq_bot_iff.2 fun S hS => ContinuousLinearMap.ext fun y => ?_)
  have : isoPart π ρ ⊤ ≤ (ℂ ∙ S y)ᗮ := isoPart_le (Submodule.isClosed_orthogonal _) fun T hT x =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 (inner_eq_zero_of_not_uEquiv hπ hπ' hρ hn hT hS x y)
  exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (this (h.ge Submodule.mem_top)))

end Hom

section Dual

variable (G : Type) [Group G] [TopologicalSpace G]

structure IrrU : Type 1 where

  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]

  π : G →* (H →L[ℂ] H)
  isIrr : IsIrrUnitary π

attribute [instance] IrrU.nacg IrrU.ips

variable {G}

instance (R : IrrU G) : CompleteSpace R.H := R.isIrr.complete

instance (R : IrrU G) : Nontrivial R.H := R.isIrr.irred.1

def IrrU.ofChar (χ : G →* Circle) (hχ : Continuous χ) : IrrU G := ⟨ℂ, charRep χ, isIrrUnitary_charRep hχ⟩

variable (G) in

instance IrrU.setoid : Setoid (IrrU G) where
  r R R' := UEquiv R.π R'.π
  iseqv := ⟨fun _ => .refl _, .symm, .trans⟩

variable (G) in

def UDual : Type 1 := Quotient (IrrU.setoid G)

def IrrU.cl (R : IrrU G) : UDual G := Quotient.mk _ R

def UDual.rep (c : UDual G) : IrrU G := Quotient.out c

theorem IrrU.cl_eq_iff {R R' : IrrU G} : R.cl = R'.cl ↔ UEquiv R.π R'.π := Quotient.eq

@[simp] theorem UDual.cl_rep (c : UDual G) : c.rep.cl = c := Quotient.out_eq c

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def UDual.multIn (c : UDual G) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : Cardinal := AutMult.multIn c.rep.π ρ U

theorem IrrU.multIn_cl (R : IrrU G) (ρ : G →* (K →L[ℂ] K)) (U : Submodule ℂ K) : R.cl.multIn ρ U = multIn R.π ρ U :=
  (IrrU.cl_eq_iff.1 (UDual.cl_rep R.cl)).multIn_eq

theorem IrrU.cl_ofChar_inj {χ ψ : G →* Circle} (hχ : Continuous χ) (hψ : Continuous ψ) :
    (IrrU.ofChar χ hχ).cl = (IrrU.ofChar ψ hψ).cl ↔ χ = ψ := by
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  obtain ⟨e, he⟩ : UEquiv (charRep χ) (charRep ψ) := IrrU.cl_eq_iff.1 h
  ext g
  have h1 : e ((χ g : ℂ) • (1 : ℂ)) = (ψ g : ℂ) • e 1 := he g 1
  rw [map_smul] at h1
  exact smul_left_injective ℂ (e.map_ne_zero_iff.2 one_ne_zero) h1

end Dual

section Alg

variable {G G' V W X H : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev toRep (π : G →* (H →L[ℂ] H)) : Representation ℂ G H := (ContRepresentation.ofMonoidHom π).toRepresentation

@[simp] theorem toRep_apply (π : G →* (H →L[ℂ] H)) (g : G) (x : H) : toRep π g x = π g x := rfl

def Contains (τ : Representation ℂ G V) (ρ : Representation ℂ G W) : Prop := ∃ f : τ.IntertwiningMap ρ, f ≠ 0

def isoPartAlg (σ : Representation ℂ G V) (ρ : Representation ℂ G W) : Submodule ℂ W :=
  ⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap

def IsIsotypicAlg (σ : Representation ℂ G V) (ρ : Representation ℂ G W) : Prop := isoPartAlg σ ρ = ⊤

def IsIsotypicDense (σ : Representation ℂ G V) (π : G →* (H →L[ℂ] H)) : Prop :=
  (isoPartAlg σ (toRep π)).topologicalClosure = ⊤

variable {τ : Representation ℂ G X} {σ : Representation ℂ G V} {ρ : Representation ℂ G W}

theorem contains_iff : Contains τ ρ ↔ ∃ f : X →ₗ[ℂ] W, f ≠ 0 ∧ ∀ g x, f (τ g x) = ρ g (f x) :=
  ⟨fun ⟨f, h⟩ => ⟨f.toLinearMap, fun e => h (Representation.IntertwiningMap.ext e), f.isIntertwining⟩,
    fun ⟨f, h, e⟩ => ⟨f.intertwiningMap_of_isIntertwiningMap _ _ e, fun e' => h (congrArg (·.toLinearMap) e')⟩⟩

theorem Contains.of_injective (h : Contains τ σ) (f : σ.IntertwiningMap ρ) (hf : Function.Injective f) :
    Contains τ ρ :=
  let ⟨t, ht, e⟩ := contains_iff.1 h
  contains_iff.2 ⟨f.toLinearMap ∘ₗ t, fun h0 => ht (LinearMap.ext fun x => hf ((DFunLike.congr_fun h0 x).trans
    (map_zero f).symm)), fun g x => (congrArg f (e g x)).trans (DFunLike.congr_fun (f.isIntertwining' g) _)⟩

theorem contains_trivial_iff (K : Subgroup G) :
    Contains (Representation.trivial ℂ K ℂ) (ρ.comp K.subtype) ↔ LGrp.IsSpherical ρ K := by
  rw [contains_iff, LGrp.IsSpherical, Submodule.ne_bot_iff]
  refine ⟨fun ⟨f, h0, e⟩ => ⟨f 1, LGrp.mem_fixed.2 fun k hk => (e ⟨k, hk⟩ 1).symm, fun h => h0 (LinearMap.ext_ring h)⟩,
    fun ⟨x, hx, h0⟩ => ⟨.toSpanSingleton ℂ W x, fun h => h0 (by simpa using DFunLike.congr_fun h 1), fun k c => ?_⟩⟩
  simp [LGrp.mem_fixed.1 hx k k.2]

theorem IsIsotypicAlg.refl (σ : Representation ℂ G V) : IsIsotypicAlg σ σ :=
  eq_top_iff.2 fun x _ => Submodule.mem_iSup_of_mem (.id σ) ⟨x, rfl⟩

theorem IsIsotypicAlg.exists_injective [Nontrivial W] (h : IsIsotypicAlg σ ρ) (hσ : σ.IsIrreducible) :
    ∃ f : σ.IntertwiningMap ρ, Function.Injective f := by
  by_contra hn
  refine (top_ne_bot (α := Submodule ℂ W)) (le_bot_iff.1 (h ▸ iSup_le fun f => ?_))
  rcases eq_bot_or_eq_top f.ker with e | e
  · exact absurd ⟨f, (injective_iff_map_eq_zero _).2 fun x hx => by
      have : x ∈ f.ker := hx
      rwa [e] at this⟩ hn
  · rintro _ ⟨x, rfl⟩
    have : x ∈ f.ker := by rw [e]; trivial
    exact this

theorem IsIsotypicAlg.contains [Nontrivial W] (h : IsIsotypicAlg σ ρ) (hσ : σ.IsIrreducible) {j : G' →* G}
    {τ : Representation ℂ G' X} (ht : Contains τ (σ.comp j)) : Contains τ (ρ.comp j) :=
  let ⟨f, hf⟩ := h.exists_injective hσ
  ht.of_injective ⟨f.toLinearMap, fun g => f.isIntertwining' (j g)⟩ hf

end Alg

example : be (Complex.I • .id ℂ ℂ) (.id ℂ ℂ) = Complex.I ∧ be (.id ℂ ℂ) (Complex.I • .id ℂ ℂ) = -Complex.I := by
  have h : be (.id ℂ ℂ) (.id ℂ ℂ) = 1 := by rw [be_self, ContinuousLinearMap.id_apply, norm_unitVec]; simp
  constructor
  · rw [be, map_smul, LinearMap.smul_apply, ← be, h, smul_eq_mul, mul_one]
  · rw [be, map_smulₛₗ, ← be, h, smul_eq_mul, mul_one, Complex.conj_I]

example {G : Type} [Group G] [TopologicalSpace G] {χ ψ : G →* Circle} (hχ : Continuous χ) (hψ : Continuous ψ)
    (h : χ ≠ ψ) : multIn (charRep χ) (charRep ψ) ⊤ = 0 :=
  not_not.1 fun h0 => h ((IrrU.cl_ofChar_inj hχ hψ).1 (IrrU.cl_eq_iff.2
    (uEquiv_of_multIn_ne_zero (isIrrUnitary_charRep hχ) (isIrrUnitary_charRep hψ) h0)))

end GlobalTheory.AutMult

end
