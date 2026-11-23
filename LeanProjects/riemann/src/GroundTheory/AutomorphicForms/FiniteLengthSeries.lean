import Mathlib
import GroundTheory.AutomorphicForms.FiniteLengthJacquet
import GroundTheory.AutomorphicForms.FiniteLengthPieces
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function Parabolic

universe u

section Series

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

def subquotientRep (A B : Subrepresentation ρ) :
    Representation ℂ G (B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) :=
  Representation.quotient B.toRepresentation (A.toSubmodule.comap B.toSubmodule.subtype)
    (fun g _ hx => A.apply_mem_toSubmodule g hx)

def subquotientMk (A B : Subrepresentation ρ) :
    Representation.IntertwiningMap B.toRepresentation (subquotientRep A B) :=
  quotientMk _ _

theorem subquotientMk_surjective (A B : Subrepresentation ρ) : Surjective (subquotientMk A B) :=
  quotientMk_surjective _ _

theorem subquotientMk_eq_zero_iff (A B : Subrepresentation ρ) (b : B.toSubmodule) :
    subquotientMk A B b = 0 ↔ (b : V) ∈ A :=
  Submodule.Quotient.mk_eq_zero _

def subrepInclusionOfLE {A B : Subrepresentation ρ} (h : A ≤ B) :
    Representation.IntertwiningMap A.toRepresentation B.toRepresentation :=
  ⟨Submodule.inclusion (p := A.toSubmodule) (p' := B.toSubmodule) fun _ hx => h hx,
    fun _ => LinearMap.ext fun _ => rfl⟩

theorem subrepInclusionOfLE_injective {A B : Subrepresentation ρ} (h : A ≤ B) :
    Injective (subrepInclusionOfLE h) :=
  fun a b hab => by
    have := congrArg (Subtype.val : B.toSubmodule → V) hab
    exact Subtype.ext this

theorem exact_subrepInclusionOfLE_subquotientMk {A B : Subrepresentation ρ} (h : A ≤ B) :
    Exact (subrepInclusionOfLE h) (subquotientMk A B) := by
  intro b
  rw [subquotientMk_eq_zero_iff]
  exact ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩

theorem isIrreducible_subquotientRep {A B : Subrepresentation ρ} (h : A ⋖ B) :
    (subquotientRep A B).IsIrreducible := by
  set T := A.toSubmodule.comap B.toSubmodule.subtype
  obtain ⟨b₀, hb₀B, hb₀A⟩ := SetLike.exists_of_lt h.lt
  have hmk : ∀ b : B.toSubmodule, Submodule.Quotient.mk (p := T) b = 0 ↔ (b : V) ∈ A :=
    fun b => Submodule.Quotient.mk_eq_zero _
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun Z => ?_ }
  · have : Submodule.Quotient.mk (p := T) ⟨b₀, hb₀B⟩ ∈ (⊥ : Subrepresentation (subquotientRep A B)) := by
      rw [hbt]; trivial
    exact hb₀A ((hmk _).1 ((Submodule.mem_bot ℂ).1 this))

  let Z' : Subrepresentation ρ :=
    ⟨(Z.toSubmodule.comap T.mkQ).map B.toSubmodule.subtype, by
      rintro g _ ⟨b, hb, rfl⟩
      exact ⟨B.toRepresentation g b, Z.apply_mem_toSubmodule g hb, rfl⟩⟩
  have hAZ : A ≤ Z' := fun a ha => ⟨⟨a, h.le ha⟩, by
    show Submodule.Quotient.mk (p := T) _ ∈ Z.toSubmodule
    rw [(hmk _).2 ha]
    exact Z.toSubmodule.zero_mem, rfl⟩
  have hZB : Z' ≤ B := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hmem : ∀ b : B.toSubmodule, (b : V) ∈ Z' → Submodule.Quotient.mk (p := T) b ∈ Z := by
    rintro b ⟨b', hb', hbb'⟩
    rw [show b = b' from Subtype.ext hbb'.symm]
    exact hb'
  rcases h.eq_or_eq hAZ hZB with hZ | hZ
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun q hq => ?_)
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective T q
    have : (b : V) ∈ Z' := ⟨b, hq, rfl⟩
    rw [hZ] at this
    exact (Submodule.mem_bot ℂ).2 ((hmk b).2 this)
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun q _ => ?_)
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective T q
    exact hmem b (by rw [hZ]; exact b.2)

theorem HasFiniteLength.exists_compositionSeries (h : HasFiniteLength ρ) :
    ∃ (k : ℕ) (S : ℕ → Subrepresentation ρ), S 0 = ⊥ ∧ S k = ⊤ ∧ ∀ j < k, S j ⋖ S (j + 1) := by
  have := h.wellFoundedLT
  have := h.wellFoundedGT
  obtain ⟨a, h0, k, hk, hcov⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (bot_le : (⊥ : Subrepresentation ρ) ≤ ⊤)
  exact ⟨k, a, h0, hk, hcov⟩

variable {W U : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  {α : Representation ℂ G W} {γ : Representation ℂ G U}

theorem hasFiniteLength_of_exact (f : Representation.IntertwiningMap α ρ)
    (g : Representation.IntertwiningMap ρ γ) (hf : Injective f) (hfg : Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength ρ := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α ρ f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule ρ γ g
  have hf' : Injective f' := hf
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range g') :=
    IsFiniteLength.of_injective hC (LinearMap.range g').injective_subtype
  have hex : Exact f' g'.rangeRestrict := by
    intro y
    have : g'.rangeRestrict y = 0 ↔ g y = 0 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact f' g'.rangeRestrict hf' g'.surjective_rangeRestrict hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hA, Module.length_ne_top_iff.2 hr⟩

end Series

namespace Parabolic

open Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section IndMap

variable {β : Fin n → ℕ} {W W' W'' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
  [Module ℂ W'] [AddCommGroup W''] [Module ℂ W''] {σ : Representation ℂ (levi F n β) W}
  {σ' : Representation ℂ (levi F n β) W'} {σ'' : Representation ℂ (levi F n β) W''}

theorem comp_mem_parabolicIndSpace (f : Representation.IntertwiningMap σ σ')
    {φ : GL (Fin n) F → W} (hφ : φ ∈ parabolicIndSpace F n β σ) :
    (f ∘ φ) ∈ parabolicIndSpace F n β σ' := by
  obtain ⟨h1, K, hK, hφK⟩ := hφ
  refine ⟨fun p g => ?_, K, hK, fun k hk g => ?_⟩
  · show f (φ ((p : GL (Fin n) F) * g)) = inflateTwist F n β σ' p (f (φ g))
    rw [h1 p g, inflateTwist_apply, inflateTwist_apply, map_smul,
      Representation.IntertwiningMap.isIntertwining]
  · show f (φ (g * k)) = f (φ g)
    rw [hφK k hk g]

def parabolicIndMap (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (parabolicInd F n β σ) (parabolicInd F n β σ') where
  toLinearMap :=
    { toFun := fun φ => ⟨f ∘ (φ : GL (Fin n) F → W), comp_mem_parabolicIndSpace f φ.2⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add f _ _)
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => map_smul f _ _) }
  isIntertwining' _ := LinearMap.ext fun _ => rfl

theorem coe_parabolicIndMap_apply (f : Representation.IntertwiningMap σ σ')
    (φ : parabolicIndSpace F n β σ) (x : GL (Fin n) F) :
    ((parabolicIndMap f φ : parabolicIndSpace F n β σ') : GL (Fin n) F → W') x =
      f ((φ : GL (Fin n) F → W) x) := rfl

theorem parabolicIndMap_injective (f : Representation.IntertwiningMap σ σ') (hf : Injective f) :
    Injective (parabolicIndMap f) := fun _ _ h =>
  Subtype.ext (funext fun x => hf (congrFun (congrArg Subtype.val h) x))

theorem exists_parabolicIndMap_eq (f : Representation.IntertwiningMap σ σ') (hf : Injective f)
    (φ : parabolicIndSpace F n β σ') (hφ : ∀ x, ∃ y, f y = (φ : GL (Fin n) F → W') x) :
    ∃ ψ, parabolicIndMap f ψ = φ := by
  choose ψ hψ using hφ
  obtain ⟨h1, K, hK, hφK⟩ := φ.2
  refine ⟨⟨ψ, fun p x => hf ?_, K, hK, fun k hk x => hf ?_⟩, Subtype.ext (funext hψ)⟩
  · show f (ψ ((p : GL (Fin n) F) * x)) = f (inflateTwist F n β σ p (ψ x))
    rw [hψ, h1 p x, inflateTwist_apply, inflateTwist_apply, map_smul,
      Representation.IntertwiningMap.isIntertwining, hψ]
  · rw [hψ, hψ, hφK k hk x]

theorem exact_parabolicIndMap (f : Representation.IntertwiningMap σ σ')
    (g : Representation.IntertwiningMap σ' σ'') (hf : Injective f) (hfg : Exact f g) :
    Exact (parabolicIndMap f) (parabolicIndMap g) := by
  intro φ
  constructor
  · intro hφ
    exact exists_parabolicIndMap_eq f hf φ fun x =>
      (hfg _).1 (congrFun (congrArg Subtype.val hφ) x)
  · rintro ⟨ψ, rfl⟩
    refine Subtype.ext (funext fun x => ?_)
    exact (hfg _).2 ⟨_, rfl⟩

theorem parabolicIndMap_surjective (f : Representation.IntertwiningMap σ σ') (hf : Bijective f) :
    Surjective (parabolicIndMap f) := fun φ =>
  exists_parabolicIndMap_eq f hf.1 φ fun _ => hf.2 _

theorem hasFiniteLength_parabolicInd_of_factors {W₀ : Type u} [AddCommGroup W₀] [Module ℂ W₀]
    {σ₀ : Representation ℂ (levi F n β) W₀} (hσ : IsSmooth σ₀) (hfl : HasFiniteLength σ₀)
    (H : ∀ (W' : Type u) [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (levi F n β) W')
      [ρ.IsIrreducible], IsSmooth ρ → IsSubquotient ρ σ₀ → HasFiniteLength (parabolicInd F n β ρ)) :
    HasFiniteLength (parabolicInd F n β σ₀) := by
  obtain ⟨k, S, h0, hk, hcov⟩ := hfl.exists_compositionSeries
  have key : ∀ j ≤ k, HasFiniteLength (parabolicInd F n β (S j).toRepresentation) := by
    intro j hj
    induction j with
    | zero =>
      have hS0 : ∀ v, v ∈ (S 0).toSubmodule → v = 0 := fun v hv => by
        rw [h0] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      have : Subsingleton (S 0).toSubmodule :=
        ⟨fun a b => Subtype.ext ((hS0 _ a.2).trans (hS0 _ b.2).symm)⟩
      have := subsingleton_indSpace (blockUpper F n β) (inflateTwist F n β (S 0).toRepresentation)
      exact hasFiniteLength_of_subsingleton
    | succ j ih =>
      have hcj := hcov j (by omega)
      have := isIrreducible_subquotientRep hcj
      exact hasFiniteLength_of_exact (parabolicIndMap (subrepInclusionOfLE hcj.le))
        (parabolicIndMap (subquotientMk (S j) (S (j + 1))))
        (parabolicIndMap_injective _ (subrepInclusionOfLE_injective hcj.le))
        (exact_parabolicIndMap _ _ (subrepInclusionOfLE_injective hcj.le)
          (exact_subrepInclusionOfLE_subquotientMk hcj.le))
        (ih (by omega))
        (H _ (subquotientRep (S j) (S (j + 1)))
          (isSmooth_quotient (isSmooth_subrep hσ _) _ _)
          ⟨S (j + 1), subquotientMk _ _, subquotientMk_surjective _ _⟩)
  refine hasFiniteLength_of_surjective (parabolicIndMap (subrepInclusion (S k)))
    (parabolicIndMap_surjective _ ⟨fun a b hab => Subtype.ext hab, fun v => ⟨⟨v, ?_⟩, rfl⟩⟩)
    (key k le_rfl)
  rw [hk]
  trivial

end IndMap

section Jacquet

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem hasFiniteLength_jacquetRep_of_factors (hπ : IsSmooth π) (hfl : HasFiniteLength π)
    (β : Fin n → ℕ)
    (H : ∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V'] (π' : Representation ℂ (GL (Fin n) F) V')
      [π'.IsIrreducible], IsSmooth π' → IsSubquotient π' π → HasFiniteLength (jacquetRep F n β π')) :
    HasFiniteLength (jacquetRep F n β π) := by
  obtain ⟨k, S, h0, hk, hcov⟩ := hfl.exists_compositionSeries
  have key : ∀ j ≤ k, HasFiniteLength (jacquetRep F n β (S j).toRepresentation) := by
    intro j hj
    induction j with
    | zero =>
      have hS0 : ∀ v, v ∈ (S 0).toSubmodule → v = 0 := fun v hv => by
        rw [h0] at hv
        exact (Submodule.mem_bot ℂ).1 hv
      have : Subsingleton (S 0).toSubmodule :=
        ⟨fun a b => Subtype.ext ((hS0 _ a.2).trans (hS0 _ b.2).symm)⟩
      have : Subsingleton (JacquetModule F n β (S 0).toRepresentation) :=
        ⟨fun a b => by
          obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
          obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
          rw [Subsingleton.elim a b]⟩
      exact hasFiniteLength_of_subsingleton
    | succ j ih =>
      have hcj := hcov j (by omega)
      have := isIrreducible_subquotientRep hcj
      have hs : ∀ i, IsSmooth (S i).toRepresentation := fun i => isSmooth_subrep hπ _
      have hq : IsSmooth (subquotientRep (S j) (S (j + 1))) :=
        isSmooth_quotient (hs _) _ _
      exact hasFiniteLength_of_exact (jacquetMap F n β (subrepInclusionOfLE hcj.le))
        (jacquetMap F n β (subquotientMk (S j) (S (j + 1))))
        (jacquetMap_injective (hs _) (hs _) _ (subrepInclusionOfLE_injective hcj.le) β)
        (exact_jacquetMap (hs _) hq _ _ (exact_subrepInclusionOfLE_subquotientMk hcj.le))
        (ih (by omega))
        (H _ (subquotientRep (S j) (S (j + 1))) hq
          ⟨S (j + 1), subquotientMk _ _, subquotientMk_surjective _ _⟩)
  refine hasFiniteLength_of_surjective (jacquetMap F n β (subrepInclusion (S k)))
    (jacquetMap_surjective _ (fun v => ⟨⟨v, ?_⟩, rfl⟩) β) (key k le_rfl)
  rw [hk]
  trivial

end Jacquet

end Parabolic

end GroundTheory.Automorphic
