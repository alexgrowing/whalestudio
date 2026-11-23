import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubImage

variable {k H V Y Q : Type} [Field k] [Group H] [AddCommGroup V] [Module k V] [AddCommGroup Y]
  [Module k Y] [AddCommGroup Q] [Module k Q]

theorem isIrreducible_of_minimal {η : Representation k H Y} (R : Subrepresentation η)
    (hne : R.toSubmodule ≠ ⊥)
    (h : ∀ U : Subrepresentation η, U.toSubmodule ≤ R.toSubmodule →
      U.toSubmodule = ⊥ ∨ R.toSubmodule ≤ U.toSubmodule) :
    R.toRepresentation.IsIrreducible := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨⊥, ⊤, fun he => hy0 ?_⟩
    have h1 : (⟨y, hy⟩ : R.toSubmodule) ∈ (⊤ : Subrepresentation R.toRepresentation).toSubmodule :=
      Submodule.mem_top
    rw [← he] at h1
    have h2 := (Submodule.mem_bot k).1 h1
    simpa using congrArg Subtype.val h2
  · intro U'
    let U : Subrepresentation η := ⟨U'.toSubmodule.map R.toSubmodule.subtype, by
      rintro g _ ⟨v, hv, rfl⟩
      exact ⟨R.toRepresentation g v, U'.apply_mem_toSubmodule g hv, rfl⟩⟩
    rcases h U (by rintro _ ⟨v, -, rfl⟩; exact v.2) with h1 | h1
    · left
      apply Subrepresentation.toSubmodule_injective
      show U'.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      have h3 : (v : Y) ∈ U.toSubmodule := ⟨v, hv, rfl⟩
      rw [h1] at h3
      exact (Submodule.mem_bot k).2 (Subtype.ext ((Submodule.mem_bot k).1 h3))
    · right
      apply Subrepresentation.toSubmodule_injective
      show U'.toSubmodule = ⊤
      rw [eq_top_iff]
      intro v _
      obtain ⟨w, hw, hwv⟩ := h1 v.2
      have h4 : w = v := Subtype.ext hwv
      subst h4
      exact hw

theorem exists_irreducible_of_atom {ρ : Representation k H V} {η : Representation k H Y}
    {τ : Representation k H Q} (F : ρ.IntertwiningMap η) (q : ρ.IntertwiningMap τ)
    (hker : ∀ x, q x = 0 → F x = 0) (A : Subrepresentation τ) (hA : IsAtom A)
    (x₀ : V) (hx₀ : q x₀ ∈ A.toSubmodule) (hF : F x₀ ≠ 0) :
    ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
      R.toSubmodule ≤ LinearMap.range F.toLinearMap := by
  let T : Submodule k V := A.toSubmodule.comap q.toLinearMap
  have hT : ∀ g, ∀ x ∈ T, ρ g x ∈ T := fun g x hx => by
    show q (ρ g x) ∈ A.toSubmodule
    rw [q.isIntertwining]
    exact A.apply_mem_toSubmodule g hx
  let R : Subrepresentation η := ⟨T.map F.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hT g x hx, F.isIntertwining _ _ g x⟩⟩
  refine ⟨R, isIrreducible_of_minimal R ?_ ?_, ?_⟩
  · intro h0
    have : F x₀ ∈ R.toSubmodule := ⟨x₀, hx₀, rfl⟩
    rw [h0] at this
    exact hF ((Submodule.mem_bot k).1 this)
  · intro U hUR

    let T' : Subrepresentation τ := ⟨(T ⊓ U.toSubmodule.comap F.toLinearMap).map q.toLinearMap, by
      rintro g _ ⟨x, ⟨hxT, hxU⟩, rfl⟩
      refine ⟨ρ g x, ⟨hT g x hxT, ?_⟩, q.isIntertwining _ _ g x⟩
      show F (ρ g x) ∈ U.toSubmodule
      rw [F.isIntertwining]
      exact U.apply_mem_toSubmodule g hxU⟩
    have hT'A : T' ≤ A := by
      rintro _ ⟨x, ⟨hxT, -⟩, rfl⟩
      exact hxT
    rcases hA.le_iff.1 hT'A with h0 | h0
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hxT, rfl⟩ := hUR hy
      have hq : q x = 0 := by
        have : q x ∈ T'.toSubmodule := ⟨x, ⟨hxT, hy⟩, rfl⟩
        rw [h0] at this
        exact (Submodule.mem_bot k).1 this
      exact (Submodule.mem_bot k).2 (hker x hq)
    · right
      rintro _ ⟨x, hxT, rfl⟩
      have : q x ∈ T'.toSubmodule := by rw [h0]; exact hxT
      obtain ⟨t, ⟨htT, htU⟩, hqt⟩ := this
      have hd : F (x - t) = 0 := hker _ (by
        rw [map_sub]; exact sub_eq_zero.2 (by exact hqt.symm))
      rw [map_sub, sub_eq_zero] at hd
      show F x ∈ U.toSubmodule
      rw [hd]; exact htU
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩

theorem exists_atom_of_semisimple {ρ : Representation k H V} {η : Representation k H Y}
    {τ : Representation k H Q} (hss : τ.IsSemisimpleRepresentation) (F : ρ.IntertwiningMap η)
    (q : ρ.IntertwiningMap τ) (hker : ∀ x, q x = 0 → F x = 0) (hF : F ≠ 0) :
    ∃ A : Subrepresentation τ, IsAtom A ∧ ∃ x₀, q x₀ ∈ A.toSubmodule ∧ F x₀ ≠ 0 := by
  by_contra hno
  push_neg at hno
  haveI : IsSemisimpleModule (MonoidAlgebra k H) τ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule τ).1 hss
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := τ)
  let B : Subrepresentation τ := ⟨(LinearMap.ker F.toLinearMap).map q.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨ρ g x, ?_, q.isIntertwining _ _ g x⟩
    show F (ρ g x) = 0
    rw [F.isIntertwining]
    have hx' : F x = 0 := hx
    rw [hx', map_zero]⟩
  have hRB : q.range ≤ B := by
    rw [← e.le_iff_le, ← IsSemisimpleModule.sSup_simples_le (e q.range)]
    refine sSup_le ?_
    rintro m ⟨hm, hmle⟩
    have hm' : IsAtom m := (isSimpleModule_iff_isAtom).1 hm
    rw [← e.apply_symm_apply m] at hm' hmle ⊢
    rw [e.isAtom_iff] at hm'
    rw [e.le_iff_le] at hmle ⊢
    intro a ha
    obtain ⟨x, rfl⟩ := hmle ha
    exact ⟨x, hno _ hm' x ha, rfl⟩
  apply hF
  ext x
  obtain ⟨y, hy, hyx⟩ := hRB (show q x ∈ q.range from ⟨x, rfl⟩)
  have hy' : F y = 0 := hy
  have hd : F (x - y) = 0 := hker _ (by
    rw [map_sub]; exact sub_eq_zero.2 (by exact hyx.symm))
  rw [map_sub, hy', sub_zero] at hd
  show F x = 0
  exact hd

section Quot

variable {G X : Type} [Group G] [AddCommGroup X] [Module k X]

theorem isIrreducible_subQuot {σ : Representation k G X} (M M' : Subrepresentation σ)
    (hlt : M' < M) (hmax : ∀ W : Subrepresentation σ, W < M → ¬ M' < W) :
    (subQuot M M').IsIrreducible := by
  obtain ⟨x, hxM, hxM'⟩ := SetLike.exists_of_lt hlt
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun he => hxM' ?_⟩
    have h1 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) :
        M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) ∈
        (⊤ : Subrepresentation (subQuot M M')).toSubmodule := Submodule.mem_top
    rw [← he] at h1
    have h2 : (Submodule.Quotient.mk (⟨x, hxM⟩ : M.toSubmodule) :
        M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0 :=
      (Submodule.mem_bot k).1 h1
    exact (Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 h2
  · intro U
    let W : Subrepresentation σ :=
      ⟨(U.toSubmodule.comap (Submodule.mkQ _)).map M.toSubmodule.subtype, by
        rintro g _ ⟨m, hm, rfl⟩
        exact ⟨M.toRepresentation g m, U.apply_mem_toSubmodule g hm, rfl⟩⟩
    have hM'W : M' ≤ W := by
      intro y hy
      refine ⟨⟨y, hlt.le hy⟩, ?_, rfl⟩
      show Submodule.mkQ _ _ ∈ U.toSubmodule
      have h0 : (Submodule.Quotient.mk (⟨y, hlt.le hy⟩ : M.toSubmodule) :
          M.toSubmodule ⧸ M'.toSubmodule.comap M.toSubmodule.subtype) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hy
      rw [Submodule.mkQ_apply, h0]
      exact zero_mem _
    have hWM : W ≤ M := by
      rintro _ ⟨m, -, rfl⟩
      exact m.2
    rcases eq_or_lt_of_le hWM with h | h
    · right
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊤
      rw [eq_top_iff]
      intro z _
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hm : (m : X) ∈ W := by rw [h]; exact m.2
      obtain ⟨m', hm', hm'm⟩ := hm
      have : m' = m := Subtype.ext hm'm
      subst this
      exact hm'
    · left
      have hW : W = M' := (eq_of_le_of_not_lt hM'W (hmax W h)).symm
      apply Subrepresentation.toSubmodule_injective
      show U.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hm : (m : X) ∈ W := ⟨m, hz, rfl⟩
      rw [hW] at hm
      exact (Submodule.mem_bot k).2 ((Submodule.Quotient.mk_eq_zero _).2 hm)

theorem isSubquotient_subQuot {σ : Representation k G X} (M M' : Subrepresentation σ) :
    IsSubquotient (subQuot M M') σ :=
  ⟨M, ⟨Submodule.mkQ _, fun g => LinearMap.ext fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

end Quot

theorem exists_irreducible_le_range : ∀ (L H : Type) [Group L] [Group H] (s : H →* L) (X : Type)
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ L X), GlobalTheory.SmGL.HasFiniteLength σ →
    (∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (τ : Representation ℂ L Z), GlobalTheory.SmGL.IsSubquotient τ σ →
      τ.IsIrreducible → Representation.IsSemisimpleRepresentation (τ.comp s)) →
    ∀ (S : Subrepresentation (σ.comp s)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
      (η : Representation ℂ H Y) (F : S.toRepresentation.IntertwiningMap η), F ≠ 0 →
      ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
        R.toSubmodule ≤ LinearMap.range F.toLinearMap := by
  intro L H _ _ s X _ _ σ hfl hss S Y _ _ η
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  rw [HasFiniteLength, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff',
    isArtinian_iff] at hfl
  obtain ⟨hN, hA⟩ := hfl
  haveI : WellFoundedGT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedGT
  haveI : WellFoundedLT (Submodule (MonoidAlgebra ℂ L) σ.asModule) := ⟨hA⟩
  haveI : WellFoundedLT (Subrepresentation σ) := φ.toOrderEmbedding.wellFoundedLT
  suffices key : ∀ M : Subrepresentation σ, ∀ S : Subrepresentation (σ.comp s),
      S.toSubmodule ≤ M.toSubmodule → ∀ F : S.toRepresentation.IntertwiningMap η, F ≠ 0 →
      ∃ R : Subrepresentation η, R.toRepresentation.IsIrreducible ∧
        R.toSubmodule ≤ LinearMap.range F.toLinearMap from
    fun F hF => key ⊤ S le_top F hF
  intro M
  induction M using WellFoundedLT.induction with
  | _ M ih =>
  intro S hSM F hF
  obtain ⟨x₁, hx₁⟩ : ∃ x, F x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF (by ext x; exact h x)
  have hMbot : ⊥ < M := by
    refine bot_lt_iff_ne_bot.2 fun h => hx₁ ?_
    have h1 : (x₁ : X) ∈ M.toSubmodule := hSM x₁.2
    rw [h] at h1
    have h0 : x₁ = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 h1)
    rw [h0, map_zero]
  obtain ⟨M', hM'lt, hM'max⟩ :=
    (wellFounded_gt (α := Subrepresentation σ)).has_min {W | W < M} ⟨⊥, hMbot⟩
  have hM'lt' : M' < M := hM'lt
  let M'H : Subrepresentation (σ.comp s) :=
    ⟨M'.toSubmodule, fun h _ hv => M'.apply_mem_toSubmodule (s h) hv⟩
  by_cases hcase : ∃ x : S.toSubmodule, (x : X) ∈ M'.toSubmodule ∧ F x ≠ 0
  · obtain ⟨x, hxM', hFx⟩ := hcase
    let S' : Subrepresentation (σ.comp s) := S ⊓ M'H
    have hle : S'.toSubmodule ≤ S.toSubmodule := inf_le_left
    let F' : S'.toRepresentation.IntertwiningMap η :=
      ⟨F.toLinearMap ∘ₗ Submodule.inclusion hle, fun h => by
        ext v
        exact F.isIntertwining _ _ h (Submodule.inclusion hle v)⟩
    have hF' : F' ≠ 0 := by
      intro h0
      apply hFx
      have h2 : F' ⟨x, x.2, hxM'⟩ = 0 := by rw [h0]; rfl
      exact h2
    obtain ⟨R, hR, hRle⟩ := ih M' hM'lt' S' inf_le_right F' hF'
    refine ⟨R, hR, hRle.trans ?_⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨Submodule.inclusion hle v, rfl⟩
  · push_neg at hcase
    have hirr := isIrreducible_subQuot M M' hM'lt' (fun W hW h => hM'max W hW h)
    have hssτ := hss _ (subQuot M M') (isSubquotient_subQuot M M') hirr
    let q : S.toRepresentation.IntertwiningMap ((subQuot M M').comp s) :=
      ⟨(Submodule.mkQ _) ∘ₗ Submodule.inclusion hSM, fun h => LinearMap.ext fun _ => rfl⟩
    have hker : ∀ x, q x = 0 → F x = 0 := fun x hx =>
      hcase x ((Submodule.Quotient.mk_eq_zero (M'.toSubmodule.comap M.toSubmodule.subtype)).1 hx)
    obtain ⟨A, hA, x₀, hx₀, hF₀⟩ := exists_atom_of_semisimple hssτ F q hker hF
    exact exists_irreducible_of_atom F q hker A hA x₀ hx₀ hF₀

end GlobalTheory.IrrSubImage
