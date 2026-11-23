import Mathlib
import GroundTheory.AutomorphicForms.FiniteLengthSubquotient
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open Function

namespace Parabolic

open Function Matrix Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Congr

variable {α α' : Type*} [LinearOrder α] [LinearOrder α'] {β : Fin n → α} {γ : Fin n → α'}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eq_iff_eq_of_lt_iff (h : ∀ i j, β i < β j ↔ γ i < γ j) (i j : Fin n) :
    β i = β j ↔ γ i = γ j := by
  constructor
  · intro e
    rcases lt_trichotomy (γ i) (γ j) with hl | he | hg
    · exact absurd ((h i j).2 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).2 hg) (by rw [e]; exact lt_irrefl _)
  · intro e
    rcases lt_trichotomy (β i) (β j) with hl | he | hg
    · exact absurd ((h i j).1 hl) (by rw [e]; exact lt_irrefl _)
    · exact he
    · exact absurd ((h j i).1 hg) (by rw [e]; exact lt_irrefl _)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem blockUpper_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    blockUpper F n β = blockUpper F n γ := by
  ext g
  simp only [mem_blockUpper, Matrix.BlockTriangular]
  exact forall_congr' fun i => forall_congr' fun j => imp_congr_left (h j i)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem unipotentRadical_congr (h : ∀ i j, β i < β j ↔ γ i < γ j) :
    unipotentRadical F n β = unipotentRadical F n γ := by
  ext g
  rw [mem_unipotentRadical, mem_unipotentRadical, blockUpper_congr h]
  exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j =>
    imp_congr_left (eq_iff_eq_of_lt_iff h i j)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_iff {i j : Fin n} : blockRank β i < blockRank β j ↔ β i < β j := by
  refine ⟨fun h => ?_, blockRank_lt⟩
  by_contra h'
  rcases (not_lt.1 h').lt_or_eq with h'' | h''
  · exact absurd (blockRank_lt h'') (by omega)
  · exact absurd (blockRank_eq h''.symm) (by omega)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem blockRank_lt_card (β : Fin n → α) (i : Fin n) : blockRank β i < n := by
  have : (Finset.univ.filter fun j => β j < β i) ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, fun h => by
      have := h ▸ Finset.mem_univ i
      simp at this⟩
  simpa [blockRank] using Finset.card_lt_card this

def rankFun (β : Fin n → α) : Fin n → Fin n := fun i => ⟨blockRank β i, blockRank_lt_card β i⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem rankFun_lt_iff (β : Fin n → α) (i j : Fin n) :
    ((rankFun β i : Fin n) : ℕ) < (rankFun β j : ℕ) ↔ β i < β j :=
  blockRank_lt_iff

end Congr

section Jacquet

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {X : Representation ℂ (GL (Fin n) F) V} {π : Representation ℂ (GL (Fin n) F) V'}

theorem jacquetMap_surjective (p : Representation.IntertwiningMap X π) (hp : Surjective p)
    (γ : Fin n → ℕ) : Surjective (jacquetMap F n γ p) := by
  intro y
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, jacquetMap_mk _ _⟩

theorem jacquetMap_injective (hX : IsSmooth X) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap X π) (hi : Injective i) (γ : Fin n → ℕ) :
    Injective (jacquetMap F n γ i) := by
  have hex := exact_jacquetMap (β := γ) hX hπ (0 : Representation.IntertwiningMap X X) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : V) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [jacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.jacquetRep (hX : IsSmooth X) (h : IsSubquotient π X) (γ : Fin n → ℕ) :
    IsSubquotient (jacquetRep F n γ π) (jacquetRep F n γ X) := by
  obtain ⟨C, p, hp⟩ := h
  exact .of_injective_of_surjective (jacquetMap F n γ (subrepInclusion C))
    (jacquetMap_injective (isSmooth_subrep hX C) hX _ (fun a b h => Subtype.ext h) γ)
    (jacquetMap F n γ p) (jacquetMap_surjective p hp γ)

theorem surjective_frobeniusParabolic [Nontrivial V'] {δ : Fin n → ℕ} {U : Type*}
    [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible]
    (hπ : IsSmooth π) (Φ : Representation.IntertwiningMap π (parabolicInd F n δ τ))
    (hΦ : Injective Φ) : Surjective (frobeniusParabolic F n δ τ hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero
    (frobeniusParabolic F n δ τ hπ Φ) with h | h
  · exact h
  · exfalso
    have h0 : Φ = 0 := (frobeniusParabolic F n δ τ hπ).injective (h.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : V')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Jacquet

end Parabolic

section Irreducible

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] {ρ : Representation ℂ G V} {π : Representation ℂ G W}

theorem IsSubquotient.exists_bijective [π.IsIrreducible] [ρ.IsIrreducible]
    (h : IsSubquotient π ρ) : ∃ e : Representation.IntertwiningMap π ρ, Bijective e := by
  obtain ⟨C, p, hp⟩ := h
  obtain ⟨x, hx⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have hC : C = ⊤ := (eq_bot_or_eq_top C).resolve_left fun hC => hx (by
    obtain ⟨c, rfl⟩ := hp x
    have hc : (c : V) ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [← hC]; exact c.2
    rw [show c = 0 from Subtype.ext ((Submodule.mem_bot ℂ).1 hc), map_zero])
  have hCtop : ∀ v : V, v ∈ C.toSubmodule := fun v => by rw [hC]; trivial

  let K : Subrepresentation ρ := ⟨(LinearMap.ker p.toLinearMap).map C.toSubmodule.subtype, by
    rintro g _ ⟨c, hc, rfl⟩
    refine ⟨C.toRepresentation g c, ?_, rfl⟩
    have hc' : p c = 0 := hc
    show p (C.toRepresentation g c) = 0
    rw [Representation.IntertwiningMap.isIntertwining, hc', map_zero]⟩
  have hK : K = ⊥ := (eq_bot_or_eq_top K).resolve_right fun hK => hx (by
    obtain ⟨c, rfl⟩ := hp x
    have hc : (c : V) ∈ K.toSubmodule := by rw [hK]; trivial
    obtain ⟨c', hc', hcc'⟩ := hc
    rw [show c = c' from Subtype.ext hcc'.symm]
    exact hc')
  have hpinj : Injective p := (injective_iff_map_eq_zero _).2 fun c hc => Subtype.ext (by
    have hmem : (c : V) ∈ K.toSubmodule := ⟨c, hc, rfl⟩
    rw [hK] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem)
  let e₀ : C.toSubmodule ≃ₗ[ℂ] W := LinearEquiv.ofBijective p.toLinearMap ⟨hpinj, hp⟩
  have he₀ : ∀ c, e₀ c = p c := fun c => rfl
  refine ⟨⟨C.toSubmodule.subtype ∘ₗ e₀.symm.toLinearMap, fun g => LinearMap.ext fun y => ?_⟩,
    ⟨?_, fun v => ⟨e₀ ⟨v, hCtop v⟩, by simp⟩⟩⟩
  · obtain ⟨c, rfl⟩ := e₀.surjective y
    have h1 : π g (e₀ c) = e₀ (C.toRepresentation g c) := by
      rw [he₀, he₀, Representation.IntertwiningMap.isIntertwining]
    simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe, h1,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    rfl
  · intro a b hab
    exact e₀.symm.injective (Subtype.ext hab)

end Irreducible

end GroundTheory.Automorphic
