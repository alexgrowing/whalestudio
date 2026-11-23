import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JNormal

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (blockFnField)
open PositivityTheory.UnitarySelfGeneration.JN

namespace LevelTowerAlt.Comparison₂

theorem join_normal {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₁ Ω₂ Ω : Type} [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω)
    (i₂ : Ω₂ →+* Ω) (y₁ : (Σ k, ι₁ k) → Ω₁) (y₂ : (Σ k, ι₂ k) → Ω₂) (d : ℕ) {X₁ X₂ : Scheme.{0}}
    (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂) (ha₁ : IsArithVar (mCoordIdeal y₁) d)
    (hb₁ : Birational y₁) (hf₁ : FiniteDimensional i₁.fieldRange Ω) (hg₁ : ∀ q : X₁, genPt ξ₁ ⤳ q)
    (hg₂ : ∀ q : X₂, genPt ξ₂ ⤳ q) (ht₁ : CoordTie ℤ ξ₁ fun c' : (k : K₁) → ι₁ k => ∏ k, y₁ ⟨k, c' k⟩)
    (ht₂ : CoordTie ℤ ξ₂ fun c' : (k : K₂) → ι₂ k => ∏ k, y₂ ⟨k, c' k⟩) :
    ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, J k)
      (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, J k) (y : (Σ k, J k) → Ω) (Z : Scheme.{0})
      (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), IsBlockMap κ₁ v₁ ∧ IsBlockMap κ₂ v₂ ∧
      (∀ p, y (v₁ p) = i₁ (y₁ p)) ∧ (∀ p, y (v₂ p) = i₂ (y₂ p)) ∧ mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ ∧
      mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ ∧ IsArithVar (mCoordIdeal y) d ∧ Birational y ∧ (∀ q : Z, genPt ξ ⤳ q) ∧
      CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ IsNormalScheme Z ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₁ h₁ i₁ ∧
      GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₂ h₂ i₂ ∧ IntermediateField.relfinrank (blockFnField (y ∘ v₁)) (blockFnField y) ≠ 0 := by
  obtain ⟨m, w, y, Z, ξ, h₁, h₂, e₁, e₂, -, hg, ht, hN, hd₁, hd₂⟩ :=
    GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join Ω₁ Ω₂ Ω i₁ i₂ K₁ K₂ ι₁ ι₂ y₁ y₂ X₁ X₂ ξ₁ ξ₂ (finite_of i₁ hf₁) hg₁ hg₂ ht₁ ht₂
  let J : K₁ ⊕ K₂ ⊕ Unit → Type := Sum.elim ι₁ (Sum.elim ι₂ fun _ => Fin m)
  have fin : ∀ k, Finite (J k) := by
    rintro (k | k | k)
    · change Finite (ι₁ k); infer_instance
    · change Finite (ι₂ k); infer_instance
    · change Finite (Fin m); infer_instance
  let inst : ∀ k, Fintype (J k) := fun k => Fintype.ofFinite _
  let v₁ : (Σ k, ι₁ k) → Σ k, J k := fun p => ⟨.inl p.1, p.2⟩
  let v₂ : (Σ k, ι₂ k) → Σ k, J k := fun p => ⟨.inr (.inl p.1), p.2⟩
  have hv₁ : IsBlockMap (ι' := J) Sum.inl v₁ := by
    refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have hv₂ : IsBlockMap (ι' := J) (fun k => .inr (.inl k)) v₂ := by
    refine ⟨fun _ _ h => Sum.inl_injective (Sum.inr_injective h), ?_, fun _ => rfl, ?_⟩
    · rintro ⟨k, a⟩ ⟨k', a'⟩ h
      cases h
      rfl
    · rintro ⟨_, a⟩ ⟨k, rfl⟩
      exact ⟨⟨k, a⟩, rfl⟩
  have y1 : y ∘ v₁ = fun p => i₁ (y₁ p) := funext fun p => e₁ p.1 p.2
  have y2 : y ∘ v₂ = fun p => i₂ (y₂ p) := funext fun p => e₂ p.1 p.2
  have hb : Birational (ι := J) y := birational_of_tie (ι := J) ht
  obtain ⟨c, hc⟩ := exists_chart (ι := J) ht
  obtain ⟨c₁, hc₁⟩ := exists_chart ht₁
  have F : (blockFnField (ι := J) y).toSubfield = (RingHom.id Ω).fieldRange :=
    blockFnField_eq (ι := J) (RingHom.id Ω) y hb c hc
  have F₁ : (blockFnField (y ∘ v₁)).toSubfield = i₁.fieldRange := by
    rw [y1]; exact blockFnField_eq i₁ y₁ hb₁ c₁ hc₁
  have fd : FiniteDimensional (blockFnField (y ∘ v₁)) Ω := by
    have : FiniteDimensional (blockFnField (y ∘ v₁)).toSubfield Ω := by rw [F₁]; exact hf₁
    exact this
  have I1 : mCoordIdeal (y ∘ v₁) = mCoordIdeal y₁ := by rw [y1, mCoordIdeal_map]
  have I2 : mCoordIdeal (y ∘ v₂) = mCoordIdeal y₂ := by rw [y2, mCoordIdeal_map]
  refine ⟨K₁ ⊕ K₂ ⊕ Unit, inferInstance, J, inst, Sum.inl, v₁, fun k => .inr (.inl k), v₂, y, Z, ξ, h₁, h₂, hv₁, hv₂,
    congrFun y1, congrFun y2, I1, I2, ?_, hb, hg, ht, hN, hd₁, hd₂, ?_⟩
  · exact GlobalTheory.T.isArithVar_of_block_algebraic K₁ ι₁ _ J Sum.inl v₁ Ω y d hv₁
      (fun k => ⟨c k, Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)⟩) (I1 ▸ ha₁)
      (fun t _ => Algebra.IsAlgebraic.isAlgebraic t)
  · rw [relfinrank_eq i₁ _ _ F₁ F]
    exact Module.finrank_pos.ne'

end LevelTowerAlt.Comparison₂
