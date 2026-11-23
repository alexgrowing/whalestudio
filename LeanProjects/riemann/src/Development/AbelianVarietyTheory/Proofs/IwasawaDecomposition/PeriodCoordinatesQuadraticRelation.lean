import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Set Filter Topology

theorem FramesCover.lead_eq_zero {α β γ δ α' β' γ' δ' t₁ t₂ : ℂ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₁₂ : t₁ ≠ t₂)
    (e₀ : α * β = γ * δ) (e₁ : (α + t₁ * α') * (β + t₁ * β') = (γ + t₁ * γ') * (δ + t₁ * δ'))
    (e₂ : (α + t₂ * α') * (β + t₂ * β') = (γ + t₂ * γ') * (δ + t₂ * δ')) : α' * β' = γ' * δ' := by
  have h : (α' * β' - γ' * δ') * (t₁ * t₂ * (t₂ - t₁)) = 0 := by
    linear_combination t₁ * e₂ - t₂ * e₁ + (t₂ - t₁) * e₀
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mul_ne_zero (mul_ne_zero h₁ h₂) (sub_ne_zero.mpr h₁₂.symm))

theorem FramesCover.eq_smul_one {E : Type} [Field E] {r : ℕ} (hr : 0 < r) (τ₁ : E →+* ℂ)
    (W : Matrix (Fin r) (Fin r) E)
    (h : ∀ (ξ : Fin r → ℂ) (a b : Fin r), (∑ i, ξ i * τ₁ (W i a)) * ξ b = (∑ i, ξ i * τ₁ (W i b)) * ξ a) :
    W = W ⟨0, hr⟩ ⟨0, hr⟩ • (1 : Matrix (Fin r) (Fin r) E) := by
  have hoff : ∀ c a, c ≠ a → W c a = 0 := by
    intro c a hca
    have e := h (Pi.single c 1) a c
    simp [Pi.single_apply, hca] at e
    exact τ₁.injective (by simpa using e)
  have hdiag : ∀ a b, W a a = W b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    have e := h (Pi.single a 1 + Pi.single b 1) a b
    simp [Pi.single_apply, hab, Ne.symm hab, Finset.sum_add_distrib, add_mul, ite_mul] at e
    simp [hoff a b hab, hoff b a (Ne.symm hab)] at e
    exact τ₁.injective (by simpa using e)
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [hdiag i ⟨0, hr⟩]
  · simp [hoff i j hij, hij]

theorem FramesCover.coord_of_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (τ₁ : E →+* ℂ) (W : Matrix (Fin r) (Fin r) E) (y : Fin r → ℂ)
    (h : ∀ v ∈ X.Λ, ∀ w ∈ X.Λ, (y ⬝ᵥ Data.emb τ₁ (W *ᵥ v)) * (y ⬝ᵥ Data.emb τ₁ w) =
      (y ⬝ᵥ Data.emb τ₁ (W *ᵥ w)) * (y ⬝ᵥ Data.emb τ₁ v)) (a b : Fin r) :
    (∑ i, y i * τ₁ (W i a)) * y b = (∑ i, y i * τ₁ (W i b)) * y a := by
  have hadd : ∀ v w : Fin r → E, Data.emb τ₁ (v + w) = Data.emb τ₁ v + Data.emb τ₁ w := fun v w => by
    funext i; simp [Data.emb]
  have hsmul : ∀ (c : E) (v : Fin r → E), Data.emb τ₁ (c • v) = τ₁ c • Data.emb τ₁ v := fun c v => by
    funext i; simp [Data.emb]
  have hzero : Data.emb τ₁ (0 : Fin r → E) = 0 := by funext i; simp [Data.emb]
  let P : (Fin r → E) → (Fin r → E) → Prop := fun v w =>
    (y ⬝ᵥ Data.emb τ₁ (W *ᵥ v)) * (y ⬝ᵥ Data.emb τ₁ w) = (y ⬝ᵥ Data.emb τ₁ (W *ᵥ w)) * (y ⬝ᵥ Data.emb τ₁ v)
  have hspan : ∀ u : Fin r → E, u ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := fun u => by
    rw [X.Λ_span]; trivial
  have h1 : ∀ v, ∀ w ∈ X.Λ, P v w := by
    intro v w hw
    induction hspan v using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [P, hzero]
    | add x x' _ _ hx hx' =>
      simp only [P, mulVec_add, hadd, dotProduct_add] at hx hx' ⊢
      linear_combination hx + hx'
    | smul c x _ hx =>
      simp only [P, mulVec_smul, hsmul, dotProduct_smul, smul_eq_mul] at hx ⊢
      linear_combination τ₁ c * hx
  have h2 : ∀ v w, P v w := by
    intro v w
    induction hspan w using Submodule.span_induction with
    | mem x hx => exact h1 v x hx
    | zero => simp [P, hzero]
    | add x x' _ _ hx hx' =>
      simp only [P, mulVec_add, hadd, dotProduct_add] at hx hx' ⊢
      linear_combination hx + hx'
    | smul c x _ hx =>
      simp only [P, mulVec_smul, hsmul, dotProduct_smul, smul_eq_mul] at hx ⊢
      linear_combination τ₁ c * hx
  have e := h2 (Pi.single a 1) (Pi.single b 1)
  have hs : ∀ c, y ⬝ᵥ Data.emb τ₁ (W *ᵥ Pi.single c 1) = ∑ i, y i * τ₁ (W i c) := fun c => by
    simp [dotProduct, Data.emb, mulVec_single_one]
  have ht : ∀ c, y ⬝ᵥ Data.emb τ₁ (Pi.single c 1) = y c := fun c => by
    simp [dotProduct, Data.emb, Pi.single_apply]
  simpa only [P, hs, ht] using e

end GlobalTheory

namespace GlobalTheory

open Set Filter Topology

theorem FramesCover.exists_scalar_mem :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (hr : 0 < r) (τ₁ : E →+* ℂ)
      (κ : Frame X.Ψ r → Fin r → ℂ), ContinuousOn κ X.dom →
      (∀ O : Set (Frame X.Ψ r), IsOpen O → O ⊆ X.dom → ∀ x ∈ O, ∀ ξ : Fin r → ℂ,
        ∀ᶠ t in nhdsWithin (0 : ℂ) {0}ᶜ, ∃ x' ∈ O, κ x' = κ x + t • ξ) →
      ∀ (S : Set (Matrix (Fin r) (Fin r) E)),
        (∀ x ∈ X.dom, ∃ W ∈ S, ∀ v ∈ X.Λ, ∀ w ∈ X.Λ,
          (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ v)) * (κ x ⬝ᵥ Data.emb τ₁ w) =
            (κ x ⬝ᵥ Data.emb τ₁ (W *ᵥ w)) * (κ x ⬝ᵥ Data.emb τ₁ v)) →
        ∃ W ∈ S, ∃ ζ : E, W = ζ • (1 : Matrix (Fin r) (Fin r) E) := by
  intro E _ _ _ r X hr τ₁ κ hκ hmove S hS
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have hO : IsOpen X.dom := FourierCoefficientDomain.isOpen_dom X
  haveI : BaireSpace X.dom := hO.baireSpace
  haveI : Nonempty X.dom :=
    ⟨⟨_, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom X _ (fun τ => (X.signature τ).choose_spec.2)⟩⟩
  have hκc : Continuous fun x : X.dom => κ x := hκ.restrict
  let C : S → Set X.dom := fun W => ⋂ v ∈ (X.Λ : Set (Fin r → E)), ⋂ w ∈ (X.Λ : Set (Fin r → E)),
    {x : X.dom | (κ x ⬝ᵥ Data.emb τ₁ ((W : Matrix (Fin r) (Fin r) E) *ᵥ v)) * (κ x ⬝ᵥ Data.emb τ₁ w) =
      (κ x ⬝ᵥ Data.emb τ₁ ((W : Matrix (Fin r) (Fin r) E) *ᵥ w)) * (κ x ⬝ᵥ Data.emb τ₁ v)}
  have hcl : ∀ W, IsClosed (C W) := fun W =>
    isClosed_biInter fun v _ => isClosed_biInter fun w _ =>
      isClosed_eq ((hκc.dotProduct continuous_const).mul (hκc.dotProduct continuous_const))
        ((hκc.dotProduct continuous_const).mul (hκc.dotProduct continuous_const))
  have hcov : ⋃ W, C W = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨W, hW, hx⟩ := hS x x.2
    refine mem_iUnion.mpr ⟨⟨W, hW⟩, ?_⟩
    simp only [C, mem_iInter, mem_setOf_eq]
    exact fun v hv w hw => hx v hv w hw
  obtain ⟨W, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  set O : Set (Frame X.Ψ r) := Subtype.val '' interior (C W) with hOdef
  have hOo : IsOpen O := hO.isOpenMap_subtype_val _ isOpen_interior
  have hOs : O ⊆ X.dom := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hxO : (x : Frame X.Ψ r) ∈ O := ⟨x, hx, rfl⟩
  have key : ∀ y ∈ O, ∀ a b : Fin r, (∑ i, κ y i * τ₁ ((W : Matrix (Fin r) (Fin r) E) i a)) * κ y b =
      (∑ i, κ y i * τ₁ ((W : Matrix (Fin r) (Fin r) E) i b)) * κ y a := by
    rintro _ ⟨y, hy, rfl⟩ a b
    have hy' := interior_subset hy
    simp only [C, mem_iInter, mem_setOf_eq] at hy'
    exact FramesCover.coord_of_lattice X τ₁ W (κ y) hy' a b
  have hlin : ∀ (u ξ : Fin r → ℂ) (t : ℂ) (c : Fin r → ℂ),
      ∑ i, (u + t • ξ) i * c i = (∑ i, u i * c i) + t * ∑ i, ξ i * c i := by
    intro u ξ t c
    simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hall : ∀ (ξ : Fin r → ℂ) (a b : Fin r),
      (∑ i, ξ i * τ₁ ((W : Matrix (Fin r) (Fin r) E) i a)) * ξ b =
        (∑ i, ξ i * τ₁ ((W : Matrix (Fin r) (Fin r) E) i b)) * ξ a := by
    intro ξ a b
    have hev := (hmove O hOo hOs x hxO ξ).and self_mem_nhdsWithin
    obtain ⟨t₁, ⟨y₁, hy₁, e₁⟩, ht₁⟩ := hev.exists
    have ht₁' : t₁ ≠ 0 := ht₁
    obtain ⟨t₂, ⟨⟨y₂, hy₂, e₂⟩, ht₂⟩, ht₁₂⟩ :=
      (hev.and (nhdsWithin_le_nhds (eventually_ne_nhds ht₁'.symm))).exists
    have ht₂' : t₂ ≠ 0 := ht₂
    have k₀ := key x hxO a b
    have k₁ := key y₁ hy₁ a b
    have k₂ := key y₂ hy₂ a b
    rw [e₁, hlin, hlin] at k₁
    rw [e₂, hlin, hlin] at k₂
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at k₁ k₂
    exact FramesCover.lead_eq_zero ht₁' ht₂' (Ne.symm ht₁₂) k₀ k₁ k₂
  exact ⟨W, W.2, _, FramesCover.eq_smul_one hr τ₁ W hall⟩

end GlobalTheory
