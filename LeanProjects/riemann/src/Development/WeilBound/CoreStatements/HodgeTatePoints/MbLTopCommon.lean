import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.GenfibMap
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLFlatten
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinMany
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLNormExists
import Development.WeilBound.CoreStatements.HodgeTatePoints.MbLPullEq

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LTopCommon

theorem exists_common_normal_model : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ _ Ω _ _ κ _ x M A _ κa _ w B _ E _ _ L V _ hw hL hV
  choose κb hκb v hv0 hv1 hv2 using fun b => PositivityTheory.HtPt.Mb.flatten o Ω κ x M (E b) (L b) (V b) (hL b) (hV b)
  let κs : A ⊕ B → Type := fun s => match s with
    | .inl a => κa a
    | .inr b => κb b
  let ws : ∀ s, κs s → Ω := fun s => match s with
    | .inl a => w a
    | .inr b => v b
  haveI : ∀ s, Finite (κs s) := fun s => match s with
    | .inl a => inferInstanceAs (Finite (κa a))
    | .inr b => hκb b
  have hws : ∀ s, ∃ l, ws s l ≠ 0 := fun s => match s with
    | .inl a => hw a
    | .inr b => hv0 b
  obtain ⟨κ₁, _, y₁, M₁, f, hf, hch, hiso⟩ := PositivityTheory.HtPt.Mb.join_many o Ω κ x M (A ⊕ B) κs ws hws
  obtain ⟨κ₂, hκ₂, y₂, M₂, g, hg, hN, -, hnorm⟩ := PositivityTheory.HtPt.Mb.norm_exists o Ω κ₁ y₁ M₁ Ω
  replace hg : Dominates M₂.ξ M₁.ξ g (RingHom.id Ω) := hg
  replace hnorm : ∀ p, NormAt M₂.ξ g (RingHom.id Ω) p := hnorm
  have hgf : Dominates M₂.ξ M.ξ (g ≫ f) (RingHom.id Ω) := by
    unfold Dominates at *
    rw [← Category.assoc, hg, Category.assoc, hf]
    simp
  have hch₂ : ∀ s (p' : Cpt M₂.ξ), ∃ l, InChart M₂.ξ (ws s) l p' := by
    intro s p'
    obtain ⟨h, h1, -⟩ := PositivityTheory.HtPt.Mb.dom_local _ Ω M₁.ξ _ Ω M₂.ξ _ g hg p'
    obtain ⟨l, hl⟩ := hch s ⟨_, h⟩
    exact ⟨l, hl.1, fun c => h1 _ (hl.2 c)⟩
  refine ⟨κ₂, hκ₂, y₂, M₂, g ≫ f, hgf, hN, fun a => hch₂ (.inl a), fun b => ?_, fun p hp hfr => ?_⟩
  · obtain ⟨e, hc⟩ := PositivityTheory.HtPt.Mb.pull_eq o Ω κ x M (E b) (L b) _ Ω M₂.ξ _ (E b) (AddMonoidHom.id _) (g ≫ f) (hL b) hgf
    have key := hv2 b _ Ω M₂.ξ (RingHom.id Ω) (E b) (AddMonoidHom.id _) ⟨fun _ _ => rfl, fun _ _ h => h⟩
    have hu : {p' | p' ∈ ctrSet o x (RingHom.id Ω) M₂.ξ ∧ ∃ l, InChart M₂.ξ (fun l => RingHom.id Ω (v b l)) l p'}
        = Set.univ := Set.eq_univ_of_forall fun p' => ⟨hc p', hch₂ (.inr b) p'⟩
    have hs : Submodule.span Ω (AddMonoidHom.id (E b) '' (V b : Set (E b))) = V b := by simp
    rw [hu, hs] at key
    rw [e]
    exact key
  · refine (PositivityTheory.HtPt.Mb.iso_comp _ Ω M.ξ _ _ Ω (RingHom.id Ω) p).1 M₁.ξ M₂.ξ f g hg (hiso p ?_) fun p₁ _ => hnorm p₁
    rintro (a | b)
    · exact hp a
    · exact hv1 b p (hfr b)

end PositivityTheory.HtPt.Mb.LTopCommon

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.top_common : ∀ (o : Type) [CommRing o] [Algebra.EssFiniteType ℤ o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (A : Type) [Finite A] (κa : A → Type) [∀ a, Finite (κa a)] (w : ∀ a, κa a → Ω) (B : Type) [Finite B] (E : B → Type) [∀ b, AddCommGroup (E b)] [∀ b, Module Ω (E b)] (L : ∀ b, Lat M.ξ (E b)) (V : ∀ b, Submodule Ω (E b)) [∀ b, FiniteDimensional Ω (V b)], (∀ a, ∃ l, w a l ≠ 0) → (∀ b, (L b).IsCohOn Set.univ) → (∀ b p, Submodule.span Ω (L b p : Set (E b)) = V b) → ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel o y) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ a (p' : Cpt M'.ξ), ∃ l, InChart M'.ξ (w a) l p') ∧ (∀ b, ((L b).pull M'.ξ f (AddMonoidHom.id (E b))).IsVB (Module.finrank Ω (V b)) (V b)) ∧ ∀ p : Cpt M.ξ, (∀ a, ∃ l, InChart M.ξ (w a) l p) → (∀ b, ∃ (r : ℕ) (g : Fin r → E b), (L b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LTopCommon.exists_common_normal_model
