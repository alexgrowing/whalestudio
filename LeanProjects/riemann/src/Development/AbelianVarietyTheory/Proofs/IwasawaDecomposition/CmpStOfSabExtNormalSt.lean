import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal

namespace GlobalTheory.TorRef

theorem exists_sabMap_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m⟩⟩

theorem cmpSt_of_sabExtNormalSt : SabExtNormalSt → CmpSt := by
  intro hS E _ _ _ H D l Xo c O O' _ _ β β' Y Z ρ hρ hN
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  obtain ⟨t₀, ⟨n₁⟩⟩ := exists_sabMap_pull (genι Z) Z.t
  obtain ⟨t', ⟨n'⟩⟩ := exists_sabMap_pull (ρ ≫ genι Y) Y.t
  obtain ⟨a, ha⟩ := GlobalTheory.LevelCover.sab_cancel n₁ Z.m Z.jQ rfl
  obtain ⟨k, hk⟩ := GlobalTheory.LevelCover.sab_cancel Y.m0.toSABMap Z.m0.toSABMap (𝟙 _) (Category.id_comp _)
  obtain ⟨ky, hky⟩ := GlobalTheory.LevelCover.sab_comp k Y.m (e := Z.jQ ≫ ρ ≫ genι Y)
    (by rw [Category.id_comp, ← hρ, Category.assoc])
  obtain ⟨a', ha'⟩ := GlobalTheory.LevelCover.sab_cancel n' ky Z.jQ rfl
  have hdom : IsDominant Z.jQ := ⟨Z.jQ_dense⟩
  obtain ⟨b, hb⟩ := hS E H (gen Z) (Xo.XF c) Z.jQ hN Z.jQ_open hdom Z.oF.t t₀ t' a a' Z.oF.proper
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.LevelCover.sab_comp b n' (Category.id_comp _)
  refine ⟨t₀, n₁, n₂, fun T g g₁ g₂ h₁ h₂ h₃ h₄ => ?_⟩
  have hg : g = g₁ ≫ a.φ := by
    apply n₁.cart.1.hom_ext
    · rw [h₂, Category.assoc, ha]
    · rw [h₁, Category.assoc, a.cart.1.w]
  have hg₂ : g₁ ≫ k.φ = g₂ := by
    apply Y.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hk, h₃]
    · rw [Category.assoc, k.cart.1.w, Category.comp_id, h₄]
  rw [hn₂, hg]
  simp only [Category.assoc]
  rw [reassoc_of% hb, ha', hky, reassoc_of% hg₂]

end GlobalTheory.TorRef
