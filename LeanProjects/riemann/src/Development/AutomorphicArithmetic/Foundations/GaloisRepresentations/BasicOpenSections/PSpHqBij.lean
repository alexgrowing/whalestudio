import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Gal.Mod

private theorem pullHl_bijective (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ)
    (h : ∀ k : ℕ, Function.Bijective (pull _ f (tw (l ^ k) i) n)) :
    Function.Bijective (pullHl l f n i) := by
  constructor
  · intro x y hxy
    refine Subtype.ext (funext fun k => (h k).1 ?_)
    exact congrArg (fun z : Hl l E n i => z.1 k) hxy
  · intro y
    choose g hg using fun k => (h k).2 (y.1 k)
    refine ⟨⟨g, fun k => (h k).1 ?_⟩, Subtype.ext (funext hg)⟩
    refine (pull_red _ _ f n i (g (k + 1))).trans ?_
    refine (congrArg _ (hg (k + 1))).trans ?_
    exact (y.2 k).trans (hg k).symm

theorem spHqBij : ∀ (l : ℕ) [Fact l.Prime] {E E' : Spc} (f : E ⟶ E') (n i : ℤ),
    (∀ k : ℕ, Function.Bijective (pull _ f (tw (l ^ k) i) n)) →
      Function.Bijective (pullHQ l f n i) := by
  intro l _ E E' f n i h
  let e := LinearEquiv.ofBijective (pullHl l f n i) (pullHl_bijective l f n i h)
  have h1 : (pullHl l f n i) ∘ₗ (e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i) = LinearMap.id :=
    LinearMap.ext fun x => e.apply_symm_apply x
  have h2 : (e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i) ∘ₗ (pullHl l f n i) = LinearMap.id :=
    LinearMap.ext fun x => e.symm_apply_apply x
  have k1 : (pullHQ l f n i) ∘ₗ ((e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i).baseChange ℚ_[l]) = LinearMap.id := by
    unfold pullHQ
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have k2 : ((e.symm : Hl l E n i →ₗ[ℤ_[l]] Hl l E' n i).baseChange ℚ_[l]) ∘ₗ (pullHQ l f n i) = LinearMap.id := by
    unfold pullHQ
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  exact Function.bijective_iff_has_inverse.mpr
    ⟨_, fun x => LinearMap.congr_fun k2 x, fun x => LinearMap.congr_fun k1 x⟩

end UpperTheory.Gal.Mod
