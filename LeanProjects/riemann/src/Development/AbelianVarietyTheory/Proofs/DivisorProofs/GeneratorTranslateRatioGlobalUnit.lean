import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeMonHomSquareLiftOneRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem gen_transl_ratio : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB →
    ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
        r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
        gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  intro X X' π Q₁ Q₂ hQ₁ hQ₂ w hw τ hτ
  have hπτ : ∀ x : X, π (τ x) = π x := fun x => by
    rw [← Scheme.Hom.comp_apply, hτ]
  have hmem : ∀ {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)},
      x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → τ x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
    intro x k hx
    rw [mem_divPull] at hx ⊢
    rw [hπτ]; exact hx
  have hle : ∀ k, (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ τ ⁻¹ᵁ (LB.div (Q₂.pull π) (Q₁.pull π)).U k :=
    fun k x hx => hmem hx
  let u : ∀ k, Γ(X, (LB.div (Q₂.pull π) (Q₁.pull π)).U k)ˣ := fun k =>
    res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm r z _ (u k) = gm (r ≫ τ) z _ (w.s k) * (gm r z _ (w.s k))⁻¹ := by
    intro Z r z k hz
    show gm r z _ (res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹) = _
    rw [map_mul, map_inv, gm_res r z (hle k) hz, gm_pull r τ z _ (hmem hz)]
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k l, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U l →
      gm (r ≫ τ) z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) = gm r z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) := by
    intro Z r z k l hk hl
    have hk' := hmem hk
    have hl' := hmem hl
    rw [germ_div_g _ _ (r ≫ τ) z hk' hl', germ_div_g _ _ r z hk hl]
    have hk₀ := mem_divPull.1 hk
    have hl₀ := mem_divPull.1 hl
    have hk₁ := mem_divPull.1 hk'
    have hl₁ := mem_divPull.1 hl'
    rw [gm_pull_g Q₂ π (r ≫ τ) z hk₁.1 hl₁.1, gm_pull_g Q₁ π (r ≫ τ) z hk₁.2 hl₁.2,
      gm_pull_g Q₂ π r z hk₀.1 hl₀.1, gm_pull_g Q₁ π r z hk₀.2 hl₀.2, Category.assoc, hτ]
  have hc : (⊤ : X.Opens) ≤ iSup (LB.div (Q₂.pull π) (Q₁.pull π)).U := by
    intro x _
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, fun _ => j), mem_divPull.2 ⟨hi, hj⟩⟩
  obtain ⟨f, hf⟩ := glue_unit (⊤ : X.Opens) (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => le_top) hc u (by
    intro k l x hx
    rw [hu _ _ _ k hx.1, hu _ _ _ l hx.2, gen_germ hw (𝟙 X ≫ τ) x (hmem hx.1) (hmem hx.2),
      gen_germ hw (𝟙 X) x hx.1 hx.2, hg _ _ _ k l hx.1 hx.2]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _)
  refine ⟨f, fun Z r z k hz => ?_⟩
  rw [← gm_res r z (le_top : (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ ⊤) hz f, hf k, hu Z r z k hz,
    inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
