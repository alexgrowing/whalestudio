import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.GalCarry

open Matrix GlobalTheory.GradedNorm

theorem qf_cast {m m' : ℕ} (h : m = m') (M : Matrix (Fin m') (Fin m') ℂ) (v : Fin m' → ℂ) :
    star (v ∘ Fin.cast h) ⬝ᵥ M.submatrix (Fin.cast h) (Fin.cast h) *ᵥ (v ∘ Fin.cast h) = star v ⬝ᵥ M *ᵥ v := by
  subst h; rfl

theorem qf_cast' {m m' : ℕ} (h : m = m') (M : Matrix (Fin m') (Fin m') ℂ) (v : Fin m → ℂ) :
    star v ⬝ᵥ M.submatrix (Fin.cast h) (Fin.cast h) *ᵥ v = star (v ∘ Fin.cast h.symm) ⬝ᵥ M *ᵥ (v ∘ Fin.cast h.symm) := by
  subst h; rfl

theorem mix_cast {m m' : ℕ} (h : m = m') (s : ℝ) (M₀ M : Matrix (Fin m') (Fin m') ℂ) :
    mix s (M₀.submatrix (Fin.cast h) (Fin.cast h)) (M.submatrix (Fin.cast h) (Fin.cast h)) =
      (mix s M₀ M).submatrix (Fin.cast h) (Fin.cast h) := by
  subst h; rfl

theorem mixDual_cast {m m' : ℕ} (h : m = m') (s : ℝ) (M₀ M : Matrix (Fin m') (Fin m') ℂ) :
    mixDual s (M₀.submatrix (Fin.cast h) (Fin.cast h)) (M.submatrix (Fin.cast h) (Fin.cast h)) =
      (mixDual s M₀ M).submatrix (Fin.cast h) (Fin.cast h) := by
  subst h; rfl

theorem metAt_eigMetAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (T : Tw s.T.Z) (x x' : ToroidalCompactificationData s), (∀ σ y, x'.r σ y = x.r σ (T.pt y)) → (∀ σ y, T.MetAt y (x.eigMet σ) (x'.eigMet σ)) → (∀ σ y, ¬ LiesIn y (genBd s.T.Z) → T.MetAt y (x.hodge σ) (x'.hodge σ)) → ∀ σ (R : Option ℝ) y, T.MetAt y (x.eigMetAt σ R) (x'.eigMetAt σ R) := by
  intro D A N j S κ s T x x' hr hmet hhodge
  have hli : ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ),
      LiesIn (T.pt y) (genBd s.T.Z) ↔ LiesIn y (genBd s.T.Z) := fun σ y => by
    have e : (T.pt y).1 (IsLocalRing.closedPoint ℂ) = T.g.hom (y.1 (IsLocalRing.closedPoint ℂ)) :=
      Scheme.Hom.comp_apply _ _ _
    unfold LiesIn
    rw [e]
    exact T.mem_genBd _
  have hsurj : ∀ (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ), ∃ y₀, T.pt y₀ = y := fun σ y =>
    ⟨⟨y.1 ≫ T.g.inv, by rw [Category.assoc, (Iso.inv_comp_eq _).2 T.g_str.symm, y.2]⟩,
      Subtype.ext (by simp [Tw.pt])⟩
  have hH : ∀ σ y, T.MetAt y (x.hodge σ) (x'.hodge σ) := fun σ y => by
    by_cases hy : LiesIn y (genBd s.T.Z)
    · intro f f' hp τ
      rw [x.hodge_gram_of_liesIn ((hli σ y).2 hy), x'.hodge_gram_of_liesIn hy]
      exact hmet σ y f f' hp τ
    · exact hhodge σ y hy
  have hmu : x'.IsMuExp = x.IsMuExp := by
    funext C
    refine propext ⟨fun ⟨h0, h⟩ => ⟨h0, fun σ y hy g τ v => ?_⟩, fun ⟨h0, h⟩ => ⟨h0, fun σ y hy g τ v => ?_⟩⟩
    · obtain ⟨y₀, rfl⟩ := hsurj σ y
      obtain ⟨f, hf⟩ := T.exists_pull (x := y₀.1 ≫ genι s.T.Z) g rfl (T.pt_ι y₀)
      have hy₀ : ¬ LiesIn y₀ (genBd s.T.Z) := by rwa [hli] at hy
      have e1 : x.gram (T.pt y₀) g τ = (x'.gram y₀ f (T.emb τ)).submatrix T.ix T.ix := hmet σ y₀ f g hf τ
      have e2 := hhodge σ y₀ hy₀ f g hf τ
      have q1 : star v ⬝ᵥ x.gram (T.pt y₀) g τ *ᵥ v = star (v ∘ Fin.cast (T.mult_emb τ).symm) ⬝ᵥ
          x'.gram y₀ f (T.emb τ) *ᵥ (v ∘ Fin.cast (T.mult_emb τ).symm) := by
        rw [e1]; exact qf_cast' _ _ _
      have q2 : star v ⬝ᵥ (x.hodge σ).gram (T.pt y₀) g τ *ᵥ v = star (v ∘ Fin.cast (T.mult_emb τ).symm) ⬝ᵥ
          (x'.hodge σ).gram y₀ f (T.emb τ) *ᵥ (v ∘ Fin.cast (T.mult_emb τ).symm) := by
        rw [e2]; exact qf_cast' _ _ _
      have := h σ y₀ hy₀ f (T.emb τ) (v ∘ Fin.cast (T.mult_emb τ).symm)
      rw [q1, q2, ← hr]
      exact this
    · obtain ⟨τ₀, rfl⟩ : ∃ τ₀, T.emb τ₀ = τ := T.embEquiv.surjective τ
      obtain ⟨g', hg'⟩ := T.exists_push (x' := (T.pt y).1 ≫ genι s.T.Z) g rfl (T.pt_ι y)
      have e1 : x.gram (T.pt y) g' τ₀ = (x'.gram y g (T.emb τ₀)).submatrix T.ix T.ix := hmet σ y g g' hg' τ₀
      have e2 := hhodge σ y hy g g' hg' τ₀
      have q1 : star (v ∘ Fin.cast (T.mult_emb τ₀)) ⬝ᵥ x.gram (T.pt y) g' τ₀ *ᵥ (v ∘ Fin.cast (T.mult_emb τ₀)) =
          star v ⬝ᵥ x'.gram y g (T.emb τ₀) *ᵥ v := by
        rw [e1]; exact qf_cast _ _ _
      have q2 : star (v ∘ Fin.cast (T.mult_emb τ₀)) ⬝ᵥ (x.hodge σ).gram (T.pt y) g' τ₀ *ᵥ
          (v ∘ Fin.cast (T.mult_emb τ₀)) = star v ⬝ᵥ (x'.hodge σ).gram y g (T.emb τ₀) *ᵥ v := by
        rw [e2]; exact qf_cast _ _ _
      have := h σ (T.pt y) (by rwa [hli]) g' τ₀ (v ∘ Fin.cast (T.mult_emb τ₀))
      rw [q1, q2, ← hr] at this
      exact this
  have hkap : x'.kap = x.kap := by
    unfold ToroidalCompactificationData.kap ToroidalCompactificationData.muExp
    rw [hmu]
  have hwt : ∀ σ (R : ℝ) y, x'.wt σ R y = x.wt σ R (T.pt y) := fun σ R y => by
    unfold ToroidalCompactificationData.wt
    rw [hkap, hr, hli]
  intro σ R y
  cases R with
  | none => exact hH σ y
  | some R =>
    intro f f' hp τ
    change (EigMet.interp (x.wt σ R) (x.wt_mem R) (x.eigMet σ) (x.hodge σ)).gram (T.pt y) f' τ =
      ((EigMet.interp (x'.wt σ R) (x'.wt_mem R) (x'.eigMet σ) (x'.hodge σ)).gram y f (T.emb τ)).submatrix T.ix T.ix
    simp only [EigMet.interp]
    rw [T.emb_rt, hwt, hmet σ y f f' hp τ, hH σ y f f' hp τ]
    split_ifs
    · exact mix_cast _ _ _ _
    · exact mixDual_cast _ _ _ _

end GlobalTheory.ShFam.GalCarry
