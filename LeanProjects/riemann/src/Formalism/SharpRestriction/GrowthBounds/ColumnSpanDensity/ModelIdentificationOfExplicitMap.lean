import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoLatLeTwoSp

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

def TiePsi : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    Function.Injective (PsiXY R.Kf m) ∧
    (∀ (P Q : ℕ) x, x ∈ twoSp R.Kf m P Q ↔ ∃ f ∈ PolAB R.Kf (m + 1) P Q, PsiXY R.Kf m f = x) ∧
    (∀ (a b : ℕ) y, y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) ↔
      ∃ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = y) ∧
    (∀ (a b : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) a b, deltaB R.Kf m (PsiXY R.Kf m f) = 0 →
      ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), f = hXY R.Kf (m + 1) * G) ∧
    ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ →
      ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ), ∀ f ∈ PolAB R.Kf (m + 1) P Q,
          PsiXY R.Kf m f ∈ twoLat R.O m P Q Λ ↔ f ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) y, y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f ∈ PolAB R.Kf (m + 1) a b, f ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            deltaB R.Kf m (PsiXY R.Kf m f) = y)

theorem model_identification_of_explicit_map (h : TiePsi) : TwoLetterModelIdentification := by
  intro p n' R m hm
  obtain ⟨hinj, hsp, hdw, hker, hlat⟩ := h p n' R m hm
  let e : ∀ P Q : ℕ, PolAB R.Kf (m + 1) P Q →ₗ[R.Kf] twoSp R.Kf m P Q := fun P Q =>
    ((PsiXY R.Kf m).toLinearMap.domRestrict (PolAB R.Kf (m + 1) P Q)).codRestrict (twoSp R.Kf m P Q)
      (fun f => (hsp P Q _).2 ⟨f.1, f.2, rfl⟩)
  have he : ∀ P Q, Function.Bijective (e P Q) := fun P Q => by
    refine ⟨fun f g hfg => Subtype.ext (hinj (congrArg Subtype.val hfg)), fun x => ?_⟩
    obtain ⟨f, hf, hfx⟩ := (hsp P Q x.1).1 x.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  let α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q := fun P Q =>
    (LinearEquiv.ofBijective (e P Q) (he P Q)).symm
  have hαe : ∀ P Q (x : twoSp R.Kf m P Q),
      PsiXY R.Kf m (α P Q x : PolXY R.Kf (m + 1)) = x := fun P Q x => by
    have h1 := (LinearEquiv.ofBijective (e P Q) (he P Q)).apply_symm_apply x
    exact congrArg Subtype.val h1
  let β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)) :=
    fun a b => (((deltaB R.Kf m).comp (PsiXY R.Kf m)).toLinearMap.domRestrict
      (PolAB R.Kf (m + 1) a b)).codRestrict _ (fun f => (hdw a b _).2 ⟨f.1, f.2, rfl⟩)
  have hβ : ∀ a b (f : PolAB R.Kf (m + 1) a b),
      (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = deltaB R.Kf m (PsiXY R.Kf m f) :=
    fun a b f => rfl
  have ha : ∀ i, deltaB R.Kf m (PsiXY R.Kf m (X (Sum.inl i))) = X (i, (0 : Fin (m + 1))) := by
    intro i
    simp only [PsiXY, aeval_X, Sum.elim_inl, deltaB, rename_X]
  have hc : ∀ i, deltaB R.Kf m (PsiXY R.Kf m (X (Sum.inr i))) = covY R.Kf m i := by
    intro i
    simp only [PsiXY, aeval_X, Sum.elim_inr, deltaB, rename_rename]
    rw [show (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id from rfl,
      rename_id, AlgHom.id_apply]
  have hh0 : deltaB R.Kf m (PsiXY R.Kf m (hXY R.Kf (m + 1))) = 0 := by
    simp only [hXY, map_sum, map_mul, ha, hc]
    exact sum_covY R.Kf m (by omega)
  refine ⟨α, β, ?_, ?_, ?_⟩
  · intro a b y
    obtain ⟨f, hf, hfy⟩ := (hdw a b y.1).1 y.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  · intro a b f
    constructor
    · intro h0
      have h1 : deltaB R.Kf m (PsiXY R.Kf m f) = 0 := by
        rw [← hβ]
        exact congrArg Subtype.val h0
      exact hker a b f.1 f.2 h1
    · rintro ⟨G, _, hfG⟩
      apply Subtype.ext
      rw [hβ, hfG, map_mul, map_mul, hh0, zero_mul]
      rfl
  · intro Λ hΛ
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    refine ⟨g', fun P Q x => ?_, fun a b y => ?_⟩
    · constructor
      · intro hx
        have hxs := twoLat_le_twoSp m P Q Λ hΛ x hx
        refine ⟨hxs, ?_⟩
        rw [← h1 P Q _ (α P Q ⟨x, hxs⟩).2, hαe]
        exact hx
      · rintro ⟨hxs, hl⟩
        have h3 := (h1 P Q _ (α P Q ⟨x, hxs⟩).2).2 hl
        rwa [hαe] at h3
    · rw [h2 a b y]
      constructor
      · rintro ⟨f, hf, hl, hfy⟩
        exact ⟨⟨f, hf⟩, hl, hfy⟩
      · rintro ⟨f, hl, hfy⟩
        exact ⟨f.1, f.2, hl, hfy⟩

end Formalism.MainNotions.flipOneThree.Pf

end
