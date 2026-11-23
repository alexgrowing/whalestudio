import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisCartDesc

theorem epi_of_isGaloisCover {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) : Epi π := by
  refine ⟨fun {Z} g₁ g₂ e ↦ ?_⟩
  obtain ⟨f', -, hu⟩ := h.existsUnique_desc (π ≫ g₁) (fun a ↦ by rw [← Category.assoc, h.inv])
  exact (hu g₁ rfl).trans (hu g₂ e.symm).symm

theorem epi_pullback_fst {X Y : Scheme.{0}} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {π : X ⟶ Y}
    (h : GlobalTheory.ZM.IsGaloisCover Ga ρ π) {T : Scheme.{0}} (t : T ⟶ Y) : Epi (pullback.fst t π) := by
  let ρ' : Ga → (pullback t π ⟶ pullback t π) := fun a ↦
    pullback.map t π t π (𝟙 _) (ρ a) (𝟙 _) (by simp) (by simp [h.inv])
  have hg : GlobalTheory.ZM.IsGaloisCover Ga ρ' (pullback.fst t π) :=
    h.of_isPullback (IsPullback.of_hasPullback t π).flip
      (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_snd])
      (fun a ↦ by simp only [ρ', pullback.map, pullback.lift_fst, Category.comp_id])
  exact epi_of_isGaloisCover hg

theorem isGrpPullback_of_galoisCover : ∀ (S S₁ Y : Scheme.{0}) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga] (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y)
    (A' : Over S₁) (A : Over S) (B : Over Y) [GrpObj A'] [GrpObj A] [GrpObj B] (φ₁ : A'.left ⟶ A.left)
    (ψ : A'.left ⟶ B.left) (φ : A.left ⟶ B.left), GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → IsGrpPullback A' A π₁ φ₁ →
    IsGrpPullback A' B (π₁ ≫ f) ψ → φ₁ ≫ φ = ψ → IsGrpPullback A B f φ := by
  intro S S₁ Y π₁ Ga _ ρ₁ f A' A B _ _ _ φ₁ ψ φ hG hφ₁ hψ hφ

  let τ : Ga → (A'.left ⟶ A'.left) := fun a ↦
    hφ₁.1.lift φ₁ (A'.hom ≫ ρ₁ a) (by rw [hφ₁.1.w, Category.assoc, hG.inv])
  have hτ₁ : ∀ a, τ a ≫ φ₁ = φ₁ := fun a ↦ hφ₁.1.lift_fst _ _ _
  have hτ₂ : ∀ a, τ a ≫ A'.hom = A'.hom ≫ ρ₁ a := fun a ↦ hφ₁.1.lift_snd _ _ _
  have gφ₁ : GlobalTheory.ZM.IsGaloisCover Ga τ φ₁ := hG.of_isPullback hφ₁.1.flip hτ₂ hτ₁
  have eφ₁ : Epi φ₁ := epi_of_isGaloisCover gφ₁

  have w : φ ≫ B.hom = A.hom ≫ f := by
    rw [← cancel_epi φ₁, reassoc_of% hφ, hψ.1.w, ← reassoc_of% hφ₁.1.w]

  let q : A'.left ⟶ pullback B.hom f := pullback.lift ψ (A'.hom ≫ π₁) (by rw [hψ.1.w, Category.assoc])
  have hq₁ : q ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd B.hom f = A'.hom ≫ π₁ := pullback.lift_snd _ _ _
  have hsq : IsPullback q A'.hom (pullback.snd B.hom f) π₁ := by
    refine IsPullback.of_right ?_ hq₂ (IsPullback.of_hasPullback B.hom f)
    rw [hq₁]
    exact hψ.1
  have hτq : ∀ a, τ a ≫ q = q := fun a ↦ by
    apply pullback.hom_ext
    · rw [Category.assoc, hq₁, ← hφ, reassoc_of% hτ₁ a]
    · rw [Category.assoc, hq₂, reassoc_of% hτ₂ a, hG.inv]
  have gq : GlobalTheory.ZM.IsGaloisCover Ga τ q := hG.of_isPullback hsq.flip hτ₂ hτq
  have eq : Epi q := epi_of_isGaloisCover gq
  obtain ⟨d, hd, -⟩ := gq.existsUnique_desc φ₁ hτ₁
  let c : A.left ⟶ pullback B.hom f := pullback.lift φ A.hom w
  have hc : φ₁ ≫ c = q := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc, hq₁]
      rw [pullback.lift_fst, hφ]
    · simp only [c, Category.assoc, hq₂]
      rw [pullback.lift_snd, hφ₁.1.w]
  have hcd : c ≫ d = 𝟙 _ := by rw [← cancel_epi φ₁, reassoc_of% hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 _ := by rw [← cancel_epi q, reassoc_of% hd, hc, Category.comp_id]
  let i : A.left ≅ pullback B.hom f := ⟨c, d, hcd, hdc⟩
  refine ⟨IsPullback.of_iso_pullback ⟨w⟩ i (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ?_⟩

  intro T x y x₀ y₀ hx hy
  let e : pullback T.hom π₁ ⟶ T.left := pullback.fst T.hom π₁
  have ee : Epi e := epi_pullback_fst hG T.hom
  let T₁ : Over S₁ := Over.mk (pullback.snd T.hom π₁)
  let j : Over.mk (T₁.hom ≫ π₁) ⟶ T := Over.homMk e (by simp [T₁, e, pullback.condition])
  let j' : Over.mk (T₁.hom ≫ π₁ ≫ f) ⟶ Over.mk (T.hom ≫ f) :=
    Over.homMk e (by simp [T₁, e, pullback.condition_assoc])
  have lift : ∀ z : T ⟶ A, ∃ z₁ : T₁ ⟶ A', z₁.left ≫ φ₁ = e ≫ z.left := fun z ↦
    ⟨Over.homMk (hφ₁.1.lift (e ≫ z.left) (pullback.snd T.hom π₁)
      (by simp [e, pullback.condition])) (hφ₁.1.lift_snd _ _ _), hφ₁.1.lift_fst _ _ _⟩
  obtain ⟨x₁, hx₁⟩ := lift x
  obtain ⟨y₁, hy₁⟩ := lift y
  have a₁ : ((j ≫ x) * (j ≫ y)).left = (x₁ * y₁).left ≫ φ₁ :=
    hφ₁.2 T₁ x₁ y₁ (j ≫ x) (j ≫ y) (by simp [j, hx₁]) (by simp [j, hy₁])
  have a₂ : ((j' ≫ x₀) * (j' ≫ y₀)).left = (x₁ * y₁).left ≫ ψ :=
    hψ.2 T₁ x₁ y₁ (j' ≫ x₀) (j' ≫ y₀) (by simp [j', hx, ← hφ, reassoc_of% hx₁])
      (by simp [j', hy, ← hφ, reassoc_of% hy₁])
  rw [← MonObj.comp_mul] at a₁ a₂
  rw [← cancel_epi e]
  have b₁ : e ≫ (x * y).left = (x₁ * y₁).left ≫ φ₁ := by simpa [j] using a₁
  have b₂ : e ≫ (x₀ * y₀).left = (x₁ * y₁).left ≫ ψ := by simpa [j'] using a₂
  rw [b₂, reassoc_of% b₁, hφ]

end GlobalTheory.GaloisCartDesc
