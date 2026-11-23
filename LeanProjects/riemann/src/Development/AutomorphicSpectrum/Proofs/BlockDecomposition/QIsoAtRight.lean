import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.QCalc

section Linear

variable {R A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ C₂ : Type} [CommRing R]
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁] [Module R C₂]
  {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂}
  {c₀ : C₀ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] C₂}
  {f₀ : A₀ →ₗ[R] B₀} {f₁ : A₁ →ₗ[R] B₁} {f₂ : A₂ →ₗ[R] B₂}
  {g₀ : B₀ →ₗ[R] C₀} {g₁ : B₁ →ₗ[R] C₁} {g₂ : B₂ →ₗ[R] C₂} {k : A₁ →ₗ[R] C₁}

theorem qIsoAt_comp (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x)) (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hk : ∀ x, k x = g₁ (f₁ x)) (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) :
    QIsoAt a₀ a₁ c₀ c₁ k := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · have hc : b₁ (f₁ x) = 0 := by rw [← hf₂, hx, map_zero]
    exact hf.1 x hx (hg.1 (f₁ x) hc ⟨y, by rw [hy, hk]⟩)
  · obtain ⟨w, y, hw, hy⟩ := hg.2 z hz
    obtain ⟨x, y', hx, hy'⟩ := hf.2 w hw
    refine ⟨x, y + g₀ y', hx, ?_⟩
    have e : f₁ x = w + b₀ y' := by rw [← hy']; abel
    rw [hk, e, map_add, hg₀, map_add, ← hy]
    abel

theorem qIsoAt_right (hf₀ : ∀ x, f₁ (a₀ x) = b₀ (f₀ x)) (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hk : ∀ x, k x = g₁ (f₁ x))
    (hf : QIsoAt a₀ a₁ b₀ b₁ f₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt b₀ b₁ c₀ c₁ g₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨u, v, hu, hv⟩ := hf.2 x hx
    have e : f₁ u = x + b₀ v := by rw [← hv]; abel
    obtain ⟨w, hw⟩ := hK.1 u hu ⟨y + g₀ v, by rw [hk, e, map_add, map_add, hg₀, hy]⟩
    refine ⟨f₀ w - v, ?_⟩
    rw [map_sub, ← hf₀, hw, e]
    abel
  · obtain ⟨x, y, hx, hy⟩ := hK.2 z hz
    refine ⟨f₁ x, y, by rw [← hf₂, hx, map_zero], ?_⟩
    rw [← hk]
    exact hy

theorem qIsoAt_left (hf₂ : ∀ x, f₂ (a₁ x) = b₁ (f₁ x))
    (hg₀ : ∀ x, g₁ (b₀ x) = c₀ (g₀ x)) (hg₂ : ∀ x, g₂ (b₁ x) = c₁ (g₁ x))
    (hk : ∀ x, k x = g₁ (f₁ x))
    (hg : QIsoAt b₀ b₁ c₀ c₁ g₁) (hK : QIsoAt a₀ a₁ c₀ c₁ k) :
    QIsoAt a₀ a₁ b₀ b₁ f₁ := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · exact hK.1 x hx ⟨g₀ y, by rw [← hg₀, hy, hk]⟩
  · have hc : c₁ (g₁ z) = 0 := by rw [← hg₂, hz, map_zero]
    obtain ⟨x, y, hx, hy⟩ := hK.2 (g₁ z) hc
    have hd : b₁ (f₁ x - z) = 0 := by rw [map_sub, ← hf₂, hx, hz, map_zero, sub_zero]
    obtain ⟨y', hy'⟩ := hg.1 (f₁ x - z) hd ⟨y, by rw [map_sub, ← hk, hy]⟩
    exact ⟨x, y', hx, hy'.symm⟩

end Linear

theorem qCalcSt : CxSt → QCalcSt := by
  intro hCx R _ C _ F D E _ _ G H m n k hk
  have cm : ∀ i x, pulln m (i + 1) (dn F i x) = dn G i (pulln m i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R C F).2 D G m i) x
  have cn : ∀ i x, pulln n (i + 1) (dn G i x) = dn H i (pulln n i x) :=
    fun i x ↦ LinearMap.congr_fun ((hCx R D G).2 E H n i) x
  have zf : ∀ x : R, pulln m 0 ((0 : R →ₗ[R] Cn F 0) x) =
      (0 : R →ₗ[R] Cn G 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  have zg : ∀ x : R, pulln n 0 ((0 : R →ₗ[R] Cn G 0) x) =
      (0 : R →ₗ[R] Cn H 0) ((0 : R →ₗ[R] R) x) := fun x ↦ by simp
  refine ⟨fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩, fun h₁ h₂ ↦ ⟨?_, fun i ↦ ?_⟩⟩
  · exact qIsoAt_comp (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_comp (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_right zf (cm 0) zg (hk 0) h₁.1 h₂.1
  · exact qIsoAt_right (cm i) (cm (i + 1)) (cn i) (hk (i + 1)) (h₁.2 i) (h₂.2 i)
  · exact qIsoAt_left (cm 0) zg (cn 0) (hk 0) h₁.1 h₂.1
  · exact qIsoAt_left (cm (i + 1)) (cn i) (cn (i + 1)) (hk (i + 1)) (h₁.2 i) (h₂.2 i)

end GlobalTheory.CompanionTheory.QCalc
