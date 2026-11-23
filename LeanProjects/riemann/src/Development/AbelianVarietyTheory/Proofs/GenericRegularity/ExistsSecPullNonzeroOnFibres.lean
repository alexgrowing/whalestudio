import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in

theorem exists_sec_pull_nonzero_on_fibres :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (U : S.Opens), ⊤ ≤ f ⁻¹ᵁ U → ∀ θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ U), (∀ y ∈ U, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i)) → ∃ (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (θ' : LB.Sec t'.PP.L), IsRigIso m.cm t'.PP t.PP w ∧ (∀ (j : t.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j)) (h₂ : W ≤ (t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U k), (m.φ.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (θ'.f k)) ∧ ∀ y' : S', ∃ (g : t'.G.left) (i : t'.PP.L.ι), t'.G.hom g = y' ∧ g ∈ t'.G.left.basicOpen (θ'.f i) := by
  intro E _ _ _ H S S' t t' f m U hU θ₀ hθ₀ nz
  have mem : ∀ x, m.φ x ∈ t.G.hom ⁻¹ᵁ U := fun x => (congrArg (fun q => q x ∈ U) m.cart.1.w).mpr
    (hU (show t'.G.hom x ∈ (⊤ : S'.Opens) from trivial))
  have le : ∀ j, m.φ ⁻¹ᵁ t.PP.L.U j ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j) := fun j x hx => ⟨mem x, hx⟩
  have ev : ∀ y j, m.φ y ∈ t.PP.L.U j → gs (𝟙 _) y _ ((m.φ.appLE _ _ (le j)).hom (θ₀ j)) = gs m.φ y _ (θ₀ j) :=
    fun y j h => (gs_appLE m.φ _ _ (le j) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  obtain ⟨w, g1, r1, -⟩ := m.lin
  obtain ⟨θ, hθ⟩ := sec_down ((isGen_iff w).1 g1) t.PP.isLB t'.PP.isLB (fun j => (m.φ.appLE _ _ (le j)).hom (θ₀ j))
    fun y j j' h h' => by
      have hm : m.φ y ∈ t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j ⊓ t.PP.L.U j' := ⟨⟨mem y, h⟩, h'⟩
      have e := congrArg (gs m.φ y _) (hθ₀ j j')
      rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm,
        gs_unit _ y (t.PP.L.U j ⊓ t.PP.L.U j') ⟨h, h'⟩] at e
      exact (ev y j h).trans (e.trans (congrArg _ (ev y j' h').symm))
  refine ⟨w, θ, ⟨g1, r1⟩, fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun y' => ?_⟩
  · have e := hθ _ (𝟙 _) y j k (h₁ hy).2 (h₂ hy).2
    rw [ev y j (h₁ hy).2] at e
    rw [gs_appLE m.φ _ _ h₁ (𝟙 _) y hy, Category.id_comp, e, gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)).symm rfl
  · obtain ⟨g₀, i, hg₀, hb₀⟩ := nz (f y') (hU (show y' ∈ (⊤ : S'.Opens) from trivial))
    obtain ⟨g, hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 g₀ y' hg₀
    obtain rfl : m.φ g = g₀ := hg₁
    have hgi : m.φ g ∈ t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U i := t.G.left.basicOpen_le _ hb₀
    obtain ⟨k₀, hk₀⟩ := exists_chart t'.PP.isLB g
    have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
      have u₀ : IsUnit (gs (𝟙 _) (m.φ g) _ (θ₀ i)) := by
        rw [gs_eq (𝟙 _) (m.φ g) _ hgi]; exact (t.G.left.mem_basicOpen _ _ hgi).1 hb₀
      have u₁ : IsUnit (gs m.φ g _ (θ₀ i)) := by rw [gs_stalkMap m.φ g _ hgi]; exact u₀.map _
      rw [← ev g i hgi.2, hθ _ (𝟙 _) g i k₀ hgi.2 hk₀] at u₁
      exact isUnit_of_mul_isUnit_right u₁
    exact ⟨g, k₀, hg₂, (t'.G.left.mem_basicOpen _ _ hk₀).2 (by rwa [gs_eq _ _ _ hk₀] at un)⟩

end GlobalTheory
