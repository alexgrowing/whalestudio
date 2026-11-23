import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isUnit_gs_id_iff {X : Scheme.{0}} (z : X) (U : X.Opens) (h : z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) z U a) ↔ z ∈ X.basicOpen a := by
  rw [gs_eq (𝟙 X) z U h, X.mem_basicOpen a z h]
  rfl

theorem exists_frame_of_isUnit_on_fibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  intro X Y β hβ L hL V s hs y hy hu
  let N : X.Opens := ⨆ k, X.basicOpen (s k)
  have hN : ∀ z : X, β z = y → z ∈ N := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart hL z
    have hm : z ∈ β ⁻¹ᵁ V ⊓ L.U k := ⟨show β z ∈ V from hz ▸ hy, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_id_iff z _ hm _).1 (hu z k hz hk)⟩
  let V₀ : Y.Opens := ⟨(β '' (N : Set X)ᶜ)ᶜ, (hβ _ N.2.isClosed_compl).isOpen_compl⟩
  have hy₀ : y ∈ V₀ := by
    rintro ⟨p, hp, e⟩
    exact hp (hN p e)
  have hV₀ : ∀ p : X, β p ∈ V₀ → p ∈ N := by
    intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩
  have hle : ∀ k, β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k ≤ β ⁻¹ᵁ V ⊓ L.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have hunit : ∀ k, IsUnit ((X.presheaf.map (homOfLE (hle k)).op).hom (s k)) := by
    intro k
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV₀ z hz.1.2)
    have hm' : z ∈ β ⁻¹ᵁ V ⊓ L.U k' := X.basicOpen_le _ hk'
    have h1 : IsUnit (gs (𝟙 X) z _ (s k)) := by
      rw [hs z k k' hm'.1 hz.2 hm'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_id_iff z _ hm' _).2 hk')
    rw [← gs_res (𝟙 X) z (hle k) hz, gs_eq (𝟙 X) z _ hz] at h1
    exact h1
  have key : ∀ (f : X ⟶ X) (z : X) (k : L.ι), f z ∈ β ⁻¹ᵁ (V ⊓ V₀) → f z ∈ L.U k →
      (gm f z _ (hunit k).unit : X.presheaf.stalk z) = gs f z _ (s k) := by
    intro f z k h1 h2
    have hm : f z ∈ β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k := ⟨h1, h2⟩
    rw [← gs_unit f z _ hm, IsUnit.unit_spec, gs_res f z (hle k) hm]
  refine ⟨V ⊓ V₀, ⟨hy, hy₀⟩, inf_le_left, fun k => (hunit k).unit, ?_, ?_⟩
  · intro k k'
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz]
    apply Units.ext
    rw [Units.val_mul, key (𝟙 X) z k hz.1.1 hz.1.2, key (𝟙 X) z k' hz.2.1 hz.2.2]
    exact hs z k k' hz.1.1.1 hz.1.2 hz.2.2
  · intro f w hw z j k hz hfz hk hj
    apply Units.ext
    rw [Units.val_mul, key f z j hfz hj, key (𝟙 X) z k hz hk]
    exact hw z j k hz.1 hfz.1 hk hj

end GlobalTheory.Mum
