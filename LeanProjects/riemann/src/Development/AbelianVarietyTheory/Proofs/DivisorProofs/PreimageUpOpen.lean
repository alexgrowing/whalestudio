import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

section One
variable {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]

theorem isHomeomorph : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

def upOpen (U : Y₀.Opens) : Y₁.Opens := ⟨i '' (U : Set Y₀), (isHomeomorph i).isOpenMap _ U.2⟩

theorem preimage_upOpen (U : Y₀.Opens) : i ⁻¹ᵁ upOpen i U = U := by
  ext x
  change i x ∈ i '' (U : Set Y₀) ↔ x ∈ U
  exact (isHomeomorph i).injective.mem_set_image

theorem upOpen_preimage (V : Y₁.Opens) : upOpen i (i ⁻¹ᵁ V) = V := by
  ext y
  change y ∈ i '' (i ⁻¹' (V : Set Y₁)) ↔ y ∈ V
  rw [Set.image_preimage_eq _ i.surjective]
  rfl

theorem upOpen_mono : Monotone (upOpen i) := fun _ _ h ↦ Set.image_mono h

abbrev upFun : Y₀.Opens ⥤ Y₁.Opens := (upOpen_mono i).functor

def res (U : Y₀.Opens) : Γ(Y₁, upOpen i U) ⟶ Γ(Y₀, U) :=
  i.appLE (upOpen i U) U (preimage_upOpen i U).ge

theorem res_naturality {U V : Y₀.Opens} (h : U ≤ V) :
    Y₁.presheaf.map (homOfLE (upOpen_mono i h)).op ≫ res i U =
      res i V ≫ Y₀.presheaf.map (homOfLE h).op := by
  simp only [res, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end One

section Two
variable {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁]
  [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂]

abbrev cone (U : Y₀.Opens) : PullbackCone (res i₁ U) (res i₂ U) :=
  CommRingCat.pullbackCone (res i₁ U) (res i₂ U)

def coneIsLimit (U : Y₀.Opens) : IsLimit (cone i₁ i₂ U) :=
  CommRingCat.pullbackConeIsLimit _ _

def fibMap {U V : Y₀.Opens} (h : U ≤ V) : (cone i₁ i₂ V).pt ⟶ (cone i₁ i₂ U).pt :=
  PullbackCone.IsLimit.lift (coneIsLimit i₁ i₂ U)
    ((cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op)
    ((cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op)
    (by rw [Category.assoc, Category.assoc, res_naturality i₁ h, res_naturality i₂ h,
      (cone i₁ i₂ V).condition_assoc])

@[reassoc (attr := simp)]
theorem fibMap_fst {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).fst =
    (cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibMap_snd {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).snd =
    (cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

def fib : Y₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := (cone i₁ i₂ U.unop).pt
  map f := fibMap i₁ i₂ f.unop.le
  map_id U := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ U.unop)
    (by simp [homOfLE_refl]) (by simp [homOfLE_refl])
  map_comp f g := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ _)
    (by simp [← Functor.map_comp]; rfl) (by simp [← Functor.map_comp]; rfl)

def fibFst : fib i₁ i₂ ⟶ (upFun i₁).op ⋙ Y₁.presheaf where
  app U := (cone i₁ i₂ U.unop).fst
  naturality U V f := fibMap_fst i₁ i₂ f.unop.le

def fibSnd : fib i₁ i₂ ⟶ (upFun i₂).op ⋙ Y₂.presheaf where
  app U := (cone i₁ i₂ U.unop).snd
  naturality U V f := fibMap_snd i₁ i₂ f.unop.le

def fibπ : fib i₁ i₂ ⟶ Y₀.presheaf where
  app U := (cone i₁ i₂ U.unop).fst ≫ res i₁ U.unop
  naturality U V f := by
    change fibMap i₁ i₂ f.unop.le ≫ _ ≫ _ = _
    rw [fibMap_fst_assoc, res_naturality]
    rfl

def good : Set Y₀.Opens :=
  {U | IsAffineOpen U ∧ IsAffineOpen (upOpen i₁ U) ∧ IsAffineOpen (upOpen i₂ U)}

end Two

end GlobalTheory.FerrandPush
