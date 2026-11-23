import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusStableGoodOpenOfWeightUnits
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusCot

open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.Conormal GlobalTheory.SS.TorusSlice

def derOpen {S X Y : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} {π' : Y ⟶ S} {e' : S ⟶ Y} {F : S.Modules}
    (φ : Y ⟶ X) [IsOpenImmersion φ] (w : φ ≫ π = π') (we : e' ≫ φ = e) (D : Der π e F) : Der π' e' F :=
  have hle : ∀ {W : Y.Opens} {V : S.Opens}, V ≤ e' ⁻¹ᵁ W → V ≤ e ⁻¹ᵁ (φ ''ᵁ W) := fun {W V} h =>
    (le_preimage_of_comp we).1 (by rwa [φ.preimage_image_eq])
  have hinj : ∀ W : Y.Opens, Function.Injective (φ.appLE (φ ''ᵁ W) W (φ.preimage_image_eq W).ge) := fun W => by
    rw [← Scheme.Hom.appIso_hom']
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hinv : ∀ (W : Y.Opens) (a : Γ(Y, W)),
      φ.appLE (φ ''ᵁ W) W (φ.preimage_image_eq W).ge ((φ.appIso W).inv a) = a := fun W a => by
    rw [← Scheme.Hom.appIso_hom']
    exact congrArg (fun ψ => ψ.hom a) (φ.appIso W).inv_hom_id
  { app {W V} h := (D.app (hle h)).comp (φ.appIso W).inv.hom.toAddMonoidHom
    res_app h h' f := D.res_app _ h' _
    app_res {W W' V} h k f := by
      refine (congrArg (D.app _) (hinj W' ?_)).trans (D.app_res _ (φ.image_mono k) _)
      refine (hinv _ _).trans ?_
      rw [appLE_resG, ← resG_appLE φ k (φ.preimage_image_eq W).ge]
      exact congrArg _ (hinv _ _).symm
    app_mul {W V} h f g := by
      refine (congrArg (D.app _) (map_mul (φ.appIso W).inv.hom f g)).trans ((D.app_mul _ _ _).trans ?_)
      rw [← appLE_appLE we (φ.preimage_image_eq W).ge h, ← appLE_appLE we (φ.preimage_image_eq W).ge h]
      erw [hinv, hinv]
      rfl
    app_base {W V U} h k a := by
      have k' : φ ''ᵁ W ≤ π ⁻¹ᵁ U :=
        (φ.image_mono ((le_preimage_of_comp w).2 k)).trans (φ.image_preimage_le _)
      refine (congrArg (D.app _) (hinj W ?_)).trans (D.app_base _ k' a)
      exact (hinv _ _).trans (appLE_appLE w _ _ _ a).symm }

theorem isFrame_append {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : IsFrame e₁) (he₂ : IsFrame e₂) :
    IsFrame (Fin.append (fun i => p₁.app U (e₁ i)) fun j => p₂.app U (e₂ j)) := by
  let ψ (V : S.Opens) : (Γ(F₁, V) × Γ(F₂, V)) ≃ₗ[Γ(S, V)] Γ(F, V) :=
    LinearEquiv.ofBijective ((QCoh.appLinear p₁ V).coprod (QCoh.appLinear p₂ V)) ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ hab
      change p₁.app V a + p₂.app V b = 0 at hab
      have a₁ := congrArg (i₁.app V) hab
      have a₂ := congrArg (i₂.app V) hab
      rw [map_add, map_zero, QCoh.app_app, QCoh.app_app] at a₁ a₂
      rw [h₁, h₄] at a₁
      rw [h₃, h₂] at a₂
      ext
      · simpa using a₁
      · simpa using a₂, fun c => ⟨(i₁.app V c, i₂.app V c), congr(($h).app V c)⟩⟩
  refine isFrame_of_basis (fun V k => (((he₁.basis k).prod (he₂.basis k)).map (ψ V)).reindex finSumFinEquiv)
    fun V k i => ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.map_apply]
  rcases i with i | i
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]
  · change p₁.app V _ + p₂.app V _ = _
    simp [app_resM]

section Geo

variable {S : Scheme.{0}} {T G B Y : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
  [IsMonHom u] {j : Y ⟶ G} {σ : Y ⟶ T}

end Geo

end GlobalTheory.TorusCot

namespace GlobalTheory.TorusPart

open GlobalTheory.TorusCot GlobalTheory.QCoh

end GlobalTheory.TorusPart
