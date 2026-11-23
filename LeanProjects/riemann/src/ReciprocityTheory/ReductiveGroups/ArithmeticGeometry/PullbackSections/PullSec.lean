import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExistsFieldOfFf

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X))
  (ε : K → ℤ) (H : Y' ⟶ Y)

theorem wchart_pull_le' (e : ∀ k, H ≫ φ k = φ' k) (j : K → L.ι) :
    (LB.LinComb L φ' ε).U j ≤ H ⁻¹ᵁ (LB.LinComb L φ ε).U j := by
  intro p hp
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : p ∈ (φ' k).base ⁻¹' (L.U (j k) : Set X) := Set.mem_iInter.1 hp k
  rw [← e k] at h1
  simpa using h1

theorem map_prod_pullU (e : ∀ k, H ≫ φ k = φ' k) (U : K → X.Opens) (u : ∀ k, Γ(X, U k)ˣ) (V : Y.Opens)
    (V' : Y'.Opens) (hV : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (hV' : ∀ k, V' ≤ φ' k ⁻¹ᵁ U k) (hH : V' ≤ H ⁻¹ᵁ V) :
    Units.map (H.appLE V V' hH).hom.toMonoidHom (∏ k, (res (hV k) (pullU (φ k) (U k) (u k))) ^ ε k) =
      ∏ k, (res (hV' k) (pullU (φ' k) (U k) (u k))) ^ ε k := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  ext
  show (H.appLE V V' hH).hom (((φ k).appLE (U k) V (hV k)).hom (u k : Γ(X, U k))) =
    ((φ' k).appLE (U k) V' (hV' k)).hom (u k : Γ(X, U k))
  show ((φ k).appLE (U k) V (hV k) ≫ H.appLE V V' hH).hom (u k : Γ(X, U k)) = _
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr (e k) (U k) V' _ (hV' k)]

def pullSecF (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y', (LB.LinComb L φ' ε).U j) :=
  (H.appLE ((LB.LinComb L φ ε).U j) ((LB.LinComb L φ' ε).U j) (wchart_pull_le' L φ φ' ε H e j)).hom (s.f j)

set_option maxHeartbeats 1000000 in
theorem pullSecF_compat (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (i j : K → L.ι) :
    (Y'.presheaf.map (homOfLE (inf_le_left : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
        (LB.LinComb L φ' ε).U i)).op).hom (pullSecF L φ φ' ε H e s i) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) *
        (Y'.presheaf.map (homOfLE (inf_le_right : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
          (LB.LinComb L φ' ε).U j)).op).hom (pullSecF L φ φ' ε H e s j) := by
  have hW : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
      H ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) :=
    fun p hp => ⟨wchart_pull_le' L φ φ' ε H e i hp.1, wchart_pull_le' L φ φ' ε H e j hp.2⟩
  have hres : ∀ (k : K → L.ι) (hk : (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U k)
      (hk' : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤ (LB.LinComb L φ' ε).U k),
      (Y'.presheaf.map (homOfLE hk').op).hom (pullSecF L φ φ' ε H e s k) =
        (H.appLE _ _ hW).hom ((Y.presheaf.map (homOfLE hk).op).hom (s.f k)) := by
    intro k hk hk'
    show (H.appLE _ _ (wchart_pull_le' L φ φ' ε H e k) ≫ Y'.presheaf.map (homOfLE hk').op).hom (s.f k) =
      (Y.presheaf.map (homOfLE hk).op ≫ H.appLE _ _ hW).hom (s.f k)
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hu : Units.map (H.appLE _ _ hW).hom.toMonoidHom ((LB.LinComb L φ ε).g i j) = (LB.LinComb L φ' ε).g i j :=
    map_prod_pullU φ φ' ε H e (fun k => L.U (i k) ⊓ L.U (j k)) (fun k => L.g (i k) (j k)) _ _
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ' i k)) (inf_le_right.trans (LB.wchart_le L φ' j k))) hW
  have hg : (H.appLE _ _ hW).hom ((LB.LinComb L φ ε).g i j : Γ(Y, (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) :=
    congrArg Units.val hu
  rw [hres i inf_le_left inf_le_left, hres j inf_le_right inf_le_right, ← hg, ← map_mul]
  exact congrArg (H.appLE _ _ hW).hom (s.compat i j)

def pullSecLC (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb L φ' ε) where
  f := pullSecF L φ φ' ε H e s
  compat := pullSecF_compat L φ φ' ε H e s

end LC

theorem exists_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S}
    (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) :
    ∃ s' : LB.Sec (LPow A L a T'), IsPullSec A L a h hh s s' := by
  have e : ∀ _k : Fin 1, h.left ≫ (snd T A).left = (snd T' A).left := fun _ => by rw [← Over.comp_left, hh]
  exact ⟨pullSecLC L _ _ _ h.left e s, fun j => rfl⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
