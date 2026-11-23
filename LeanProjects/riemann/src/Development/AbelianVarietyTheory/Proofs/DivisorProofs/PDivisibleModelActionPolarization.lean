import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

def liftPt {R K : Type} [CommRing R] [Field K] [Algebra R K] {G : Over (Sp R)} {G₀ : Over (Sp K)}
    {F : G₀.left ⟶ G.left} (hF : F ≫ G.hom = G₀.hom ≫ spMap (algebraMap R K)) {B : Type} [CommRing B] [Algebra R B]
    [Algebra K B] [IsScalarTower R K B] (x : SpAlg K B ⟶ G₀) : SpAlg R B ⟶ G :=
  Over.homMk (x.left ≫ F) (by
    change (x.left ≫ F) ≫ G.hom = spMap (algebraMap R B)
    rw [Category.assoc, hF, ← Category.assoc, Over.w x]
    change spMap (algebraMap K B) ≫ spMap (algebraMap R K) = _
    rw [← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])

@[simp] theorem liftPt_left {R K : Type} [CommRing R] [Field K] [Algebra R K] {G : Over (Sp R)} {G₀ : Over (Sp K)}
    {F : G₀.left ⟶ G.left} (hF : F ≫ G.hom = G₀.hom ≫ spMap (algebraMap R K)) {B : Type} [CommRing B] [Algebra R B]
    [Algebra K B] [IsScalarTower R K B] (x : SpAlg K B ⟶ G₀) : (liftPt hF x).left = x.left ≫ F := rfl

section Lift

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {G : Over (Sp R)} [GrpObj G] {G₀ : Over (Sp K)} [GrpObj G₀]
  {F : G₀.left ⟶ G.left} (hF : IsGrpPullback G₀ G (spMap (algebraMap R K)) F) {B : Type} [CommRing B] [Algebra R B]
  [Algebra K B] [IsScalarTower R K B]

theorem liftPt_mul (x y : SpAlg K B ⟶ G₀) :
    liftPt hF.1.w (x * y) = liftPt hF.1.w x * liftPt hF.1.w y := by
  let j : Over.mk ((SpAlg K B).hom ≫ spMap (algebraMap R K)) ⟶ SpAlg R B :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ spMap (algebraMap R B) = spMap (algebraMap K B) ≫ spMap (algebraMap R K)
      rw [Category.id_comp, ← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq])
  have h := hF.2 (SpAlg K B) x y (j ≫ liftPt hF.1.w x) (j ≫ liftPt hF.1.w y) rfl rfl
  rw [← MonObj.comp_mul] at h
  refine Over.OverMorphism.ext ?_
  rw [liftPt_left]
  exact h.symm.trans (by simp [j])

theorem liftPt_one : liftPt hF.1.w (1 : SpAlg K B ⟶ G₀) = 1 := by
  have h := liftPt_mul hF (1 : SpAlg K B ⟶ G₀) 1
  rw [_root_.mul_one] at h
  exact (mul_eq_left.1 h.symm)

theorem liftPt_pow (x : SpAlg K B ⟶ G₀) (N : ℕ) : liftPt hF.1.w (x ^ N) = liftPt hF.1.w x ^ N := by
  induction N with
  | zero => simpa using liftPt_one hF
  | succ N ih => rw [pow_succ, liftPt_mul hF, ih, pow_succ]

def liftTors {N : ℕ} (z : Tors G₀ N B) : Tors G N B :=
  ⟨liftPt hF.1.w z.1, by rw [← liftPt_pow hF, z.2, liftPt_one hF]⟩

@[simp] theorem liftTors_left {N : ℕ} (z : Tors G₀ N B) : (liftTors hF z).1.left = z.1.left ≫ F := rfl

end Lift

end GlobalTheory.GroupBplus.Aff

namespace GlobalTheory.GroupBplus.Aff

theorem induced_endo_compat : ∀ (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (G₀ : Over (Sp K)) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (algebraMap R K)) F → ∀ (GG : PDivGroup p R) (θ : TorsionMap G GG), IsModel K θ → ∀ (GG₀ : PDivGroup p K) (θ₀ : TorsionMap G₀ GG₀) (e : GG₀ ≅ GG.baseChange K), GenCompat F θ θ₀ e → (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra K B], Function.Bijective (θ₀.pt n B)) → ∀ (f : G ⟶ G) (f₀ : G₀ ⟶ G₀) [IsMonHom f₀] (g : GG ⟶ GG) (g₀ : GG₀ ⟶ GG₀), f₀.left ≫ F = F ≫ f.left → θ.Intertwines f g → θ₀.Intertwines f₀ g₀ → g₀ ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap K g := by
  intro p _ R K _ _ _ _ _ _ _ _ G _ _ _ G₀ _ _ F hF GG θ _ GG₀ θ₀ e hc hbij f f₀ _ g g₀ hfF hθ hθ₀
  refine PDivGroup.baseChange_hom_ext fun n a => ?_
  let A := GG₀.A n
  letI : Algebra R A := ((algebraMap K A).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨z', hz'⟩ := (hbij n A).2 (AlgHom.id K A)
  have key : ∀ x y : A, θ₀.pt n A z' x = θ₀.pt n A z' y → x = y := fun x y h => by
    rw [hz'] at h; exact h
  apply key
  let w' : Tors G₀ (p ^ n) A := ⟨z'.1 ≫ f₀, by rw [← MonObj.pow_comp, z'.2, MonObj.one_comp]⟩
  let z := liftTors hF z'
  let w := liftTors hF w'
  have hw : w.1 = z.1 ≫ f := Over.OverMorphism.ext (by
    simp only [w, z, liftTors_left, Over.comp_left, w']
    rw [Category.assoc, hfF, ← Category.assoc])
  have h1 : θ₀.pt n A z' (g₀.app n (e.hom.app n (1 ⊗ₜ a))) = θ₀.pt n A w' (e.hom.app n (1 ⊗ₜ a)) :=
    (DFunLike.congr_fun (hθ₀ n A z' w' rfl) _).symm
  have h2 : θ.pt n A w a = θ₀.pt n A w' (e.hom.app n (1 ⊗ₜ a)) := hc n A w w' rfl a
  have h3 : θ.pt n A w a = θ.pt n A z (g.app n a) := DFunLike.congr_fun (hθ n A z w hw) a
  have h4 : θ.pt n A z (g.app n a) = θ₀.pt n A z' (e.hom.app n (1 ⊗ₜ g.app n a)) := hc n A z z' rfl _
  simp only [PDivGroup.comp_app, BialgHom.comp_apply, PDivGroup.baseChangeMap_app]
  rw [h1, ← h2, h3, h4]
  rfl

end GlobalTheory.GroupBplus.Aff
