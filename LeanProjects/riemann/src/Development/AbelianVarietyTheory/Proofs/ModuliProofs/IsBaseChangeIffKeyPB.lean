import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.PolarizationCorrespondence

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence

namespace GlobalTheory.KeyInputCompare

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem epsScaleR_eq (c : R) : epsScaleR c = epsHom (RingHom.id R) c := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

theorem epsScale_left (c : R) : (epsScale c).left = spMap (epsScaleR c) := by
  rw [epsScaleR_eq]; rfl

end Dual

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ v ∈ lieSub G := by
  change _ ↔ epsZero R ≫ v = η[G]
  constructor
  · intro h; ext1; exact h
  · intro h; exact congrArg CommaMorphism.left h

theorem linComb_val {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) :
    (linComb c v).1 = (List.ofFn fun i => epsScale (c i) ≫ (v i).1).prod := by
  rw [linComb, Subgroup.val_list_prod, List.map_ofFn]
  rfl

theorem isLieComb_iff_prod {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = (List.ofFn fun i => epsScale (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => epsScale (c i) ≫ v i := by
      funext i; ext1; rw [hu, Over.comp_left, epsScale_left]
    rw [this]
  · rintro rfl
    exact ⟨_, fun i => by rw [Over.comp_left, epsScale_left], rfl⟩

theorem isLieComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) (w : epsR R ⟶ G) :
    IsLieComb c (fun i => (v i).1) w ↔ w = (linComb c v).1 := by
  rw [isLieComb_iff_prod, linComb_val]

theorem isLieBasis_val_iff {n : ℕ} (v : Fin n → Tan G) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis (fun i => (v i).1) ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis v := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence.IsLieBasis, Function.bijective_iff_existsUnique]
  constructor
  · rintro ⟨-, h⟩ w
    have := h w.1 ((isTangent_iff _).2 w.2)
    simp only [isLieComb_iff] at this
    simpa only [Subtype.ext_iff, eq_comm (b := w.1)] using this
  · intro h
    refine ⟨fun i => (isTangent_iff _).2 (v i).2, fun w hw => ?_⟩
    have := h ⟨w, (isTangent_iff _).1 hw⟩
    simp only [isLieComb_iff]
    simpa only [Subtype.ext_iff, eq_comm (b := w)] using this

end Lie

section Input

variable {R R' : Type} [CommRing R] [CommRing R']

def keyInEquiv (R : Type) [CommRing R] : KeyIn R ≃ KeyInput R where
  toFun x :=
    { P := x.P, dim_pos := x.g_pos, rig := x.rig, rig_gen := x.rig_gen, th := x.th, th_ne := x.th_ne
      b := fun i => ⟨x.v i, (isTangent_iff _).1 (x.basis.1 i)⟩
      b_basis := (isLieBasis_val_iff _).1 x.basis }
  invFun y :=
    { P := y.P, g_pos := y.dim_pos, rig := y.rig, rig_gen := y.rig_gen, th := y.th, th_ne := y.th_ne
      v := fun i => (y.b i).1
      basis := (isLieBasis_val_iff _).2 y.b_basis }
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem keyInEquiv_P (x : KeyIn R) : (keyInEquiv R x).P = x.P := rfl
@[simp] theorem keyInEquiv_rig (x : KeyIn R) : (keyInEquiv R x).rig = x.rig := rfl
@[simp] theorem keyInEquiv_th (x : KeyIn R) : (keyInEquiv R x).th = x.th := rfl
@[simp] theorem keyInEquiv_b (x : KeyIn R) (i : Fin x.P.g) : ((keyInEquiv R x).b i).1 = x.v i := rfl
@[simp] theorem keyInEquiv_symm_P (y : KeyInput R) : ((keyInEquiv R).symm y).P = y.P := rfl
@[simp] theorem keyInEquiv_symm_rig (y : KeyInput R) : ((keyInEquiv R).symm y).rig = y.rig := rfl
@[simp] theorem keyInEquiv_symm_th (y : KeyInput R) : ((keyInEquiv R).symm y).th = y.th := rfl
@[simp] theorem keyInEquiv_symm_v (y : KeyInput R) (i : Fin y.P.g) :
    ((keyInEquiv R).symm y).v i = (y.b i).1 := rfl

end Input

end GlobalTheory.KeyInputCompare
