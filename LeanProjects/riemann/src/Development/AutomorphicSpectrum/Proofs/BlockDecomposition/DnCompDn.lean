import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeCx

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]

section Act

variable (F : C ⥤ CommAlgCat.{0} R)

def act {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : Cn F m →ₗ[R] Cn F n :=
  LinearMap.pi fun c ↦ (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).toLinearMap ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem act_apply {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : Cn F m) (c : Fin (n + 1) ⥤ C) :
    act F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) :=
  rfl

private theorem mp_map_endo_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x : Fin (n + 1)} (h : x ⟶ x)
    (b : F.obj (c.obj x)) : GlobalTheory.CatCoh.mp F (c.map h) b = b := by
  have hc : c.map h = 𝟙 (c.obj x) := by
    rw [Subsingleton.elim h (𝟙 x)]
    exact c.map_id x
  rw [hc, GlobalTheory.CatCoh.mp_id]

private theorem mp_map_comp_apply {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)}
    (h : x ⟶ z) (h₁ : x ⟶ y) (h₂ : y ⟶ z) (b : F.obj (c.obj x)) :
    GlobalTheory.CatCoh.mp F (c.map h) b =
      GlobalTheory.CatCoh.mp F (c.map h₂) (GlobalTheory.CatCoh.mp F (c.map h₁) b) := by
  rw [Subsingleton.elim h (h₁ ≫ h₂), Functor.map_comp, GlobalTheory.CatCoh.mp_comp]

theorem act_id {n : ℕ} (f : Cn F n) : act F (OrderHom.id : Fin (n + 1) →o Fin (n + 1)) f = f := by
  funext c
  show GlobalTheory.CatCoh.mp F (c.map (𝟙 (Fin.last n))) (f c) = f c
  exact mp_map_endo_apply F c _ _

theorem act_comp {k m n : ℕ} (θ : Fin (k + 1) →o Fin (m + 1)) (ψ : Fin (m + 1) →o Fin (n + 1))
    (f : Cn F k) : act F (ψ.comp θ) f = act F ψ (act F θ f) := by
  funext c
  exact mp_map_comp_apply F c _
    (homOfLE (ψ.monotone (Fin.le_last (θ (Fin.last k))))) (homOfLE (Fin.le_last (ψ (Fin.last m))))
    (f ((ψ.comp θ).monotone.functor ⋙ c))

def cosimp : CosimplicialObject (ModuleCat.{0} R) where
  obj a := ModuleCat.of R (Cn F a.len)
  map θ := ModuleCat.ofHom (act F θ.toOrderHom)
  map_id a := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_id F f)
  map_comp θ ψ := ModuleCat.hom_ext (LinearMap.ext fun f ↦ act_comp F θ.toOrderHom ψ.toOrderHom f)

theorem cof_eq (n : ℕ) (i : Fin (n + 2)) :
    cof F n i = act F (Fin.succAboveOrderEmb i).toOrderHom := rfl

theorem objD_hom (n : ℕ) : (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp F) n).hom = dn F n := by
  unfold AlgebraicTopology.AlternatingCofaceMapComplex.objD
  rw [ModuleCat.hom_sum, MainStatements.Hodge.dn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModuleCat.hom_zsmul]
  first
  | rfl
  | (rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]; rfl)

theorem dn_comp_dn (n : ℕ) : dn F (n + 1) ∘ₗ dn F n = 0 := by
  have h := congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (GlobalTheory.CompanionTheory.HodgeCx.cosimp F) n)
  rw [ModuleCat.hom_comp, GlobalTheory.CompanionTheory.HodgeCx.objD_hom, GlobalTheory.CompanionTheory.HodgeCx.objD_hom,
    ModuleCat.hom_zero] at h
  exact h

end Act

theorem pulln_cof {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) (i : Fin (n + 2)) (f : Cn F n) :
    pulln m (n + 1) (cof F n i f) = cof G n i (pulln m n f) := by
  funext c
  exact m.3 (c.map (homOfLE (Fin.le_last _))) (f (MainStatements.Hodge.face i c ⋙ m.1))

theorem pulln_dn {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) :
    pulln m (n + 1) ∘ₗ dn F n = dn G n ∘ₗ pulln m n := by
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, MainStatements.Hodge.dn, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, map_zsmul, GlobalTheory.CompanionTheory.HodgeCx.pulln_cof]

theorem cxSt : CxSt := by
  intro R _ C _ F
  exact ⟨GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn F, fun D _ G m n => GlobalTheory.CompanionTheory.HodgeCx.pulln_dn m n⟩

end GlobalTheory.CompanionTheory.HodgeCx
