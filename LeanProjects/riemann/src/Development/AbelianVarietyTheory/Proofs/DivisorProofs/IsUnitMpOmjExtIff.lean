import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.CechDR.FormExtJ

open GlobalTheory.CatCoh

section Inst

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (j : ℕ)

@[reducible] def opModJ : Module Bᵐᵒᵖ (Om R B j) :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModJ

theorem isCentralScalarJ : IsCentralScalar B (Om R B j) := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTowerJ : IsScalarTower R Bᵐᵒᵖ (Om R B j) := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

end Inst

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

def extMapJ {T T' : C} (φ : T ⟶ T') :
    TrivSqZeroExt (F.obj T) (Om R (F.obj T) j) →ₐ[R] TrivSqZeroExt (F.obj T') (Om R (F.obj T') j) where
  toFun c := TrivSqZeroExt.inl (mp F φ c.fst) + TrivSqZeroExt.inr (pOm F j φ c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [pOm_smul]
  commutes' r := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).fst = mp F φ c.fst := by
  simp [extMapJ]

theorem snd_extMapJ {T T' : C} (φ : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) :
    (extMapJ F j φ c).snd = pOm F j φ c.snd := by
  simp [extMapJ]

def omjExt : C ⥤ CommAlgCat.{0} R where
  obj T := CommAlgCat.of R (TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
  map φ := CommAlgCat.ofHom (extMapJ F j φ)
  map_id T := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans (mp_id F T _)) ((snd_extMapJ F j _ c).trans (pOm_id F _)))
  map_comp φ ψ := CommAlgCat.hom_ext (AlgHom.ext fun c ↦ TrivSqZeroExt.ext
    ((fst_extMapJ F j _ c).trans ((mp_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).fst
      rw [fst_extMapJ, fst_extMapJ])))
    ((snd_extMapJ F j _ c).trans ((pOm_comp F φ ψ _).trans (by
      change _ = ((extMapJ F j ψ) (extMapJ F j φ c)).snd
      rw [snd_extMapJ, snd_extMapJ]))))

theorem mp_omjExt_inr {T T' : C} (φ : T ⟶ T') (x : Om R (F.obj T) j) :
    mp (omjExt F j) φ (TrivSqZeroExt.inr x : (omjExt F j).obj T) =
      (TrivSqZeroExt.inr (pOm F j φ x) : (omjExt F j).obj T') := by
  change extMapJ F j φ (TrivSqZeroExt.inr x) = _
  exact TrivSqZeroExt.ext ((fst_extMapJ F j φ _).trans (by simp)) ((snd_extMapJ F j φ _).trans (by simp))

theorem snd_mp_omjExt {T T' : C} (φ : T ⟶ T') (c : (omjExt F j).obj T) :
    (mp (omjExt F j) φ c).snd = pOm F j φ c.snd := snd_extMapJ F j φ c

theorem isUnit_mp_omjExt_iff {T S : C} (u : T ⟶ S) (c : (omjExt F j).obj T) :
    IsUnit (mp (omjExt F j) u c) ↔ IsUnit (mp F u c.fst) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.trans (iff_of_eq (congrArg IsUnit (fst_extMapJ F j u c)))

theorem span_inlJ_eq_top {S : C} {n : ℕ} {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ (TrivSqZeroExt.inl (b i) : (omjExt F j).obj S)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom (F.obj S) (Om R (F.obj S) j))) hb
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

end GlobalTheory.CechDR.FormExtJ
