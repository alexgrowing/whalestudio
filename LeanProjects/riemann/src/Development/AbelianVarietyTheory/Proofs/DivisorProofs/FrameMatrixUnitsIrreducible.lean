import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GLPath

open Polynomial

theorem appTop_spec_map {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop r = (Scheme.ΓSpecIso S).inv (g ((Scheme.ΓSpecIso R).hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

def line {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) : Matrix (Fin m) (Fin m) L[X] :=
  (1 - X : L[X]) • (1 : Matrix (Fin m) (Fin m) L[X]) + (X : L[X]) • A.map C

theorem eval_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 0 (line A i j) = (1 : Matrix (Fin m) (Fin m) L) i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eval_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 1 (line A i j) = A i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem mapMatrix_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (0 : L)).mapMatrix (line A) = 1 := by
  ext i j; exact eval_line_zero A i j

theorem mapMatrix_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (1 : L)).mapMatrix (line A) = A := by
  ext i j; exact eval_line_one A i j

end GlobalTheory.GLPath

namespace GlobalTheory.GLPath
open Polynomial

theorem exists_path : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ)
    (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) →
    ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)),
      IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧
      (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧
      (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  intro L _ ι _ n A hA
  classical
  set p : L[X] := ∏ a, (line (A a)).det with hp_def
  have hev : ∀ x : L, eval x p = ∏ a, ((evalRingHom x).mapMatrix (line (A a))).det := by
    intro x
    rw [hp_def, ← coe_evalRingHom, map_prod]
    exact Finset.prod_congr rfl fun a _ => RingHom.map_det _ _
  have hu0 : IsUnit ((evalRingHom (0 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_zero, Matrix.det_one, Finset.prod_const_one, isUnit_one]
  have hu1 : IsUnit ((evalRingHom (1 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_one]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => hA a
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hu0; exact not_isUnit_zero hu0
  let R := Localization.Away p
  haveI : IsDomain R := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  let c : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom ((algebraMap L[X] R).comp C))
  let f₁ : R →+* L := IsLocalization.Away.lift p hu0
  let f₂ : R →+* L := IsLocalization.Away.lift p hu1
  have hf : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) (q : L[X]),
      (IsLocalization.Away.lift (S := R) p hx) (algebraMap L[X] R q) = eval x q := by
    intro x hx q
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hsec : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)),
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx)) ≫ c = 𝟙 _ := by
    intro x hx
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    simp [c, hf]
  let B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(Spec (CommRingCat.of R), ⊤) := fun a =>
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap L[X] R)).mapMatrix (line (A a))
  have hval : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) a i j,
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx))).appTop (B a i j) =
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv (eval x (line (A a) i j)) := by
    intro x hx a i j
    rw [appTop_spec_map]
    simp [B, hf]
  refine ⟨Spec (CommRingCat.of R), c, _, _, hsec 0 hu0, hsec 1 hu1, B, inferInstance, ?_, ?_, ?_⟩
  · intro a
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [B]
    rw [← RingHom.map_det]
    have hdvd : (line (A a)).det ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    have hpu : IsUnit (algebraMap L[X] R p) := IsLocalization.Away.algebraMap_isUnit p
    rw [RingHom.comp_apply]
    exact (isUnit_of_dvd_unit (map_dvd (algebraMap L[X] R) hdvd) hpu).map _
  · intro a i j
    rw [hval 0 hu0, eval_line_zero]
  · intro a i j
    rw [hval 1 hu1, eval_line_one]

end GlobalTheory.GLPath
