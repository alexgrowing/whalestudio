import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TanLift

theorem comp_one_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact MonObj.comp_one u

theorem comp_mul_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    u ≫ (a * b) = (u ≫ a) * (u ≫ b) := by
  exact MonObj.comp_mul u a b

theorem comp_pow_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a : X ⟶ M) (n : ℕ) :
    u ≫ a ^ n = (u ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_mul_over, ih]

section

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

theorem pt_zero (M : LieModel G x L) : M.pt 0 = 1 := by
  have h : M.pt 0 * M.pt 0 = M.pt 0 := by rw [← M.5, add_zero]
  exact mul_eq_left.mp h

theorem pt_nsmul (M : LieModel G x L) (e : L) (n : ℕ) : M.pt (n • e) = M.pt e ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_zero]
  | succ n ih => rw [succ_nsmul, M.5, ih, pow_succ]

theorem dualMap_epsMul (I : Ideal R) (c : R) (hc : Ideal.Quotient.mk I c = 0) :
    (dualMap (Ideal.Quotient.mk I)).comp (epsMul c) =
      ((algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I)).comp
        (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, hc]

theorem dualMap_algebraMap (I : Ideal R) :
    (dualMap (Ideal.Quotient.mk I)).comp (algebraMap R (DualNumber R)) =
      (algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end

theorem tangent_mod_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L), ∃! (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M e
  obtain ⟨-, -, hinj, htors⟩ := hi
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
      (Ideal.Quotient.mk (Ideal.span {(N : R)})))))
  have hu : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
      (GlobalTheory.CompanionTheory.Ar.epsAt x).hom = (Over.mk (Y.hom ≫ x)).hom := by
    simp only [GlobalTheory.CompanionTheory.Ar.epsAt, Over.mk_hom, Y]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_algebraMap]
  let u : Over.mk (Y.hom ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x := Over.homMk _ hu
  let u₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (N : R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have htan : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left =
      (1 : Over.mk x ⟶ G).left := M.2 e
  have hg : (u ≫ M.pt e) ^ N = 1 := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_pow_over, ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_nsmul, ← Nat.cast_smul_eq_nsmul R,
      ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u₀]
    apply Over.OverMorphism.ext
    have e₁ : (u ≫ M.pt ((N : R) • e)).left =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (N : R))) ≫ (M.pt e).left := by
      rw [Over.comp_left, M.6]
      rfl
    have e₂ : (u₀ ≫ (1 : Over.mk x ⟶ G)).left =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
            (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left := by
      rw [Over.comp_left, htan]
      rfl
    rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_epsMul _ _ hN]
  obtain ⟨y, hy⟩ := (htors Y (u ≫ M.pt e)).1 hg
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · rw [hy]
    rfl
  · rintro v ⟨hv₁, hv₂⟩
    have hv : Over.homMk (U := Y) (V := Γ.G) v hv₁ = y := by
      refine hinj Y _ y ?_
      change v ≫ i = _
      rw [hv₂, hy]
      rfl
    calc v = (Over.homMk (U := Y) (V := Γ.G) v hv₁).left := rfl
      _ = y.left := by rw [hv]

end GlobalTheory.CompanionTheory.Ar.BT.TanLift
