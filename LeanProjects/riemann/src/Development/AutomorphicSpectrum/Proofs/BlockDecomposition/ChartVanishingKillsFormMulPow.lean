import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace resG)
open GlobalTheory.ProjSpace (chart formOn ratioOn ratio)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

theorem app_presheaf_map {A B : Scheme.{0}} (φ : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (h' : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U) (a : Γ(A, U)) :
    (φ.app V).hom ((A.presheaf.map (homOfLE h).op).hom a) =
      (B.presheaf.map (homOfLE h').op).hom ((φ.app U).hom a) := by
  have e := congrArg (fun g => CommRingCat.Hom.hom g a) (φ.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {R : Type} [CommRing R] {N : ℕ}

private theorem formOn_congr {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f g : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (h : f = g) :
    formOn U i hi n f hf = formOn U i hi n g hg := by
  subst h
  rfl

theorem formOn_X_pow (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hi : U ≤ chart R N i)
    (j : Fin (N + 1)) (m : ℕ) :
    formOn U i hi m (X j ^ m) (isHomogeneous_X_pow j m) = ratioOn U i hi j ^ m := by
  induction m with
  | zero =>
    rw [formOn_congr _ (isHomogeneous_C _ (1 : R)) (by simp), GlobalTheory.ProjSpace.formOn_C, map_one, pow_zero]
  | succ m ih =>
    rw [formOn_congr _ ((isHomogeneous_X_pow j m).mul (isHomogeneous_X R j)) (pow_succ _ _),
      GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow j m) (isHomogeneous_X R j), ih, GlobalTheory.ProjSpace.formOn_X, pow_succ]

theorem exists_ratio_pow_mul_eq_zero {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1))
    (h0 : (φ.app (chart R N k)).hom (formOn (chart R N k) k le_rfl n f hf) = 0)
    (j : Fin (N + 1)) :
    ∃ m : ℕ, (φ.app (chart R N j)).hom (ratio R N j k) ^ m *
      (φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf) = 0 := by
  have hW : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N j :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_left
  have hW' : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N k :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_right
  have e1 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N j) (i := j) (hi := le_rfl)
    (inf_le_left : chart R N j ⊓ chart R N k ≤ chart R N j) hf
  have e2 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N k) (i := k) (hi := le_rfl)
    (inf_le_right : chart R N j ⊓ chart R N k ≤ chart R N k) hf
  have e3 := GlobalTheory.ProjSpace.formOn_eq_ratioOn_pow_mul (U := chart R N j ⊓ chart R N k) (i := j)
    (hi := inf_le_left) (j := k) inf_le_right hf
  have key : (Y.presheaf.map (homOfLE hW).op).hom
      ((φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf)) = 0 := by
    rw [← app_presheaf_map φ inf_le_left hW]
    erw [e1]
    rw [e3, ← e2, map_mul]
    erw [app_presheaf_map φ inf_le_right hW']
    rw [h0, map_zero, mul_zero]
  have hle : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ≤ φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) := by
    rw [← Scheme.preimage_basicOpen, GlobalTheory.ProjSpace.basicOpen_ratioOn]
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y (U := φ ⁻¹ᵁ chart R N j)
    (φ.isCompact_preimage (GlobalTheory.ProjSpace.isAffineOpen_chart R N j).isCompact) _ _ ?_
  show (Y.presheaf.map (homOfLE _).op).hom _ = 0
  rw [show (homOfLE (Y.basicOpen_le _) : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ⟶ φ ⁻¹ᵁ chart R N j) =
      homOfLE hle ≫ homOfLE hW from rfl, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, key,
    map_zero]

theorem exists_killsForm_X_pow_mul :
    ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  intro R _ N Y φ _ n f hf k h0
  choose m hm using fun j => exists_ratio_pow_mul_eq_zero φ n f hf k h0 j
  refine ⟨∑ j, m j, (isHomogeneous_X_pow k _).mul hf, ?_⟩
  intro j
  rw [GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow k _) hf, formOn_X_pow, map_mul, map_pow]
  have hle : m j ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hm j, mul_zero]

end GlobalTheory.CompanionTheory.GE
