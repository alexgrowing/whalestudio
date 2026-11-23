import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cosimplicial_ses_exactAt_succ :
    ∀ (Z M Q : CosimplicialObject AddCommGrpCat.{1}) (i : Z ⟶ M) (p : M ⟶ Q), (∀ k, Function.Injective (i.app k)) → (∀ k (y : M.obj k), p.app k y = 0 ↔ ∃ w, i.app k w = y) → (∀ k, Function.Surjective (p.app k)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Z).ExactAt (n + 1)) → (∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj M).ExactAt (n + 1)) → ∀ n : ℕ, ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).obj Q).ExactAt (n + 1) := by
  intro Z M Q i p hinj hex hsurj h₁ h₂
  let F := AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}
  have hw : F.map i ≫ F.map p = 0 := by
    ext k y
    exact (hex _ (i.app _ y)).2 ⟨y, rfl⟩
  let T : ShortComplex (CochainComplex AddCommGrpCat.{1} ℕ) := ShortComplex.mk (F.map i) (F.map p) hw
  have hT : T.ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k => ?_
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.ab_exact_iff]; intro x hx; exact (hex _ x).1 hx
    · rw [AddCommGrpCat.mono_iff_injective]; exact hinj _
    · rw [AddCommGrpCat.epi_iff_surjective]; exact hsurj _
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have e := hT.homology_exact₃ (n + 1) (n + 2) rfl
  have z2 : IsZero (T.X₂.homology (n + 1)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₂ n)
  have z1 : IsZero (T.X₁.homology (n + 2)) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (h₁ (n + 1))
  exact e.isZero_X₂ (z2.eq_of_src _ _) (z1.eq_of_tgt _ _)

end GlobalTheory.EtC
