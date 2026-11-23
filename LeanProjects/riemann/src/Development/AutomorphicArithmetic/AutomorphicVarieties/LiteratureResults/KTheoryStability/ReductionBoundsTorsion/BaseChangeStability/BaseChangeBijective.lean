import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.KStability
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.DedekindSR
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.GrpHComp

noncomputable section

open CategoryTheory UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB.StabilizationIso

theorem stab_self (R : Type) [CommRing R] (n : ℕ) (h : n ≤ n) : stab R n n h = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp [stab_apply]

theorem stab_comp (R : Type) [CommRing R] {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (h : n ≤ k) :
    stab R n k h = (stab R m k h₂).comp (stab R n m h₁) := by
  refine MonoidHom.ext fun g => ?_
  ext i j
  simp only [MonoidHom.comp_apply, stab_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem isIso_stab (R : Type) [CommRing R] [IsDedekindDomain R] (i n : ℕ) (hn : 2 * i + 4 ≤ n) :
    ∀ (m : ℕ) (h : n ≤ m), IsIso (grpHMap (stab R n m h) i) := by
  intro m h
  induction m, h using Nat.le_induction with
  | base =>
    rw [stab_self, grpHComp.1]
    infer_instance
  | succ m hm ih =>
    rw [stab_comp R hm (Nat.le_succ m), grpHComp.2]
    have := PositivityTheory.v8.KStability.kStability R 2 (dedekindSR R) i m (by omega)
    infer_instance

theorem baseChange_bijective {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) [IsIso f] :
    Function.Bijective (LinearMap.baseChange ℝ f.hom) := by
  have h1 : (inv f).hom ∘ₗ f.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.hom_inv_id, ModuleCat.hom_id]
  have h2 : f.hom ∘ₗ (inv f).hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, IsIso.inv_hom_id, ModuleCat.hom_id]
  have l1 : (LinearMap.baseChange ℝ (inv f).hom) ∘ₗ LinearMap.baseChange ℝ f.hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h1, LinearMap.baseChange_id]
  have l2 : (LinearMap.baseChange ℝ f.hom) ∘ₗ LinearMap.baseChange ℝ (inv f).hom = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, h2, LinearMap.baseChange_id]
  refine ⟨Function.LeftInverse.injective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_,
    Function.RightInverse.surjective (g := LinearMap.baseChange ℝ (inv f).hom) fun x => ?_⟩
  · simpa using LinearMap.congr_fun l1 x
  · simpa using LinearMap.congr_fun l2 x

end PositivityTheory.KB.StabilizationIso

end
