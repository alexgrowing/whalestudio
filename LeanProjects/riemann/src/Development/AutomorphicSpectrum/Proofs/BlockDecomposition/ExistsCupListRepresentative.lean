import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeRepCup

open GlobalTheory.CompanionTheory.CupRep

theorem cupList_cocycle {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) :
    ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → CH.d _ m (cupListC A ℓ) = 0
  | 0, _, _ => by
      funext s
      change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom 1 = (0 : A.obj _)
      rw [Fin.sum_univ_two, map_one, map_one]
      simp
  | m + 1, ℓ, h => by
      change CH.d _ (m + 1) ((CH.mulP A).cupC (by omega) (cupListC A fun i => ℓ (Fin.castSucc i)) (ℓ (Fin.last m))) = 0
      rw [CrystallineSemistableComparison.P.leibniz, cupList_cocycle A _ (fun k => h _), h]
      simp

theorem cupList_mem {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) : ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1),
    (∀ k, ℓ k ∈ FC (Fil ((1 : ℕ) : ℤ)) 1) → cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m
  | 0, _, _ => mem_FC.2 fun s => by
      rw [Nat.cast_zero, hF.top 0 le_rfl]
      exact trivial
  | m + 1, ℓ, h => cup_mem hF (r := m) (r' := 1) _ (cupList_mem hF _ fun k => h _) (h _)

theorem exists_rep {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A) :
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := by
  intro hF m ℓ hd hl
  have hm : cupListC Φ.A ℓ ∈ FC (Fil (m : ℤ)) m :=
    cupList_mem hF ℓ fun k => mem_FC.2 fun s => by simpa using hl k s
  refine GlobalTheory.CompanionTheory.ConeLocal.rep_exists (cupListC Φ.A ℓ) (mem_FC.1 hm) fun s => ?_
  rw [cupList_cocycle Φ.A ℓ hd]
  exact (Fil ((m : ℤ) + 1)).S _ |>.zero_mem

end GlobalTheory.CompanionTheory.ConeRepCup
