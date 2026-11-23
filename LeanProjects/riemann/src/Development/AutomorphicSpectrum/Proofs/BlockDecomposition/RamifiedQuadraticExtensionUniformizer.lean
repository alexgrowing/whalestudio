import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.WcLeft

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem lower_entry {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) (g : GL (Fin 2) F) (j : Fin 2) :
    (u * g).val 1 j = g.val 1 j := by
  have h10 : u.val 1 0 = 0 := hu.1 (show (0 : Fin 2) < 1 by decide)
  have h11 : u.val 1 1 = 1 := hu.2 1
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]

theorem upper_entry {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) (g : GL (Fin 2) F) (j : Fin 2) :
    (u * g).val 0 j = g.val 0 j + u.val 0 1 * g.val 1 j := by
  have h00 : u.val 0 0 = 1 := hu.2 0
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h00]

theorem det_mul_unipotent {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) (g : GL (Fin 2) F) :
    ((u * g).val).det = (g.val).det := by
  have h10 : u.val 1 0 = 0 := hu.1 (show (0 : Fin 2) < 1 by decide)
  have h00 : u.val 0 0 = 1 := hu.2 0
  have h11 : u.val 1 1 = 1 := hu.2 1
  rw [Units.val_mul, Matrix.det_mul, Matrix.det_fin_two (u.val), h00, h11, h10]
  ring

theorem mRow_unipotent_mul {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) (g : GL (Fin 2) F) :
    mRow (u * g) = mRow g := by
  unfold mRow
  simp only [lower_entry hu]

theorem xRow_unipotent_mul {u : GL (Fin 2) F} (hu : u ∈ Iwasawa.unipotent F 2) (g : GL (Fin 2) F) :
    xRow (u * g) = xRow g + u.val 0 1 := by
  have hm := GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.mRow_ne_zero g
  unfold xRow
  simp only [lower_entry hu, upper_entry hu]
  by_cases h : modulus (g.val 1 0) < modulus (g.val 1 1)
  · have hd : g.val 1 1 ≠ 0 := by
      have : mRow g = g.val 1 1 := by simp [mRow, h]
      exact this ▸ hm
    rw [if_pos h, if_pos h]
    field_simp
  · have hc : g.val 1 0 ≠ 0 := by
      have : mRow g = g.val 1 0 := by simp [mRow, h]
      exact this ▸ hm
    rw [if_neg h, if_neg h]
    field_simp

end

theorem Wc_unipotent_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ (u g : GL (Fin 2) F), u ∈ Iwasawa.unipotent F 2 → GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (u * g) = (χ (u.val 0 1) : ℂ) * GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ η σ c hχ hc hη hform u g hu
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hdet := det_mul_unipotent hu g
  by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · obtain ⟨t, ht⟩ := hg
    rw [InertAsm.Wc_eq hc hform (u * g) t (ht.trans hdet.symm), InertAsm.Wc_eq hc hform g t ht]
    unfold InertAsm.val
    rw [hdet, mRow_unipotent_mul hu g, xRow_unipotent_mul hu g, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    ring
  · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((u * g).val).det := by
      rw [hdet]; exact hg
    rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg', mul_zero]

end GlobalTheory.CompanionTheory.SphTheta.WcLeft
