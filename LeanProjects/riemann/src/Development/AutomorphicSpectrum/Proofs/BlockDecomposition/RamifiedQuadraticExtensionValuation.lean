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

namespace GlobalTheory.CompanionTheory.SphTheta.InertAsm

theorem Wc_intInd_right_invariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ (g k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (g * k) = GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ _ χ η σ c hχ hc hη hform g k hk
  obtain ⟨hη1, hηu, -, -⟩ := hη
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hrow := GlobalTheory.CompanionTheory.SphTheta.RowIwasawa.iwasawa_lower_row F
  have hdk : modulus (k.val).det = 1 := by
    have h1 := (hrow 1 k hk).2.1
    simpa using h1
  obtain ⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by
    have hk0 : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
    have h1 := hη1 (Units.mk0 _ hk0)
    rw [char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one,
      Units.val_one, Units.val_mk0, GL2LocalData.nsg] at h1
    by_contra hn
    rw [if_neg hn] at h1
    norm_num at h1
  by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · obtain ⟨t, ht⟩ := hg
    have ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det := by
      rw [Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]
    rw [Wc_eq hc hform _ _ ht', Wc_eq hc hform _ _ ht]
    obtain ⟨hm0, hdet, hmm, hx⟩ := hrow g k hk
    exact val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx
  · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det := by
      rintro ⟨t', ht'⟩
      refine hg ⟨t' * s⁻¹, ?_⟩
      have hs0 : Algebra.norm F (s : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 s.ne_zero
      have hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) =
          Algebra.norm F (t' : E) := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
      have hd : ((g * k).val).det = (g.val).det * (k.val).det := by
        rw [Units.val_mul, Matrix.det_mul]
      rw [ht', hs, hd] at hmul
      exact mul_right_cancel₀ (hs ▸ hs0) hmul
    rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']

end GlobalTheory.CompanionTheory.SphTheta.InertAsm
