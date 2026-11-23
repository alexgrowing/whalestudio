import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirPatch

theorem eq_on_cell_of_eq_on_slice : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ GlobalTheory.JSW.mirS E S m → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  intro E _ _ _ m S b W V q hq hqi hb hW hbV hWV hsl p hp hpc
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hpc
  have key : u * q * finGL E (m + 1) k * infGL E (m + 1) y = u * ((q * infGL E (m + 1) y) * finGL E (m + 1) k) := by
    rw [mul_assoc (q) (infGL E (m + 1) y), infGL_comm, ← mul_assoc, ← mul_assoc]

  have hy : ∀ j, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have h1 := congrArg (pInf E) (hp.2 j)
    have hmap : GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y)
        = GeneralLinearGroup.map (pInf E) u * y := by
      simp [map_mul, hqi]
    have h2 : (GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
        = if j = Fin.last m then 1 else 0 := by
      rw [GeneralLinearGroup.map_apply] at *
      simpa [apply_ite (pInf E)] using h1
    rw [hmap] at h2
    rw [← h2]
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Fin.last m)]
    · have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) (Fin.last m) = 1 := hu.2 _
      simp [GeneralLinearGroup.map_apply, this]
    · intro l _ hl
      have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
      have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = 0 := hu.1 _ _ hlt
      simp [GeneralLinearGroup.map_apply, this]
    · simp
  have hslice : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [map_mul, hq.1 w hw, one_mul]
      exact map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
    · intro j
      refine ad_ext ?_ ?_
      · have := congrArg (fun g : GL (Fin (m + 1)) (Cinf E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y by simp [hqi])
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hy j]; split_ifs <;> simp
      · have := congrArg (fun g : GL (Fin (m + 1)) (Af E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q by simp)
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hq.2 j]
  rw [key, hW u hu, hb u hu, hWV k hk, hbV k hk, hsl y hslice]

end GlobalTheory.JSW.MirPatch
