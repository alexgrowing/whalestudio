import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
open scoped Classical

namespace GlobalTheory.RamShift

theorem whittaker_torusShift_add_factorisation_induction (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) (φ) (hφV : φ ∈ π.V)
    (hφ : ∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (x : GA E (m + 1)) (hx : x ∈ GlobalTheory.JSW.supS E (m + 1) T) (L : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)) :
    (∀ w ∈ T, L w = 0) → (∀ w, 0 ≤ L w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((shift m T ϖ).1 + L)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (shift m T ϖ).1) *
          ∏ w ∈ L.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (L w)) := by
  induction L using Finsupp.induction with
  | zero => intro _ _; simp
  | single_add a b f ha hb ih =>
    intro hT hlast
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have haT : a ∉ T := fun h => hb (by simpa [hfa] using hT a h)
    have hfT : ∀ w ∈ T, f w = 0 := fun w hw => by
      have hne : a ≠ w := fun e => haT (e ▸ hw)
      simpa [Finsupp.single_apply, hne] using hT w hw
    have hflast : ∀ w, 0 ≤ f w (Fin.last m) := fun w => by
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simpa [Finsupp.single_apply, hw] using hlast w
    have hblast : 0 ≤ b (Fin.last m) := by simpa [hfa] using hlast a
    set l₀ := (shift m T ϖ).1 with hl₀
    have hsplit : l₀ + (Finsupp.single a b + f) =
        (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a + b) := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    have hjoin : (l₀ - Finsupp.single a (l₀ a) + f) + Finsupp.single a (l₀ a) = l₀ + f := by
      ext w i
      by_cases hw : a = w
      · subst hw; simp [hfa]
      · simp [Finsupp.single_apply, hw]
    set g := x * GlobalTheory.CellDec.tl (m + 1) ϖ (l₀ - Finsupp.single a (l₀ a) + f) with hg
    have hga : GeneralLinearGroup.map ((pLoc E a).comp (pFin E)) g = 1 := by
      change GlobalTheory.CellDec.compV E (m + 1) a g = 1
      rw [hg, map_mul, GlobalTheory.CellDec.compV_tl]
      have h0 : (l₀ - Finsupp.single a (l₀ a) + f) a = 0 := by simp [hfa]
      have hxa : GlobalTheory.CellDec.compV E (m + 1) a x = 1 := hx a haT
      rw [h0, hxa, GlobalTheory.IwaCell.tD_zero, one_mul]
    have hl₀a : l₀ a = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) :=
      shift_apply_of_notMem m ϖ haT
    have key := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π a (α ⟨a, haT⟩) (hα ⟨a, haT⟩) φ hφV (hφ a haT) (ϖ a) (hϖ a) (condExp ϖ a)
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ a (hϖ a)) g hga b hblast
    have h1 : l₀ a + b = fun i : Fin (m + 1) => condExp ϖ a * ((m : ℤ) - ((i : ℕ) : ℤ)) + b i := by
      rw [hl₀a]; rfl
    rw [hsplit, GlobalTheory.CellDec.tl_add, GlobalTheory.CellDec.tl_single, ← mul_assoc, ← hg, h1, key, ← hl₀a,
      ← GlobalTheory.CellDec.tl_single, hg, mul_assoc, ← GlobalTheory.CellDec.tl_add, hjoin, ih hfT hflast,
      Finsupp.support_single_add ha hb, Finset.prod_cons, dif_neg haT]
    have hval : (Finsupp.single a b + f) a = b := by simp [hfa]
    have hrest : ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) ((Finsupp.single a b + f) w)) =
        ∏ w ∈ f.support, (if h : w ∈ T then 1 else
          GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (f w)) := by
      refine Finset.prod_congr rfl fun w hw => ?_
      have hne : a ≠ w := fun e => ha (e ▸ hw)
      simp [Finsupp.single_apply, hne]
    rw [hval, hrest]
    change GlobalTheory.RSCell.sphZ (Ideal.absNorm a.asIdeal) _ b * _ = _
    ring

theorem whit_mul_tl_shift_add : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) T, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, (∀ w, 0 ≤ l.1 w (Fin.last m)) →
      GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ ((GlobalTheory.RamShift.shift m T ϖ).1 + l.1)) =
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) *
          ∏ w ∈ l.1.support, (if h : w ∈ T then 1 else
            GlobalTheory.RSCell.sphZ (Ideal.absNorm w.asIdeal) (fun i => ((α ⟨w, h⟩ i : ℂˣ) : ℂ)) (l.1 w)) := by
  intro E _ _ _ m T π α hα φ hφV hφ ϖ hϖ x hx l hl
  exact whittaker_torusShift_add_factorisation_induction E m T π α hα φ hφV hφ ϖ hϖ x hx l.1 l.2 hl

end GlobalTheory.RamShift
