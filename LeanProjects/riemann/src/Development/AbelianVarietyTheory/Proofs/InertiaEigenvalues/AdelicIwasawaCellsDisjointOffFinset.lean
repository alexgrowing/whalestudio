import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_mem_unipB (v : HeightOneSpectrum (𝓞 E)) {u : GA E n} (hu : u ∈ NA E n) :
    compV E n v u ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [compV, h1 i j hij]
  · simp [compV, h2 i]

theorem compV_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (v : HeightOneSpectrum (𝓞 E)) :
    compV E n v (tl n ϖ l) = GlobalTheory.IwaCell.tD (ϖ v) (l v) := by
  rw [tl_eq_diagT]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [compV, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have hc : ∀ x : Af E, pFin E (GlobalTheory.CuspRep.corner (sFin E) x) = x := fun x => by
      show ((1 : InfiniteAdeleRing E × Af E) - ((0 : InfiniteAdeleRing E), (1 : Af E)) + ((0 : InfiniteAdeleRing E), x)).2 = x
      simp
    have hf : ∀ y : (Af E)ˣ, ((finId E y : Ad E)) = GlobalTheory.CuspRep.corner (sFin E) (y : Af E) := fun y => rfl
    rw [hf, hc]
    congr 1
    show ((ϖ v ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply, Units.val_zpow_eq_zpow_val]
  · simp

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ord_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ}
    (hx : IsUnifV E v (x : v.adicCompletion E)) : GlobalTheory.SmGL.ord (v.adicCompletion E) x = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
  rfl

theorem compV_mem_cell (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {g : GA E n} (h : (tl n ϖ l)⁻¹ * g ∈ C0 E n S)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) : compV E n v g ∈ GlobalTheory.IwaCell.cell (ϖ v) (l v) := by
  obtain ⟨u, hu, k, hk, e⟩ := h
  have hg : g = tl n ϖ l * u * (tl n ϖ l)⁻¹ * tl n ϖ l * k := by
    rw [inv_mul_eq_iff_eq_mul] at e
    rw [e]; group
  have hkv : compV E n v k ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.HeckeEigConj.KO_eq_KGL]
    have := (Subgroup.mem_iInf.1 hk) v
    exact Subgroup.mem_comap.1 ((Subgroup.mem_iInf.1 this) hv)
  refine ⟨compV E n v (tl n ϖ l * u * (tl n ϖ l)⁻¹), compV_mem_unipB v (tl_conj_mem ϖ l hu), compV E n v k, hkv, ?_⟩
  rw [hg, map_mul, map_mul, compV_tl]

end GlobalTheory.CellDec

theorem GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  intro E _ _ n S ϖ hϖ l l' g hl hl' h h'
  ext v : 1
  by_cases hv : v ∈ S
  · rw [hl v hv, hl' v hv]
  · exact GlobalTheory.IwaCell.eq_of_mem_cell (GlobalTheory.CellDec.ord_of_isUnifV (hϖ v))
      (GlobalTheory.CellDec.compV_mem_cell ϖ l h hv) (GlobalTheory.CellDec.compV_mem_cell ϖ l' h' hv)
