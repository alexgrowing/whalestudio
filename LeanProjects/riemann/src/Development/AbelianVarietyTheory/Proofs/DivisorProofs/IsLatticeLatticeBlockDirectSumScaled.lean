import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPairLat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat.PairLatLattice

variable {E : Type} [Field E] [NumberField E]

theorem scLat_isLattice {n : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.scLat 𝔞 Λ) := by
  have hinv : 𝔞⁻¹ ≠ 0 := inv_ne_zero h𝔞
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hinv)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have hb' : b ∈ 𝔞⁻¹ := hb
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_, ?_⟩
  ·
    let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
      (LinearMap.lsmul E (Fin n → E) b⁻¹).restrictScalars (𝓞 E)
    have hle : GlobalTheory.SkewLat.scLat 𝔞 Λ ≤ Λ.map f := by
      intro y hy
      refine ⟨b • y, hy b hb', ?_⟩
      simp [f, smul_smul, mul_inv_cancel₀ hb0]
    exact Submodule.FG.of_le (Submodule.FG.map f hΛ.fg) hle
  ·
    have hmem : ∀ y ∈ Λ, a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
      intro y hy c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact Λ.smul_mem r hy
    rw [eq_top_iff, ← hΛ.span_eq_top]
    refine Submodule.span_le.mpr fun y hy => ?_
    have h1 : a • y ∈ Submodule.span E (GlobalTheory.SkewLat.scLat 𝔞 Λ : Set (Fin n → E)) :=
      Submodule.subset_span (hmem y hy)
    have h2 := Submodule.smul_mem _ a⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h2

theorem prod_span_eq_top {a b : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) :
    Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E))) = ⊤ := by
  set S := Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set ((Fin a → E) × (Fin b → E)))
  have hl : ∀ x : Fin a → E, (x, 0) ∈ S := by
    have : Submodule.span E (M : Set (Fin a → E)) ≤ S.comap (LinearMap.inl E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show (m, (0 : Fin b → E)) ∈ M.prod N from ⟨hm, N.zero_mem⟩)
    intro x
    have hx : x ∈ Submodule.span E (M : Set (Fin a → E)) := by rw [hM.span_eq_top]; trivial
    exact this hx
  have hr : ∀ y : Fin b → E, (0, y) ∈ S := by
    have : Submodule.span E (N : Set (Fin b → E)) ≤ S.comap (LinearMap.inr E (Fin a → E) (Fin b → E)) := by
      refine Submodule.span_le.mpr fun m hm => ?_
      exact Submodule.subset_span (show ((0 : Fin a → E), m) ∈ M.prod N from ⟨M.zero_mem, hm⟩)
    intro y
    have hy : y ∈ Submodule.span E (N : Set (Fin b → E)) := by rw [hN.span_eq_top]; trivial
    exact this hy
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have := S.add_mem (hl x) (hr y)
  simpa using this

theorem pairLat_isLattice {a b d : ℕ} {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsLattice E M) (hN : Submodule.IsLattice E N) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat M N e) := by
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  have hφ : GlobalTheory.SkewLat.pairLat M N e = (M.prod N).map (φ.symm.restrictScalars (𝓞 E)).toLinearMap := by
    ext x
    rw [Submodule.mem_map_equiv, GlobalTheory.SkewLat.mem_pairLat]
    rfl
  rw [hφ]
  refine ⟨Submodule.FG.map _ (Submodule.FG.prod hM.fg hN.fg), ?_⟩
  rw [Submodule.map_coe]
  have : ⇑(φ.symm.restrictScalars (𝓞 E)).toLinearMap = ⇑φ.symm.toLinearMap := rfl
  rw [this, Submodule.span_image, prod_span_eq_top hM hN, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr φ.symm.surjective

end GlobalTheory.SkewLat.PairLatLattice

open GlobalTheory.SkewLat.PairLatLattice in
theorem GlobalTheory.SkewLat.pairLat_scLat_isLattice : ∀ {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 →
    ∀ {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)}, Submodule.IsLattice E ΛA →
    Submodule.IsLattice E ΛB → ∀ (e : Fin a ⊕ Fin b ≃ Fin d),
    Submodule.IsLattice E (GlobalTheory.SkewLat.pairLat (GlobalTheory.SkewLat.scLat 𝔞 ΛA) (GlobalTheory.SkewLat.scLat 𝔞 ΛB) e) := by
  intro E _ _ a b d 𝔞 h𝔞 ΛA ΛB hA hB e
  exact pairLat_isLattice (scLat_isLattice h𝔞 hA) (scLat_isLattice h𝔞 hB) e
