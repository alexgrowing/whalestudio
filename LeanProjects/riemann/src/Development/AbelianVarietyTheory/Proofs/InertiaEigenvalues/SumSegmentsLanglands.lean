import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

namespace GlobalTheory.NuShift

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpTw (x y : WD h) (s : ℝ) : (x.lpTw s).lpChar y = (x.lpChar y).lpTw s := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpTw_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · simp only [WDRep.tensor_ρ, WDRep.tw_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left]
  · rfl

theorem lpTw_lpZero (s : ℝ) : (WD.lpZero h).lpTw s = WD.lpZero h := by
  rw [WD.lpZero, WD.lpTw_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem sumList_lpTw (l : List (WD h)) (s : ℝ) :
    sumList (l.map fun x => x.lpTw s) = (sumList l).lpTw s := by
  induction l with
  | nil => exact (lpTw_lpZero s).symm
  | cons x l ih =>
    show WD.lpSum _ (sumList _) = (WD.lpSum x (sumList l)).lpTw s
    rw [ih, WD.lpTw_sum]

end GlobalTheory.NuShift

namespace GlobalTheory

open GlobalTheory.NuShift

theorem lpSum_segments_nu : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)) =
        (sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [← sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [L.nu_eq, WD.lpTw_add, add_comm, ← WD.lpTw_add, lpChar_lpTw]
  rfl

end GlobalTheory
