import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LocalLanglandsExistence₂

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_place (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ∃ A : ValuationSubring (AlgebraicClosure E), IsPlaceOver A w :=
  ⟨_, isPlaceOver_placeOf _ w⟩

theorem localLanglandsExists_of_localLanglandsGL (H : GlobalTheory.Published.LocalLanglandsGL) : GlobalTheory.Published.LocalLanglandsExists :=
  fun E Ω _ _ _ _ _ A w h => let ⟨rc, hrc, _⟩ := H.1 E Ω A w h; ⟨rc, hrc.toLit⟩

theorem eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero h := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem not_isIrrWD_lpZero : ¬ IsIrrWD (WD.lpZero h) := by
  rintro ⟨n, a, ha, hi⟩
  have h0 := congrArg WD.lpDim ha
  obtain rfl : n = 0 := by simpa [WD.lpZero] using h0
  have : Nontrivial (Subrepresentation a.ρ) := hi.toNontrivial
  obtain ⟨S, T, hST⟩ := exists_pair_ne (Subrepresentation a.ρ)
  exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem eps_tensor_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ' : ψ ≠ 1) (x y : WD h) (hy : y.lpDim = 0) : ε E w h ψ (x.lpChar y) = 1 := by
  have h1 : (x.lpChar y).lpDim = 0 := by
    obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    obtain rfl : m = 0 := by simpa using hy
    simp
  have h2 : ((x.lpChar y).lpSum (x.lpChar y)).lpDim = 0 := by
    obtain ⟨n, a, ha⟩ := (x.lpChar y).exists_rep
    rw [← ha] at h1 ⊢
    obtain rfl : n = 0 := by simpa using h1
    simp
  have h3 := hε.add E w h ψ hψ hψ' (x.lpChar y) (x.lpChar y)
  rw [(eq_lpZero h2).trans (eq_lpZero h1).symm] at h3
  exact (mul_eq_left.1 h3.symm)

theorem segSum_single (rc : IrrGL (w.adicCompletion E) → WD h) (ρ : IrrGL (w.adicCompletion E)) (hρ : ρ.IsCusp) :
    segSum rc [Segment.single ρ hρ] = rc ρ := by
  obtain ⟨n, a, ha⟩ := (rc ρ).exists_rep
  show ((((rc ρ).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h)) = rc ρ
  rw [← ha, WD.lpTw_mk, WD.lpSp, WD.lpChar_mk, WD.lpZero, WD.lpSum_mk]
  refine WD.sound ⟨(LinearEquiv.prodUnique).trans ((TensorProduct.congr (.refl ℂ _)
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ _)), fun σ v => ?_, fun v => ?_⟩
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (TensorProduct.map _ _ v)) = a.ρ σ ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [WDRep.spEig, coe_qPow]
    | add x y hx hy => simp only [map_add, hx, hy]
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (((a.tw ((((1 : ℕ) : ℝ) - 1) / 2)).tensor (WDRep.sp h 1)).N v)) = a.N ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [shiftEnd_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem frobEig_unr {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecLit h rc) (c : ℂˣ)
    (hc : IsSmoothChar (SmGL.unrChar (w.adicCompletion E) c)) :
    (rc (.ofChar _ hc)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.one]
  have : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) (ha.smooth hc) =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
    simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]
  rw [this, WD.frobEig_diag]
  rfl

theorem not_const (y : WD h) : ¬ IsRecLit h fun _ => y := by
  rintro ⟨a, ha, ε, -, H⟩
  obtain ⟨_, h0⟩ := H.bij.2 (WD.lpSp h 0)
  obtain ⟨_, h1⟩ := H.bij.2 (WD.lpSp h 1)
  have := congrArg WD.lpDim (h0.symm.trans h1)
  simp at this

end GlobalTheory.LocLanglands.LocalLanglandsExistence₂

end
