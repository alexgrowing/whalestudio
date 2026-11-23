import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ChosenEqOfAllRules

noncomputable section

namespace GlobalTheory.SupLawProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev FT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

abbrev pn (σ : c.F →+* ℂ) (fσ : FrPt Xo c (CAt σ) → Ix Dw → ℝ) (e : Ix Dw → ℕ) (f : Rul Xo c)
    (y : FrPt Xo c (CAt σ)) : ℝ :=
  ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ fσ e f y

theorem evR_of_not_ft {S : Type} [CommRing S] [Algebra c.F S] (f : Rul Xo c) (y : FrPt Xo c S) (hy : ¬ FT y) :
    evR Xo c f y = 0 := by
  unfold evR evalAt; rw [dif_neg hy]

theorem evR_one {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (hy : FT y) :
    evR Xo c 1 y = 1 := evalAt_one _ _ y hy

theorem evR_map (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FT y₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) :
    evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FT y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

theorem ex_zero (i : Ix Dw) : ex Dw 0 0 i = 0 := by cases i <;> rfl

theorem one_mem_sec : (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  simp [wchar, ex_zero]

theorem cabs_one (σ : c.F →+* ℂ) : cabs (1 : CAt σ) = 1 := norm_one (α := ℂ)
theorem cabs_zero (σ : c.F →+* ℂ) : cabs (0 : CAt σ) = 0 := norm_zero (E := ℂ)

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem fromTest_iff_of_valAtCx (hcx : ValAtCx h yP) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    FT (genFr h Z) ↔ FT (yP Z P) := by
  have h1 := hcx Z P 0 0 1 one_mem_sec
  unfold evC at h1
  constructor
  · intro hg
    by_contra hy
    rw [evR_one _ hg, evR_of_not_ft _ _ hy, map_one, norm_one, cabs_zero] at h1
    exact one_ne_zero h1
  · intro hy
    by_contra hg
    rw [evR_one _ hy, evR_of_not_ft _ _ hg, map_zero, norm_zero, cabs_one] at h1
    exact zero_ne_one h1

theorem fromTest_of_nzSome {f : Rul Xo c} (hN : NZSome h f) : ∃ Z, evC h Z f ≠ 0 ∧ FT (genFr h Z) := by
  obtain ⟨Z, hZ⟩ := hN
  refine ⟨Z, hZ, ?_⟩
  by_contra hg
  exact hZ (evR_of_not_ft _ _ hg)

theorem nzSome_one_iff : NZSome h (1 : Rul Xo c) ↔ ∃ Z, FT (genFr h Z) := by
  constructor
  · intro hN
    obtain ⟨Z, _, hZ⟩ := fromTest_of_nzSome hN
    exact ⟨Z, hZ⟩
  · rintro ⟨Z, hZ⟩
    refine ⟨Z, ?_⟩
    unfold evC
    rw [evR_one _ hZ]
    exact one_ne_zero

theorem not_nzSome_zero : ¬ NZSome h (0 : Rul Xo c) := by
  rintro ⟨Z, hZ⟩
  exact hZ (evalAt_zero _ _ _)

theorem laws_of_no_comp (hne : IsEmpty (Comp Xo c)) (f : Rul Xo c) :
    PTNe Xo c ∧ ValAtCx h yP ∧ ¬ NZSome h f :=
  ⟨fun Z => hne.elim Z, fun Z => hne.elim Z, fun ⟨Z, _⟩ => hne.elim Z⟩

theorem supR_pos [Fintype (Comp Xo c)] (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f)
    (hN : NZSome h f) (σ : c.F →+* ℂ) : 0 < supR Xo c fn σ a n f := by
  obtain ⟨Z, hZ⟩ := hN
  obtain ⟨P, hP⟩ := hPT Z σ
  have h1 := nrmC_valC_le hcx hS hB Z P
  have hP' : sgOf P = σ := hP
  rw [hP'] at h1
  exact lt_of_lt_of_le (nrmC_pos fn (yP Z) hfn P (valC_mem h a n f Z) (valC_ne_zero hZ)) h1

theorem pn_one_le (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : pn σ (fn σ) (ex Dw 0 0) 1 y ≤ 1 := by
  show cabs (evR Xo c 1 y) * ∏ i, |fn σ y i|⁻¹ ^ ex Dw 0 0 i ≤ 1
  simp only [ex_zero, pow_zero, Finset.prod_const_one, mul_one]
  by_cases hy : FT y
  · rw [evR_one _ hy, cabs_one]
  · rw [evR_of_not_ft _ _ hy, cabs_zero]; exact zero_le_one

theorem supBdd_one : SupBdd Xo c fn 0 0 1 := fun σ =>
  ⟨1, Set.forall_mem_range.2 fun y => pn_one_le σ y⟩

theorem supR_one_le (σ : c.F →+* ℂ) : supR Xo c fn σ 0 0 1 ≤ 1 :=
  Real.iSup_le (fun y => pn_one_le σ y) zero_le_one

section Conj

variable (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
  (σ : c.F →+* ℂ) (cj : FrPt Xo c (CAt σ) → FrPt Xo c (CAt ((starRingEnd ℂ).comp σ)))
  (hcj : ∀ y, FrMap (SupNormExample.conjAt σ) y (cj y))
  (htr : ∀ y i, |fn _ (cj y) i| = |fn σ y i|) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
  (hS : f ∈ sec Xo c a n)

include hWD hcj htr hS in
theorem pn_le_conj (y : FrPt Xo c (CAt σ)) :
    pn σ (fn σ) (ex Dw a n) f y ≤ pn _ (fn _) (ex Dw a n) f (cj y) := by
  by_cases hy : FT y
  · exact (SupNormExample.ptNorm_conj _ _ σ (fn σ) (fn _) (ex Dw a n) f y (cj y)
      (evR_map hWD f hS.1 (SupNormExample.conjAt σ) y hy (cj y) (hcj y)) (htr y)).ge
  · refine le_trans (le_of_eq ?_) (ptNorm_nonneg _ _ _ _ _ _ _)
    show cabs (evR Xo c f y) * _ = 0
    rw [evR_of_not_ft _ _ hy, cabs_zero, zero_mul]

include hWD hcj htr hS in
theorem bdd_of_conj
    (hB : BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn _)
      (ex Dw a n) f) :
    BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f := by
  obtain ⟨b, hb⟩ := hB
  exact ⟨b, Set.forall_mem_range.2 fun y => (pn_le_conj hWD σ cj hcj htr hS y).trans (hb ⟨cj y, rfl⟩)⟩

include hWD hcj htr hS in
theorem supR_le_conj
    (hB : BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn _)
      (ex Dw a n) f) :
    supR Xo c fn σ a n f ≤ supR Xo c fn ((starRingEnd ℂ).comp σ) a n f :=
  Real.iSup_le (fun y => (pn_le_conj hWD σ cj hcj htr hS y).trans (le_ciSup hB (cj y)))
    (Real.iSup_nonneg fun _ => ptNorm_nonneg _ _ _ _ _ _ _)

end Conj

theorem supBdd_of_fn_zero (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : n ≠ 0) (f : Rul Xo c) :
    SupBdd Xo c (fun _ _ _ => 0) a n f ∧ ∀ σ, supR Xo c (fun _ _ _ => 0) σ a n f = 0 :=
  ⟨fun σ => (SupNormExample.bddAt_of_fnorm_zero _ _ σ (ex Dw a n) none hn f).1,
   fun σ => (SupNormExample.bddAt_of_fnorm_zero _ _ σ (ex Dw a n) none hn f).2⟩

theorem exists_fn_small (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : n ≠ 0) (f : Rul Xo c) :
    ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ,
      FnNe Xo c fn ∧ SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f ≤ 1 := by
  choose g hg using fun σ : c.F →+* ℂ =>
    SupNormExample.exists_fnorm_small (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ
      (ex Dw a n) none hn f
  exact ⟨g, fun σ y i => ((hg σ).1 y i).ne', fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩

end GlobalTheory.SupLawProbe
