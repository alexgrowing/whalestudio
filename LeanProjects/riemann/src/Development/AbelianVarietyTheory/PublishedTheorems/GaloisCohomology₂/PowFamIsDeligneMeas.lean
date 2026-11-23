import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLocalLanglands

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.MeasTest

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {t : ℝ}

theorem tate_unique {e e' : ℂ} (h : IsTateMeas ψ t χ e) (h' : IsTateMeas ψ t χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  have h2 := valuation_eq_iff_ord.1 h1
  rw [IsShellReps, h2, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, h2]

theorem tate_unram {c : kˣ} (hψ : HasConductor ψ c) (hχ : IsUnram χ) :
    IsTateMeas ψ t χ (((t * nabs k c : ℝ) : ℂ) * ((χ c)⁻¹ : ℂˣ)) := by
  obtain ⟨c', a, R, hc', ha, hR, he⟩ := isTateEps_of_isUnram hψ hχ
  obtain rfl := ha.unique (hasExponent_zero_iff.2 hχ)
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hψ _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hψ _).2 le_rfl))
  refine ⟨c', 0, R, hc', ha, hR, ?_⟩
  rw [he, GlobalTheory.LGrp.nabs_eq_zpow, GlobalTheory.LGrp.nabs_eq_zpow, valuation_eq_iff_ord.1 h1]
  simp

theorem tate_exists (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hχ : IsSmoothChar χ) (ht : 0 < t) :
    ∃ e : ℂˣ, IsTateMeas ψ t χ e := by
  obtain ⟨⟨e, he, -⟩, hne⟩ := existsUnique_isTateEps ψ hψ h1 χ hχ
  have h0 := hne e he
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  have hn : (0 : ℝ) < nabs k c := by
    unfold nabs; exact_mod_cast MeasureTheory.distribHaarChar_pos
  refine ⟨Units.mk0 _ (mul_ne_zero (Complex.ofReal_ne_zero.2 (mul_pos ht hn).ne') (right_ne_zero_of_mul h0)),
    c, a, R, hc, ha, hR, rfl⟩

theorem tate_scale {e : ℂ} (h : IsTateMeas ψ t χ e) (s : ℝ) : IsTateMeas ψ (s * t) χ (s * e) := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  exact ⟨c, a, R, hc, ha, hR, by push_cast; ring⟩

end Tate

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

theorem eps_unram {ε : EpsMeasFamily A} (hε : IsDeligneMeas ε) {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {t : ℝ} (ht : 0 < t) {a : Weil h →* (v.adicCompletion L)ˣ} (ha : IsLocalArtin h a)
    {c : (v.adicCompletion L)ˣ} (hc : HasConductor ψ c) {χ : (v.adicCompletion L)ˣ →* ℂˣ} (hχ : IsUnram χ) :
    (ε L v h ψ t (WD.lpOfChar h (χ.comp a) (ha.smooth (isSmoothChar_of_isUnram hχ))) : ℂ) =
      ((t * nabs _ c : ℝ) : ℂ) * ((χ c)⁻¹ : ℂˣ) :=
  tate_unique (hε.char L v h ψ hψ h1 t ht a ha χ (isSmoothChar_of_isUnram hχ)) (tate_unram hc hχ)

theorem eps_degree_zero {ε : EpsMeasFamily A} (hε : IsDeligneMeas ε) {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (x y : WD h) (hd : x.lpDim = y.lpDim) :
    ε L v h ψ t x * ε L v h ψ t' y = ε L v h ψ t y * ε L v h ψ t' x :=
  hε.ind L L v v h h (isLocalExt_self h) ψ ψ hψ h1 hψ (fun z => by simp) t t' ht ht' x y x y
    (induces_self x) (induces_self y) hd

def powFam : EpsMeasFamily A := fun _ _ _ _ _ _ _ _ t x => WD.unitOf (t : ℂ) ^ x.lpDim

theorem powFam_isDeligneMeas
    (H : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
      (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ), ¬ IsLocalArtin h a) :
    IsDeligneMeas (powFam (A := A)) where
  add L _ _ _ _ v h ψ _ _ t _ x y := by
    obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    simp [powFam, pow_add]
  scale L _ _ _ _ v h ψ _ _ t ht a ha x := by
    have h1 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have h2 : ((a * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (mul_pos ha ht).ne'
    simp only [powFam, Units.val_pow_eq_pow_val, WD.coe_unitOf h1, WD.coe_unitOf h2]
    push_cast; ring
  ind K L _ _ _ _ _ _ _ _ _ _ v v' h h' _ ψ ψ' _ _ _ _ t t' _ _ x₁ x₂ y₁ y₂ i₁ i₂ hd := by
    obtain ⟨m, n, a, b, j, rfl, rfl, hn, -⟩ := i₁
    obtain ⟨m', n', a', b', j', rfl, rfl, hn', -⟩ := i₂
    have : m = m' := by simpa using hd
    subst this
    simp [powFam, hn, hn']
  char L _ _ _ _ v h ψ _ _ t _ a ha := absurd ha (H L v h a)

theorem trivial_place : ∃ ε : EpsMeasFamily (⊤ : ValuationSubring Ω), IsDeligneMeas ε := by
  refine ⟨powFam, powFam_isDeligneMeas fun L _ _ _ _ v h _ _ => ?_⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have := (valuation_lt_one_iff' _ _).1 ((h x).2 hx)
  rcases this.2 with h0 | h0
  · exact hx0 (by simpa using h0)
  · exact h0 trivial

theorem of_localLanglands (hL : GlobalTheory.Published.LocalLanglandsGL) : GlobalTheory.Published.DeligneLocalConstants := by
  intro Ω _ A
  by_cases H : ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] (v : HeightOneSpectrum (𝓞 L))
      (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion L)ˣ), ¬ IsLocalArtin h a
  · exact ⟨powFam, powFam_isDeligneMeas H⟩
  · by_contra hn
    exact H fun L _ _ _ _ v h _ _ => hn (MeasModel.exists_of_localLanglands hL L v h).2

theorem not_powFam {L : Type} [Field L] [NumberField L] [Algebra L Ω]
    [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {ψ : AddChar (v.adicCompletion L) Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) {a : Weil h →* (v.adicCompletion L)ˣ} (ha : IsLocalArtin h a)
    {c : (v.adicCompletion L)ˣ} (hc : HasConductor ψ c) (hc1 : nabs _ c ≠ 1) : ¬ IsDeligneMeas (powFam (A := A)) := by
  intro H
  have := eps_unram H hψ h1 one_pos ha hc (χ := 1) (fun _ _ => rfl)
  simp [powFam, WD.lpOfChar, WD.coe_unitOf] at this
  exact hc1 (by exact_mod_cast this.symm)

end GlobalTheory.LocLanglands.MeasTest

end
