import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjChar

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

theorem val_unif (P : HeightOneSpectrum (𝓞 E)) : P.valuation E ((unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) :=
  (P.valuedAdicCompletion_eq_valuation' _).symm.trans (unif_spec P)

theorem exists_unit_part (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    ∃ u : Eˣ, P.valuation E (u : E) = 1 ∧ k = unif P ^ ordF P k * u := by
  refine ⟨(unif P ^ ordF P k)⁻¹ * k, ?_, by rw [mul_inv_cancel_left]⟩
  have h0 : P.valuation E (k : E) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, val_unif,
    ← WithZero.exp_zsmul, ← WithZero.exp_neg, ordF]
  conv_lhs => rw [← WithZero.exp_log h0, WithZero.log_exp, ← WithZero.exp_add]
  simp

theorem twVal_half (χ : HChar E) (P : HeightOneSpectrum (𝓞 E)) (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1)
    (k : Eˣ) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal χ (1 / 2) P k =
      (((χ.locK P (unif P) : ℂˣ) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)) ^ ordF P k := by
  obtain ⟨u, hu, hk⟩ := exists_unit_part P k
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.twVal
  generalize ordF P k = n at hk ⊢
  rw [hk, map_mul, h u hu, mul_one, map_zpow, Units.val_zpow_eq_zpow_val, mul_zpow]
  congr 1
  have hN : (0 : ℝ) ≤ (Nat.card (kP P) : ℕ) := Nat.cast_nonneg _
  rw [show Ideal.absNorm P.asIdeal = Nat.card (kP P) from rfl, ← Complex.ofReal_zpow, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hN, ← Real.rpow_intCast, ← Real.rpow_mul hN, Complex.ofReal_cpow hN]
  push_cast
  congr 1
  ring

end General

theorem locK_eq_one {D : D7} {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (hc : ChrEq c χ) (hu : UnramEverywhere D c)
    (P : Pl D.host.E) (u : D.host.Eˣ) (h : P.valuation D.host.E (u : D.host.E) = 1) : χ.locK P u = 1 := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, hinf, hP, hQ⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  have key : ∀ k : D.host.E, P.valuation D.host.E k = 1 → finPart D (locE D e k) ∈ intAE D := by
    intro k hk
    rw [h2]
    intro Q
    have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := h1 k
    have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (ι (finPart D (incA D k)) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
    rw [h5, h4]
    change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
    by_cases hQP : Q = P
    · subst hQP
      rw [hP, one_mul, add_sub_cancel]
      exact ((Q.valuedAdicCompletion_eq_valuation' k).trans hk).le
    · rw [hQ Q hQP, zero_mul, add_zero, map_one]
  have hinv : (((locU he.1 u)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((u⁻¹ : D.host.Eˣ) : D.host.E) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [locU_val, locE_mul_locE he.1]
    simp [locE]
  have h6 := hu (locU he.1 u) (by
    rw [locU_val, locE, RingHom.map_add, RingHom.map_one, RingHom.map_mul, hinf, zero_mul, add_zero])
    (key _ h) (by
      rw [hinv]
      refine key _ ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one])
  have h7 := hc.2 P e he u (locU he.1 u) rfl
  rw [h6] at h7
  exact Units.ext h7.symm

theorem exists_galConj_eta : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsEmbOverK D σ s → ∀ η' : (AE D)ˣ →* Circle, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ R.eta η' → ∃ ηH : Formalism.L2.Host.HChar D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.IsGalConj s (1 / 2) R.C.eta ηH ∧ ChrEq η' ηH := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR σ s hσ η' hη
  obtain ⟨ηH, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D η' hη.1
  refine ⟨ηH, fun P k => ?_, hH⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
  have h0 : ∀ u : D.host.Eˣ, P.valuation D.host.E (u : D.host.E) = 1 → R.C.eta.locK P u = 1 := fun u hu =>
    R.C.isEta.unr P _ ((P.valuedAdicCompletion_eq_valuation' (u : D.host.E)).trans hu)
  rw [twVal_half _ P (locK_eq_one hH hη.2.1 P), twVal_half _ P h0, map_zpow₀,
    ← hH.2 P e he _ (locU he.1 (unif P)) rfl, ← hR.lev.eta.2 P e he _ (locU he.1 (unif P)) rfl, ← hy1, ← hy2, hσ.1]

end GlobalTheory.EtaConjChar
