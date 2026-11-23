import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AgreementAtAlmostAllSplitPrimes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharCmEqOneOfTrivialDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyResidueDegreeOnePrimeMovedByGaloisStatement

noncomputable section

namespace GlobalTheory.HeckeSplitRow

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host

def HeckeCharTie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) : Prop :=
  ∃ e : A.CG 1 → HChar H.E, Function.Injective e ∧
    (∀ π w, A.unr (A.locG π w) ↔ (e π).UnrAt w) ∧
    ∀ π w, (e π).UnrAt w → A.frobEig (A.locG π w) = {(((e π).val w)⁻¹ : ℂˣ).1}

theorem heckeCharTie_of_tied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : NCharTied D C nch Tp) : HeckeCharTie D.nd D.naut :=
  ⟨fun π => (T.e1 π).1, fun _ _ h => T.e1.injective (Subtype.ext h), T.unr_iff, T.frob⟩

theorem loc_eq_one {L : Type} [Field L] [NumberField L] (χ : HChar L) (v : HeightOneSpectrum (𝓞 L))
    (hu : χ.UnrAt v) (hv : χ.val v = 1) : χ.loc v = 1 := by
  ext x : 1
  set p := atFin v (unif v) with hp
  have hpv : Valued.v (p : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  set n : ℤ := WithZero.log (Valued.v (x : v.adicCompletion L)) with hn
  have hxn : Valued.v (x : v.adicCompletion L) = WithZero.exp n := (WithZero.exp_log hx0).symm
  have hunit : IsUnitAt v (x * p ^ n) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hpv, hxn, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hu _ hunit
  have hp1 : χ.loc v p = 1 := hv
  rw [map_mul, map_zpow, hp1, one_zpow, mul_one] at h1
  exact h1

theorem complexConj_eq {R : Ranks} (H : Host R) [IsCMField H.E] (z : H.E) :
    IsCMField.complexConj H.E z = H.conj z := by
  apply H.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj]
  exact (H.toHostAx.conjE_apply H.φ₀ z).symm

theorem eq_one_of_split {R : Ranks} (H : Host R) (ν : HChar H.E)
    (h : ∀ᶠ w in Filter.cofinite, IsSplitPl H w → ν.UnrAt w ∧ ν.val w = 1) : ν = 1 := by
  have : IsCMField H.E := H.isCMField_hostE
  apply Subtype.ext
  refine GlobalTheory.T.heckeChar_cm_eq_one_of_trivial_degree_one (maximalRealSubfield H.E) H.E ν.1 ν.2 ?_
  filter_upwards [h, GlobalTheory.T.eventually_residueDegreeOne_prime_moved_by_galois (maximalRealSubfield H.E) H.E (IsCMField.complexConj H.E)
    (IsCMField.complexConj_ne_one H.E)] with w hw hs hd
  obtain ⟨x, hx, hy⟩ := hs hd
  have hsp : IsSplitPl H w := ⟨x, hx, fun y hyx => hy y (by rw [complexConj_eq]; exact hyx)⟩
  exact (GlobalTheory.HeckeSplit.trivAt_iff H.E ν w).2 (loc_eq_one ν w (hw hsp).1 (hw hsp).2)

theorem heckeCharEqOfSplit_of_tie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N), HeckeCharTie N A → GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit N A := by
  rintro R H what₂ N A ⟨e, hinj, hunr, hfrob⟩ χ χ' hag
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff] at hag
  apply hinj
  rw [← mul_inv_eq_one]
  apply eq_one_of_split H
  filter_upwards [hag, A.locG_unr_ae χ, A.locG_unr_ae χ'] with w hw h1 h2 hs
  have u1 := (hunr χ w).1 h1
  have u2 := (hunr χ' w).1 h2
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
  · have hf := hfrob χ w u1
    rw [hw hs, hfrob χ' w u2, Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
    rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]

theorem heckeSplitOne_of_tie {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) (h : HeckeCharTie N A) : GlobalTheory.ThetaExh.HeckeSplitOne N A := fun χ χ' hw =>
  heckeCharEqOfSplit_of_tie R H what₂ N A h χ χ' ((GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.agreeAtAlmostAllSplit_iff A χ χ').2 hw)

theorem heckeCharEqOfSplit_of_tied {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : NCharTied D C nch Tp) : GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit D.nd D.naut :=
  heckeCharEqOfSplit_of_tie _ _ _ _ _ (heckeCharTie_of_tied T)

end GlobalTheory.HeckeSplitRow
