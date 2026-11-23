import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexPrincipalLevelEqRealisationPrincipalLevel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharValuesMemCoeffFieldRange
import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem exists_delta_root {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (z : (Formalism.L2.Theta.AE D)ˣ) : ∃ a : FractionRing (D.ntw.O i),
      ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) ∧ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_, _, hn, ?_⟩
  · rw [hρ.delta i j b]
    exact (GlobalTheory.SeriesTie.charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm
  · rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, map_one]

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem valC_geoHecke {P : PlE D.host} {k : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P))
    (s : T0.Q.c.F) {f g : T0.R ((j : ℕ) + 1)} (hf : f ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n)
    (hfg : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s f g)
    (z : FrC YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z → FrC YS iC b ((j : ℕ) + 1))
    (hq : ∀ C, IsHkQuot P.asIdeal (charAt P) k z C (quot C)) :
    valC z g = embC YS iC b s * ∑ᶠ C, valC (quot C) f := by
  have hrel := hfg (PAt (embC YS iC b)) z
  have hL : GlobalTheory.Reg.EvLaws (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ _ _).1
  have hfun := GlobalTheory.HeckePointLaw.heckePointLaws.2.2.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP
  have hterm : ∀ C, hkTerm (fun S _ _ => FrPt (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := T0.Q.Xo ((j : ℕ) + 1)) P.asIdeal (charAt P) k Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P)) Ω y C z)
      f z C = valC (quot C) f := by
    intro C
    have hex : ∃ w, hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P))
        (PAt (embC YS iC b)) z C w := ⟨quot C, hq C⟩
    unfold hkTerm
    rw [dif_pos hex]
    have hm := hfun (PAt (embC YS iC b)) z C _ _ hex.choose_spec (hq C)
    exact (GlobalTheory.Reg.PChartModel.evR_map hL hf.1 (AlgHom.id _ _) hm).symm
  change toCp _ (evR (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c g z) = _
  unfold evR
  rw [hrel, map_mul, toCp_algebraMap]
  congr 1
  unfold hkVal
  exact finsum_congr hterm

end Side

end GlobalTheory.GeoTie
