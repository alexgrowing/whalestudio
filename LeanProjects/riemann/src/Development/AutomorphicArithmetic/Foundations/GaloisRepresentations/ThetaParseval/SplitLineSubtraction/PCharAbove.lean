import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charAbove_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.HeckeLAdicCharacterDeRham → GlobalTheory.Published.AlgebraicCharacterWD → PstOfDR → ContLeft → CharAbove := by
  intro H hD hW hP hC E Ω _ _ _ _ _ l _ ι art ha χ n μ h1 h2 h3 w hu P AI hT A h O _ _ _ Bw hj
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have d := hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj
  have hc : Continuous ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    ((hC (G E Ω) (Qbar l) 0 0).2.2.2 μ h2).comp continuous_subtype_val
  have hr := hP l P AI hT E Ω A O Bw 1 _ hc d.1
  have e := hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha'
  have hun := (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu
  refine ⟨?_, d.1, d.2, fun g => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, e, GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
    exact hun
  · have hv : (χ.loc w (a g) : ℂ) = ((χ.val w : ℂˣ) : ℂ) ^ (-deg g) := by
      have ho : GlobalTheory.SmGL.ord (w.adicCompletion E) (atFin w (unif w)) = 1 := by
        rw [GlobalTheory.SmGL.SphCompletion.ord_completion, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _ from unif_spec w]
        simp
      have h1 : ∀ x : (w.adicCompletion E)ˣ, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
        have h0 : GlobalTheory.SmGL.ord (w.adicCompletion E) (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 0 := by
          have hz : ∀ (y : (w.adicCompletion E)ˣ), GlobalTheory.SmGL.unrChar (w.adicCompletion E) (Units.mk0 2 two_ne_zero) y =
              (Units.mk0 (2:ℂ) two_ne_zero) ^ GlobalTheory.SmGL.ord _ y := fun _ => rfl
          let φ : (w.adicCompletion E)ˣ →* Multiplicative ℤ := MonoidHom.mk' (fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord _ y))
            fun y z => by rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
          have : φ (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow]
            simp [φ, ho, ← ofAdd_zsmul]
          exact this
        have := hun _ ((GlobalTheory.SmGL.ord_eq_zero_iff).1 h0)
        rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
        exact this
      rw [h1, ha'.ord_eq, Units.val_zpow_eq_zpow_val]
    rw [e, WD.charPol_eq_prod, GlobalTheory.LocLanglands.eig_lpOfChar]
    simp [unrPol, hv]
