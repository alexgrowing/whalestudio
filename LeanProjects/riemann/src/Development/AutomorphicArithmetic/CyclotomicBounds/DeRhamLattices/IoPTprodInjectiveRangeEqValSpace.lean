import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMapStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      Function.Injective (X.R.ioP j (PiTensorProduct.tprod ℂ u)) ∧ LinearMap.range (X.R.ioP j (PiTensorProduct.tprod ℂ u)) = (baseOf Z c w j).valSpace := by
  intro D X X0 Y S YS Z c w j H ι hι u hu
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hG : (baseOf Z c w j).Good := Z.good.base (c.twI w) j (c.sd w)
  have hBo : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hio : Formalism.IndefR.FWT.IoExt X.R.toRealDat :=
    GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hcV : (X.R.cV j).Is := hC.models.cV j
  obtain ⟨u', w₀, hu', -, hw⟩ := Formalism.IndefR.FWT.IsChosenExtremalVector.io _ (Z.vec j) hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw
  have hT := Scale.io_act hC.lev hC.thP hG hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  have hval : ∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) x ∈ (baseOf Z c w j).valSpace := by
    intro x
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS).comap
          (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact (h ▸ Submodule.mem_top : x ∈ (harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u)))
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rcases hcV.2.2.2.2 (LinearMap.ker (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        have h0 : X.R.ioP j (PiTensorProduct.tprod ℂ u) w = 0 := hw'
        rw [LinearMap.mem_ker, hT a ha, h0, map_zero]) with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · have h0 : w₀ ∈ LinearMap.ker (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker, hw] at h0
      exact absurd h0 hΔ0
  · rintro _ ⟨x, rfl⟩
    exact hval x
  · obtain ⟨u1, cc, κ, hu1, -, hκ0, hv, hκ, -⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
    have e : u1 = u := funext fun ρ => Subtype.ext ((hu1 ρ).trans (hu ρ).symm)
    subst e
    intro P hP
    obtain ⟨x, hx, -⟩ := GlobalTheory.CoefLatConj.existsUnique_eq (X.R.ioP j (PiTensorProduct.tprod ℂ u1) ∘ₗ cc) hG hBo.lam hκ0 hv hκ P hP
    exact ⟨cc x, hx.symm⟩
