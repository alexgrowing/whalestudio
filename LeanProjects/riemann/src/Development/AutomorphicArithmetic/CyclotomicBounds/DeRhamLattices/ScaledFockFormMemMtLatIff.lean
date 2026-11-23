import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodInjectiveRangeEqValSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemLNabIffCoefficientsInNablaLattice
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemMtLatOfCoefficientsMemCoefLat
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

theorem _root_.UpperTheory.KN.scaled_fock_form_mem_mtLat_iff :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) ↔
        ∃ a : D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) → 𝓞 D.what₂.LL, D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m = ∑ v ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen, D.what₂.embLL (a v : D.what₂.LL) • v := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs m
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hs
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨e, he, hO, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  obtain ⟨x, rfl⟩ := e.surjective m
  have hN := UpperTheory.KN.mem_lNab_iff_coefficients_in_nabla_lattice D X j (Y.tupT (D.what₂.muTw w)) gramR c0R c0L hft x
  have hC := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hF
  have hI := (UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu).1
  have hv : ∀ h, (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x))) h =
      κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u') ((X.R.B.jL j (Y.tupT (D.what₂.muTw w))
        (GlobalTheory.Mem.R3.liftForm X.A3.A X.F.lv2.P0 X.F.lv2.ψ0 j (Y.tupT (D.what₂.muTw w)) x)) h) := fun h => by
    rw [Pi.smul_apply, fockOf_apply, he x]
  refine Iff.trans ?_ (hN.symm.trans (hO.2 x))
  constructor
  · intro hm a
    obtain ⟨F, hF1, hF2⟩ := (hC _ _).1 (((Base.mem_mtLat _ _ _ _).1 hm).2 ((X.R.B.L j (Y.tupT (D.what₂.muTw w))).pres.y a))
    rw [hv] at hF2
    exact ⟨F, hF1, hI (smul_right_injective _ (inv_ne_zero hκ) hF2)⟩
  · intro hm
    refine UpperTheory.KN.mem_mtLat_of_coefficients_mem_coefLat D X X0 Y S YS Z c w j H ι hι _ (Submodule.smul_mem _ _ ?_) fun a => ?_
    · rw [← (GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu).2]
      exact LinearMap.mem_range_self _ _
    · obtain ⟨F, hF1, hF2⟩ := hm a
      exact (hC _ _).2 ⟨F, hF1, by rw [hv, hF2]⟩
