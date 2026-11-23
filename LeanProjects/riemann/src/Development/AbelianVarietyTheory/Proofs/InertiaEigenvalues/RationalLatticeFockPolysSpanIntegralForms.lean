import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsFockFormEqOfMemMtLat
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
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

theorem _root_.GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
  (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) =
    Submodule.span (intLL D) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1)) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  classical
  have key := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  have hrat := UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
  obtain ⟨e, -, htie, -⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · intro F hF
    obtain ⟨m, rfl⟩ := hrat F hF
    obtain ⟨a, ha⟩ := (key m).1 hF
    rw [ha, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [map_smul, smul_comm]
    refine Submodule.smul_mem _ (⟨D.what₂.embLL (a v : D.what₂.LL), a v, rfl⟩ : intLL D) (Submodule.subset_span ?_)
    obtain ⟨x, hx⟩ := htie.1 v hv
    have hx' : D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) = v := hx
    exact ⟨e x, by show D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (e x) ∈ (D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen; rw [hx']; exact hv, by simp only [hx']⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine (key m).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m)]
    · simp
    · intro v _ hv
      simp [hv]
    · exact fun h => absurd hm h
