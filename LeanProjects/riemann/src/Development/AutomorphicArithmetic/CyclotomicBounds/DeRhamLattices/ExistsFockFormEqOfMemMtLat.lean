import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTopStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodInjectiveRangeEqValSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemRangeSemilinearOfValuesMemRange
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff
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

theorem _root_.UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι), ∃ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc F hF
  have hkey := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hscale⟩ := hsc
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  have hcoef := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hscale
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨hio, -⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨-, -, -, hspan⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  have hli : LinearIndependent ℂ fun i => (c0L j (bVV D.what₂.LL (FWT.lamV D j) i) : (X.R.cV j).W) := (hft.mapL j).2.1
  let ev := (X.R.HV j (Y.tupT (D.what₂.muTw w))).e ∘ₗ formOf Y (used_of_tw H.tw) j
  have hev : ∀ x h, fockOf Y (used_of_tw H.tw) j u' x h = X.R.ioP j (PiTensorProduct.tprod ℂ u') (ev x h) := fun _ _ => rfl
  have hevinj : Function.Injective ev := fun x y hxy => hinj (funext fun h => by rw [hev, hev, hxy])
  have hval : ∀ g, κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' g ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) →
      ∀ h, ev g h ∈ Set.range (c0L j) := by
    intro g hg h
    obtain ⟨G, -, hG⟩ := (hcoef h _).1 (((Base.mem_mtLat _ _ _ _).1 hg).2 h)
    rw [Pi.smul_apply, hev] at hG
    exact ⟨G, (hio (smul_right_injective _ (inv_ne_zero hκ) hG)).symm⟩
  have hsp : Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} = ⊤ :=
    GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)
  have hall : ∀ m h, ev (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) h ∈ Set.range (c0L j) := by
    intro m h
    have hm : m ∈ Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} := by
      rw [hsp]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine hval _ ((hkey x).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x then 1 else 0, ?_⟩) h
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_coe.1 hx)]
      · simp
      · intro v _ hv
        simp [hv]
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, map_add, Pi.add_apply, ← ha, ← hb]; rfl⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨s • a, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply, ← ha]; rfl⟩
  have hF1 : κ • F ∈ LinearMap.range (fockOf Y (used_of_tw H.tw) j u') := by
    rw [hrange]
    exact Submodule.smul_mem _ _ ((Base.mem_mtLat _ _ _ _).1 hF).1
  obtain ⟨f, hf⟩ := hF1
  have hFf : F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' f := by rw [hf, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨m, hm⟩ := UpperTheory.KN.mem_range_semilinear_of_values_mem_range _ _ _ _ _ _ _ D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) ev (c0L j)
    (bVV D.what₂.LL (FWT.lamV D j)) hspan hevinj hli hall f (hval f (hFf ▸ hF))
  exact ⟨m, by rw [hm]; exact hFf⟩
