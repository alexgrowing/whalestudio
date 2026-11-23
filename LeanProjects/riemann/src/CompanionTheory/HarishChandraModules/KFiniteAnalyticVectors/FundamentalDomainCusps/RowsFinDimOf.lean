import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.ShortIsot
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsProj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaBase

open Matrix MeasureTheory NumberField Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.RF

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows Formalism.L2.SG.RowsDef Formalism.L2.SG.Pf Formalism.MainNotions.LeviCoordinates

theorem dense_bdd {X : Type} [MeasurableSpace X] (μ : Measure X) :
    Dense {F : Lp ℂ 2 μ | ∃ M : ℝ, ∀ᵐ x ∂μ, ‖(F : X → ℂ) x‖ ≤ M} := by
  refine (Lp.simpleFunc.dense (E := ℂ) (μ := μ) (p := 2) (by simp)).mono fun F hF => ?_
  let f : Lp.simpleFunc ℂ 2 μ := ⟨F, hF⟩
  obtain ⟨M, hM⟩ := (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
  refine ⟨M, ?_⟩
  filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun f] with x hx
  rw [show (F : X → ℂ) x = Lp.simpleFunc.toSimpleFunc f x from hx.symm]
  exact hM x

theorem rowsFinDim_of (hCore : Core) (hFin : FiniteDimensionalFromLinearForms) (hCA : CuspAdel) (hD : GFDisc) (hLev : LevelOf)
    (hCR : ConvRep) (hRC : RepOfConv) : RowsFinDim := by
  intro I μf _ _ fund hfund R hR e Re hlc hsupp hRe H _ _ _ σ dv w hU _ hF hw hL T hT
  have : LocallyCompactSpace I.Gf := gf_locallyCompact I
  have : T2Space I.Gf := finite_adeles_group_t2 I
  have : SecondCountableTopology I.Gf := rr_secondCountable I μf
  have hright : (I.muA μf).IsMulRightInvariant := Formalism.L2.S.S7.IwasawaBase.muA_right I μf
  have : (I.muA μf).IsHaarMeasure := by
    have h1 : (I.muA μf).IsOpenPosMeasure := by unfold AutInst.muA; infer_instance
    have h2 : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
    have h3 : IsLocallyFiniteMeasure (I.muA μf) := by unfold AutInst.muA; infer_instance
    exact {}
  have hlf : IsLocallyFiniteMeasure μf := inferInstance
  let X : Formalism.MainNotions.BridgeLemma.CData :=
    { I := I, b := 0, lam := 0, g := 0, g₀ := 0, e := e, H := fun _ => ℂ, σ := fun _ _ => 0, w := 0,
      Hs := ℂ, σs := fun _ => 0, tens := fun _ => 0, μf := μf, fund := fund, R := R, Re := Re, h := 0 }
  have hd : RegData X := ⟨‹_›, hfund, hR⟩
  have hu : UnimodA X := hright
  obtain ⟨hmul, -, hiso, -⟩ := adelic_regular_rep_unitary_continuous X hd hu hlf
  have hmeas := regular_rep_coeff_measurable X hd hu
  set ph := phInf I σ w dv with hph
  have hphI : Integrable ph (muInf I) := phInf_int I hL
  have hconv := phInf_conv I hU hF hw
  have hφ₀ : Integrable (fun p : I.GA => ph p.1 * e p.2) (I.muA μf) := hphI.mul_prod hRe.1
  have hpr := prod_op_eq (muInf I) μf R hmul hiso (fun x y => (hmeas x y).aestronglyMeasurable) ph e hφ₀ T Re hT hRe.2
  have hRT : I.IsRConv μf fund R (fun p => ph p.1 * e p.2) (Re.comp T) := ⟨hφ₀, fun x y => (hpr x y).2.symm⟩
  obtain ⟨Kp, hKo, hKc, hKe⟩ := hLev I e hlc hsupp
  have hK0 : μf Kp ≠ 0 := (hKo.measure_pos μf ⟨1, Kp.one_mem⟩).ne'
  have hK1 : μf Kp ≠ ∞ := hKc.measure_lt_top.ne
  have hind : Integrable ((Kp : Set I.Gf).indicator fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ)) μf :=
    (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hK1)
  have hφ : Integrable (phK I μf ph Kp) (I.muA μf) := hphI.mul_prod hind
  have hφφ₀ : ∀ z : I.GA, ∫ y, phK I μf ph Kp y * (ph (y⁻¹ * z).1 * e (y⁻¹ * z).2) ∂(I.muA μf) = ph z.1 * e z.2 := by
    intro z
    have e1 : (fun y : I.GA => phK I μf ph Kp y * (ph (y⁻¹ * z).1 * e (y⁻¹ * z).2)) = fun y =>
        (ph y.1 * ph (y.1⁻¹ * z.1)) *
          (Kp : Set I.Gf).indicator (fun _ => (((μf Kp).toReal⁻¹ : ℝ) : ℂ) * e z.2) y.2 := by
      funext y
      by_cases hy : y.2 ∈ Kp
      · have hy' : y.2 ∈ (Kp : Set I.Gf) := hy
        simp only [phK, Set.indicator_of_mem hy', Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
          hKe _ (Kp.inv_mem hy)]
        ring
      · have hy' : y.2 ∉ (Kp : Set I.Gf) := hy
        simp only [phK, Set.indicator_of_notMem hy', mul_zero, zero_mul]
    rw [e1]
    refine (integral_prod_mul (μ := muInf I) (ν := μf) (fun g => ph g * ph (g⁻¹ * z.1)) _).trans ?_
    rw [hconv, integral_indicator_const _ hKo.measurableSet, Measure.real, Complex.real_smul, ← mul_assoc ((μf Kp).toReal : ℂ),
      ← Complex.ofReal_mul, mul_inv_cancel₀ (ENNReal.toReal_pos hK0 hK1).ne', Complex.ofReal_one, one_mul]
  have hFD := rr_isFD (rr_FD_of I μf fund hfund)
  have hO : IsClopen {g : I.GA | g.2 ∈ Kp} :=
    IsClopen.preimage (s := (Kp : Set I.Gf)) ⟨Kp.isClosed_of_isOpen hKo, hKo⟩ continuous_snd
  have hdet := hCore I.GA (I.muA μf) (rr_GF I) fund hFD (fun C hC => hD I C hC) (phK I μf ph Kp) _ hφ hO
    (fun y hy => by
      have hy' : y.2 ∉ (Kp : Set I.Gf) := hy
      simp only [phK, Set.indicator_of_notMem hy', mul_zero])
    (hCA I μf (rr_GF I) rfl Kp hKo hKc ph hphI hconv)
  refine hFin I.GA (I.muA μf) (rr_GF I) fund _ hφ hdet _ ?_
  rintro _ ⟨F₀, rfl⟩
  refine map_mem_closure (f := Re.comp T) (Re.comp T).continuous (dense_bdd _ F₀) fun F hFb => ?_
  obtain ⟨s, hs, hsb, hsi, hae⟩ := hCR I μf fund hfund R hR _ _ hRT F hFb
  exact ⟨_, hRC I.GA (I.muA μf) (rr_GF I) _ _ s hφ hφ₀ hφφ₀ hs hsb hsi, hae⟩

end CompanionTheory.D.gk.RF
