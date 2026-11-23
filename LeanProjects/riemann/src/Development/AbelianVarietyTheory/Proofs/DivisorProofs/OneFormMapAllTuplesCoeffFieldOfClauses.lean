import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXiStatement

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistField

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem oneMapOverL_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hC : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀)) (hpb : T.pb = R.C.P.pb)
    (hO : OMPins T R κ v₀ O i) (hph : PhaseTie T R κ v₀ O ph i) (hio : IoExt R) (h0 : OneMapRow0 T R κ v₀ O i)
    (hex : PinsOverL T R κ v₀ i) (hsp : LiftsSpan R i (v₀ i (sg0 D A))) : OneMapOverL T R κ v₀ (ph i) i := by
  have hrow := hph h0
  obtain ⟨w⟩ := id hW
  have hT := w.laws
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hn : (κ i).n = (Vc D i).rank :=
    (w.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, hlam, hU⟩ := GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum D G Pl0 T0 A T R F κ v₀ hC h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hF₀, hP₀⟩ := hex
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := GlobalTheory.LiftSpanClauses.exists_retie_core O₀ hC
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hF₁ : O₁.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange := e₁ ▸ hF₀
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := hF₁.ge
  obtain ⟨c0, hr, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  have hid := hU _ _ (O i) hO.1.ge hP rfl hc c0 hx
  have hid₁ := hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁
  have hE₁ := GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ O₁ hle₁ hP₁
  have n0 := ne_zero_of_root hr
  have n1 := ne_zero_of_root hr₁
  by_cases hz : ∀ y, liftQ R i (v₀ i (sg0 D A)) A.μ0 y = 0
  · exact ⟨O₁, hF₁, hP₁, oneMapOf_of_ptIdent hT hV hn hP hrow hle₁ hP₁ hlev₁ hE₁ hsp hlam n0 n1 hid hid₁ (Or.inr hz)⟩
  · obtain ⟨y, hy⟩ := not_forall.1 hz
    have hu := const_ratio_mem hT hV hn hO.1 hP hrow hle₁ hP₁ hlev₁ hE₁ hlam n1 hid hid₁ hy
    have e : ((⟨c0 / c1, hu⟩ : O₁.c'.F) : ℂ) * c1 = c0 := div_mul_cancel₀ _ n1
    have hx₂ := xiConst_scaleXi O₁ ⟨c0 / c1, hu⟩ hx₁
    have hP₂ := pins_scaleXi O₁ ⟨c0 / c1, hu⟩ (fun h => div_ne_zero n0 n1 (congrArg Subtype.val h)) hx₁ (e.symm ▸ hr) hP₁
    rw [e] at hx₂
    exact ⟨scaleXi O₁ ⟨c0 / c1, hu⟩, hF₁, hP₂, oneMapOf_of_ptIdent (O' := scaleXi O₁ ⟨c0 / c1, hu⟩) hT hV hn hP hrow hle₁ hP₂ hlev₁
      (GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂) hsp hlam n0 n0 hid
      (hU _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂ hlev₁ hc₁ c0 hx₂) (Or.inl rfl)⟩

end GlobalTheory.TwistField
