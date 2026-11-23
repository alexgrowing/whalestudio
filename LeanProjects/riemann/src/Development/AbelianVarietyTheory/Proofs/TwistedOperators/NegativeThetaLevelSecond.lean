import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowLiftAut

theorem isQuot_of_is {D : D7} {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop)
    (K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))) (h : m.Is df K) :
    GlobalTheory.Mem.Th.IsQuot N.V m.ν m.fd := by
  by_cases hd : df
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.1 hd
    exact And.intro hH hF
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.2 hd
    exact And.intro hH hF

theorem isQuot_cast {D : D7} {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat)
    (h : GlobalTheory.Mem.Th.IsQuot S.V m.ν m.fd) :
    GlobalTheory.Mem.Th.IsQuot S'.V (m.cast e).ν (m.cast e).fd := by
  subst e
  exact h

theorem lift_isAutFunSm (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF ↥D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (GlobalTheory.Grid.WRep.toSgn true ω))
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T ν 𝓕)
    {Φ : WO (GlobalTheory.Grid.sgn true S) T → ℂ} (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn true S) T Φ)
    {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ) (hφc : IsCuspFun T φ) :
    IsAutFunSm θ S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν) := by
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hK := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std hW hω.om_cont).swap
  have hL := (GlobalTheory.Mem.Lift.IsKerSys.lift hCRD hθ hK hq ⟨hφ, hφc⟩ ⟨Φ, hΦ⟩).2
  exact ((GlobalTheory.sgn_fun_cusp D θ hθ true S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν)).1).1 hL

private theorem isQuot_Yc_nuY_fdY_of_base {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (t : T) (k : ℕ) (hk : k < D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (Yc D k) (R.νY t k) (R.fdY t k) := by
  rcases Nat.lt_or_ge (k + 1) D.R.m with h | h
  · obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY t k h
    exact And.intro hH hF
  · obtain rfl : k = D.R.m - 1 := by omega
    obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY' t
    exact And.intro hH hF

theorem isQuot_meas {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (hG : G.Is)
    (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j ≤ D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (G.V i j).V (G.meas t i j).ν (G.meas t i j).fd := by
  have hM := hG.meas
  rcases i with _ | i
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col 0 (Nat.zero_le _))
    · dsimp only [GlobalTheory.Grid.GridPre.meas, GlobalTheory.Grid.meas0]
      split_ifs with h1
      · exact isQuot_cast _ _ (isQuot_Yc_nuY_fdY_of_base R hR t (j + 1) h1)
      · refine isQuot_cast _ _ ?_
        obtain ⟨⟨hH, -⟩, hF⟩ := hR.measX t
        exact And.intro hH hF
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col (i + 1) hi.le)
    · exact isQuot_of_is _ _ _ (hM.vert i j hi.le hj)

end GlobalTheory.ArrowLiftAut

namespace GlobalTheory.ArrowLiftAut

theorem liftX_isAutFunSm : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ _
  exact lift_isAutFunSm hP.cuspRapidDecay hR.inf (hG.arrows.X i j hi hj).weil
    (isQuot_meas G hR hG t i j hi hj) hΦ hφ.1 hφ.2.1

end GlobalTheory.ArrowLiftAut
