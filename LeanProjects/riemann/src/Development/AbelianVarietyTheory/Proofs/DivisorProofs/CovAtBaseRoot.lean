import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverValueCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightZeroConstFrameValueMemCoeffRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClsAt

namespace GlobalTheory.AdTh.CoverRoot

section Core

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdTh.CoverVal

theorem rdU_move {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U)
    {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (k : U.Comp) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ (U.X k).Γ) {b : Frame (U.X k).Ψ r} (hb : b ∈ Bor (U.X k).Ψ r) :
    rdU U f k (rmul (lact γ x) b) = rdU U f k x := by
  have hs := hU.2.2.2.2.1 0 0 ⟨fun τ _ _ _ => le_rfl, Even.zero⟩ f hf k
  rw [show laU U 0 0 k = 0 from GlobalTheory.Reg.IdemCusp.laU_zero (Formalism.L2.PjFree.Unf.ofPj U) k] at hs
  rw [hs.2.1 _ (dom_lact (U.X k) hx ((U.X k).Γ_stab γ hγ)) b hb, hs.2.2 γ hγ x hx, GlobalTheory.Reg.IdemCusp.chi_zero _ hγ]
  simp [bchar]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}

set_option maxHeartbeats 1000000 in

theorem covAt_mem (hR : GlobalTheory.Hk3.Core R F) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (c0 : ℂ) (h0 : GlobalTheory.PtId.CovAt O c0) :
    c0 ∈ (inC O.c').range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  obtain ⟨c1, hm, hc⟩ := hO.cxi
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc ()
  obtain ⟨hlev, hA, -⟩ := hO.cov ()
  have hs0 : O.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hX₀, hon₀, -, hp₀, hrk, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    hs0 (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ ()).c₂ ((inC O.c').comp ((O.dδ ()).eF.symm : (O.dδ ()).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ ()).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ ()).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
  obtain ⟨Wt⟩ := nonempty_uw hU'
  obtain ⟨hroot, -⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  have hxi : ∀ x, R.xi A.μ0 x = 1 :=
    GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0)
  have hf : (O.dδ ()).cδ ∈ sec (O.dδ ()).Xo₂ (O.dδ ()).c₂ 0 0 := hlev.2.2.2.2.2.2.2.1
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c1 := fun h => by
    obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 h
    obtain ⟨x, hx⟩ := hroot (γ' * h)
    have hv := hval h γ' ⟨hγ', h2, h3⟩
    rw [(hO.tuple ()).xi _ _ hx, hxi, Circle.coe_one, _root_.mul_one] at hv
    exact hv
  have key : ∀ h, (O.dict₂ () h).2 ∈ ((O.U₂ ()).X (O.dict₂ () h).1).dom ∧
      rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨hon, γ, ⟨hγ, hl, hfr⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ ()) hσ hU h1 hA R.θ (Wc D i)
      (rank_Wc i) (O.dict₂ ()) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt h
    obtain ⟨-, hsd, hmark, -⟩ := uw_lattice _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1
    obtain ⟨Dc, hDc, -⟩ := exists_dic _ _ _ _ (O.dδ ()).c₂ _ _ Wt.g 0 ((O.U₂ ()).X (O.dict₂ () h).1) 0 Wt.e hσ hU.1
      (hU.2.1 _).1 (hU.2.1 _).2 hsd ⟨fun _ => antitone_const, Even.zero⟩
    have hper := Dc.per_eq
    have hty := Dc.ty_eq
    rw [hDc] at hper hty
    obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 _ Dc.bas Dc.idx Dc.sympl Even.zero _ hon
    have hA' := uw_anFib _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (O.U₂ ())) hσ hU' h1 Wt (O.dict₂ () h).1 Dc.bas Dc.idx
      Dc.sympl hper hty ⟨_, hd'⟩ hu'
    obtain ⟨x, hx⟩ := hroot (γ * h)
    have h3 := h0 () _ Wt.g Dc.bas Dc.idx Wt.e (γ * h) x (Wt.mark (O.dict₂ () h).1) (hmod _) (hU.2.1 _).1 Dc.sympl
      ⟨hper, hty⟩ hl hx hmark hma
    rw [← hfr, hxi, Circle.coe_one, _root_.mul_one] at h3
    obtain ⟨A', hA'', -⟩ := hA'
    exact ⟨hd', (dif_pos hd').trans (h3 _ A' hA'')⟩
  obtain rfl : c0 = c1 := (key 1).2.symm.trans (hv 1)
  refine ⟨?_, hm⟩
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT.laws _ (inR i) O.s0 (hs0 ▸ T.toCore.good_σ₀) (Wc D i) O.hV
    (rank_Wc i)
  have hpq := hrk ▸ h1
  obtain ⟨a, ha⟩ := GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range _ _ _ _ _ _ _ _ (O.U₂ ()) hσ hU hpq _ hf c0 fun k x hx => by
    obtain ⟨h, γ, hγ, b, hb, e⟩ := GlobalTheory.CoverIndep.dict_onto (Wc D i) (rank_Wc i) (O.U₂ ()) (O.dict₂ ()) (iotaW T i) e' F' ik φ
      th _ hσ hA hpq hU hW hD hio hth hx₀ (fun h => (key h).1) k x hx
    have h4 := hv h
    rw [e] at h4
    exact (rdU_move (O.U₂ ()) hU hf k hx hγ hb).symm.trans h4
  exact ⟨_, ha⟩

end Core

section Top

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

theorem covAt_base_root : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ c0 : ℂ, GlobalTheory.PtId.CovAt (O i) c0 → c0 ∈ D.what₂.embLL.range ∧ ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1 := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O _ hC i hOP c0 h0
  obtain ⟨⟨a, rfl⟩, hm⟩ := covAt_mem hC ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩ (O i) hOP.2 c0 h0
  refine ⟨?_, hm⟩
  obtain ⟨b, hb⟩ := hOP.1.le a.2
  exact ⟨b, hb⟩

end Top

end GlobalTheory.AdTh.CoverRoot
