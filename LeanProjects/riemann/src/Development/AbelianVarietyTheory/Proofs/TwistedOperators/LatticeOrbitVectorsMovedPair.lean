import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqIntegralCombinationOfMemCompletedLatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOMemLatticeOOfIntegralCombinationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000

theorem bridge (V : HSp D) (k : GA D V) (s : Fin V.rank → D.host.E) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) =
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

theorem fwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfg : Module.Finite (𝓞 D.host.E) C) (hsp : Submodule.span D.host.E (C : Set (Fin V.rank → D.host.E)) = ⊤)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) := by
  have hmem : (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
    Submodule.subset_span ⟨s, hs, rfl⟩
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) C hfg hsp
    (Formalism.IndefR.Lev.finE V k) ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)))
  have e : ((Formalism.IndefR.Lev.finE V k)⁻¹ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).1 *ᵥ ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j))) = (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e] at hmem
  have k2 := key.2 hmem
  have hb := bridge V k s
  simp only [hb]
  exact k2

theorem bwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  rw [bridge, map_inv]
  exact hs

theorem mem_globLat_iff {n : ℕ} (g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat g C ↔ (g⁻¹).1 *ᵥ (fun i => Formalism.IndefR.Datum.eToEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
  Iff.rfl

theorem colLat_fin {n : ℕ} (B : GL (Fin n) D.host.E) : Module.Finite (𝓞 D.host.E) (colLat B) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))

theorem colLat_span {n : ℕ} (B : GL (Fin n) D.host.E) :
    Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hcol : ∀ j : Fin n, (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) ∈
      Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) :=
    fun j => Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩)
  have e : v = ∑ j, ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) := by
    have h1 : (B : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)

set_option maxHeartbeats 1000000 in

theorem globLat_mul_iff {n : ℕ} (a b : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (Λ C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔ b.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat a Λ ↔ y ∈ Formalism.UG.CS.globLat (a * b) C := by
  rw [mem_globLat_iff, mem_globLat_iff]
  have e : ((a * b)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)).1 = (b⁻¹).1 * (a⁻¹).1 := congrArg Units.val (_root_.mul_inv_rev a b)
  have e2 : b.1 * (b⁻¹).1 = 1 := congrArg Units.val (mul_inv_cancel b)
  rw [e, ← Matrix.mulVec_mulVec, hb ((b⁻¹).1 *ᵥ ((a⁻¹).1 *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i))),
    Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

theorem movedLat_eq {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) :
    inV (S.N.fr X) (GlobalTheory.SumSize.latAt S X x) =
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) :
        Set (Fin (G.V X).rank → D.host.E)) := by
  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) x) (G.Λ X) ↔
      y ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) := by
    have e : Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X)) =
        finG (G.V X) x * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 :=
      map_mul (Formalism.IndefR.Lev.finE (G.V X)) (x : GA D (G.V X)) (S.N.u X).1
    rw [e]
    exact globLat_mul_iff _ _ _ _ (S.N.u_lat X hX)
  ext y
  simp only [inV, GlobalTheory.SumSize.latAt, Set.mem_image, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (key _).1 hz
  · intro hy
    refine ⟨((S.N.fr X)⁻¹ : GL _ D.host.E).1 *ᵥ y, ?_, ?_⟩ <;>
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact (key _).2 hy

theorem actO_latO_le (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT) :
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
  GlobalTheory.T.weilActionO_mem_latticeO_of_integralCombinations S T g h AS BS AT BT (fun s hs => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BS _ (hS s hs)) (fun t ht => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BT _ (hT t ht))

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (w : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := by
  simp only [actO]
  rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * w), ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.one_mul]

theorem actO_latO_onto (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT)
    (hS' : ∀ s ∈ BS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g⁻¹ *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AS)
    (hT' : ∀ t ∈ BT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AT) :
    (∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
    (∀ w' ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∃ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T g h w = w') :=
  ⟨actO_latO_le S T g h AS BS AT BT hS hT, fun w' hw' =>
    ⟨actO S T g⁻¹ h⁻¹ w', actO_latO_le S T g⁻¹ h⁻¹ BS AS BT AT hS' hT' w' hw', actO_actO_inv S T g h w'⟩⟩

end GlobalTheory.MovedHomLat

open GlobalTheory.MovedHomLat in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MovedDict.actO_latO_moved : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x]
    let N := ch.S.N
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.grid (i + 1) j)) := ((y * N.u (.grid (i + 1) j) : FinPt ch.G (.grid (i + 1) j)) : Formalism.L2.Theta.GA D _)
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.grid i j)) := ((x * N.u (.grid i j) : FinPt ch.G (.grid i j)) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (negSp (ch.G.V (.grid (i + 1) j))) (ch.G.V (.grid i j)) (negGA _ ky) kx
      (colLat (N.fr (.grid (i + 1) j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid (i + 1) j)) ky) (colLat (N.fr (.grid (i + 1) j))))
      (colLat (N.fr (.grid i j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid i j)) kx) (colLat (N.fr (.grid i j))))
      (fwd (ch.G.V (.grid (i + 1) j)) ky _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.grid i j)) kx _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.grid (i + 1) j)) ky _)
      (bwd (ch.G.V (.grid i j)) kx _)
    exact H
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y]
    let N := ch.S.N
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.top j)) := ((x * N.u (.top j) : FinPt ch.G (.top j)) : Formalism.L2.Theta.GA D _)
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.top (j + 1))) := ((y * N.u (.top (j + 1)) : FinPt ch.G (.top (j + 1))) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) kx ky
      (colLat (N.fr (.top j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top j)) kx) (colLat (N.fr (.top j))))
      (colLat (N.fr (.top (j + 1))))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top (j + 1))) ky) (colLat (N.fr (.top (j + 1)))))
      (fwd (ch.G.V (.top j)) kx _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.top (j + 1))) ky _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.top j)) kx _)
      (bwd (ch.G.V (.top (j + 1))) ky _)
    exact H
  | mu t i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
