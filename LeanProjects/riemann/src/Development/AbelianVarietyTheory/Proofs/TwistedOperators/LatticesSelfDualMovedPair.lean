import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSelfDualEColLatOne
import Formalism.LocalToGlobal.Columns.DetChrChi
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

set_option maxHeartbeats 800000

namespace GlobalTheory.MovedSD

open Matrix

open Formalism.UG in
theorem colLat_one_eq_stdLat (D : D7) (n : ℕ) :
    colLat (1 : GL (Fin n) D.host.E) = Formalism.L2.Col.stdLat D.host.E n := by
  ext x
  rw [GlobalTheory.TestLat.Inhabitant.mem_colLat_one]
  simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem move_vec (D : D7) {n : ℕ} (fr : GL (Fin n) D.host.E) (a b : GL (Fin n) (Lev.EAf D)) (v : Fin n → D.host.E) :
    (fr⁻¹).val.map (eToEAf D) *ᵥ ((b⁻¹).val *ᵥ ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i))) =
      (Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
  have hb : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map (eToEAf D) := fun _ => rfl
  have ev : (fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) =
      fr.val.map (eToEAf D) *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) (v i) := by
    funext i
    exact RingHom.map_mulVec (eToEAf D) fr.val v i
  rw [ev]
  simp only [Units.val_mul, hb, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_globLat_move (D : D7) {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (fr : GL (Fin n) D.host.E)
    (a b : GL (Fin n) (Lev.EAf D))
    (hu : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔ b.val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin n → D.host.E) :
    fr.val *ᵥ v ∈ Formalism.UG.CS.globLat a Λ ↔
      v ∈ Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr) (Formalism.L2.Col.stdLat D.host.E n) := by
  change (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _) ↔ (_ ∈ Formalism.L2.Herm.hatL (F := D.host.F) _)
  generalize hw : ((a⁻¹).val *ᵥ fun i => Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) ((fr.val *ᵥ v) i)) = w
  have h1 := hu ((b⁻¹).val *ᵥ w)
  have e1 : b.val *ᵥ ((b⁻¹).val *ᵥ w) = w := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [e1] at h1
  rw [← h1]
  have hm := GlobalTheory.LatMulAd.mem_hatL_colLat_mul D fr 1 ((b⁻¹).val *ᵥ w)
  rw [mul_one, colLat_one_eq_stdLat] at hm
  rw [hm, ← hw]
  have eg : ((Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr)⁻¹ : GL (Fin n) (Lev.EAf D)) =
      Formalism.UG.bc (eToEAf D) fr⁻¹ * b⁻¹ * a⁻¹ * Formalism.UG.bc (eToEAf D) fr := by
    simp only [_root_.mul_inv_rev, ← map_inv, inv_inv, mul_assoc]
  rw [eg]
  refine Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Col.stdLat D.host.E n)) ?_)
  exact move_vec D fr a b v

theorem cT_map_inclE (D : D7) {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem move_mem_UAd (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (fr : GL (Fin n) D.host.E)
    (hfr : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.val * J * fr.val = 1) (a b : GL (Fin n) (Lev.EAf D))
    (ha : a ∈ Formalism.L2.DIV.UA D.sp.cm J) (hb : b ∈ Formalism.L2.DIV.UA D.sp.cm J) :
    Formalism.UG.bc (eToEAf D) fr⁻¹ * (a * b) * Formalism.UG.bc (eToEAf D) fr ∈ Formalism.L2.Col.UAd D.sp.cm n := by
  have hab : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (a * b).val *
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (a * b).val =
      J.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := mul_mem ha hb
  set A := (a * b).val
  set ι := Formalism.UG.inclE (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.Af D.host.F)
  set σR := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
  have hm : ∀ g : GL (Fin n) D.host.E, (Formalism.UG.bc (eToEAf D) g).val = g.val.map ι := fun _ => rfl
  have hF : Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι = 1 := by
    rw [cT_map_inclE, ← Matrix.map_mul, ← Matrix.map_mul, hfr, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : fr.val.map ι * (fr⁻¹).val.map ι = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι = J.map ι := by
    calc Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι
        = Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (Formalism.UG.cT σR (fr.val.map ι) * J.map ι * fr.val.map ι) * (fr⁻¹).val.map ι := by
          rw [hF, Matrix.mul_one]
      _ = Formalism.UG.cT σR (fr.val.map ι * (fr⁻¹).val.map ι) * J.map ι * (fr.val.map ι * (fr⁻¹).val.map ι) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J.map ι := by
          rw [h1]; simp [Formalism.UG.cT]
  show Formalism.UG.cT σR (_ : GL (Fin n) (Lev.EAf D)).val * (1 : Matrix (Fin n) (Fin n) D.host.E).map ι * _ = _
  rw [Units.val_mul, Units.val_mul, hm, hm, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  calc Formalism.UG.cT σR ((fr⁻¹).val.map ι * A * fr.val.map ι) * ((fr⁻¹).val.map ι * A * fr.val.map ι)
      = Formalism.UG.cT σR (fr.val.map ι) * (Formalism.UG.cT σR A * (Formalism.UG.cT σR ((fr⁻¹).val.map ι) * (fr⁻¹).val.map ι) * A) * fr.val.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hab, hF]

theorem sd_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) : SD D (GlobalTheory.SumSize.latAt S X x) := by
  have e : GlobalTheory.SumSize.latAt S X x = Formalism.UG.CS.globLat (Formalism.UG.bc (eToEAf D) (S.N.fr X)⁻¹ *
      (finG (G.V X) x * Lev.finE (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))) * Formalism.UG.bc (eToEAf D) (S.N.fr X))
      (Formalism.L2.Col.stdLat D.host.E _) := by
    ext v
    exact mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v
  have ha : finG (G.V X) x ∈ Formalism.L2.DIV.UA D.sp.cm (G.V X).gram := GlobalTheory.LevSplit.finE_mem_UA (G.V X) x.1
  have hb := GlobalTheory.LevSplit.finE_mem_UA (G.V X) (S.N.u X : Formalism.L2.Theta.GA D (G.V X))
  show IsSDLat D.host.E _ _
  rw [e]
  exact Formalism.L2.Col.DetChrChi.isSDLat_globLat D.sp.cm (move_mem_UAd D _ _ (S.N.fr_on X hX) _ _ ha hb)

end GlobalTheory.MovedSD

theorem GlobalTheory.MovedSD.sd_srcLat_tgtLat : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    SD D (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) ∧ SD D (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y, GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x⟩
  | top t j => exact ⟨GlobalTheory.MovedSD.sd_latAt _ _ hn.1 x, GlobalTheory.MovedSD.sd_latAt _ _ hn.2 y⟩
  | _ => exact hp.elim
