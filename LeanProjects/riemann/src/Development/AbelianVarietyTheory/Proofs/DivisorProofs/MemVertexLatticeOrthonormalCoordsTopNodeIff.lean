import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Formalism.LocalToGlobal.Columns.AdelicLemmas

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLatSplit

open Formalism.L2.Col.Br

private theorem forall_idx {N n : ℕ} (hN : N = n + 1) (p : Fin N → Prop) :
    (∀ i, p i) ↔ (∀ k, p (iC hN k)) ∧ p (iL hN) := by
  subst hN
  exact Fin.forall_fin_succ'

private theorem frame_mulVec {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (Fr : Matrix (Fin N) (Fin N) R)
    (Q : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hC : ∀ i k, Fr i (iC hN k) = Q i k) (hL : ∀ i, Fr i (iL hN) = a i)
    (t : Fin N → R) : Fr *ᵥ t = Q *ᵥ (fun k => t (iC hN k)) + t (iL hN) • a := by
  subst hN
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hC, ← hL]
  rw [Fin.sum_univ_castSucc, mul_comm (t _)]
  rfl

private theorem block {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (A Fr : GL (Fin N) R) (B fr : GL (Fin n) R)
    (P : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hP : A.val * P = P * B.val) (ha : A.val *ᵥ a = a)
    (hC : ∀ i k, Fr.val i (iC hN k) = (P * fr.val) i k) (hL : ∀ i, Fr.val i (iL hN) = a i) (v : Fin N → R) :
    (∀ k, (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iL hN) = v (iL hN) := by
  obtain ⟨z, hzC, hzL⟩ : ∃ z : Fin N → R, (∀ k, z (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      z (iL hN) = v (iL hN) := by
    subst hN
    refine ⟨Fin.snoc (α := fun _ => R) (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC rfl k)) (v (iL rfl)), fun k => ?_, ?_⟩
    · exact Fin.snoc_castSucc (α := fun _ => R) _ _ k
    · exact Fin.snoc_last (α := fun _ => R) _ _
  have e1 : B.val * fr.val * ((fr⁻¹ * B * fr)⁻¹).val = fr.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e2 : A.val *ᵥ (Fr.val *ᵥ z) = Fr.val *ᵥ v := by
    rw [frame_mulVec hN Fr.val _ a hC hL z, frame_mulVec hN Fr.val _ a hC hL v, funext hzC, hzL, Matrix.mulVec_add,
      Matrix.mulVec_smul, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hP, Matrix.mul_assoc P,
      Matrix.mul_assoc P, e1]
  have e3 : ((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v = z := by
    have e4 : (Fr⁻¹ * A * Fr).val *ᵥ z = v := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
    rw [← e4, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e3]
  exact ⟨hzC, hzL⟩

private theorem mem_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X)
    (v : Fin (G.V X).rank → D.host.E) :
    v ∈ GlobalTheory.SumSize.latAt S X x ↔ ∀ i, ((((Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹ *
      (Lev.finE (G.V X) x.1 * Lev.finE (G.V X) (S.N.u X).1) * Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹).val *ᵥ
        fun i => eToEAf D (v i)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv]
  exact (GlobalTheory.MovedSD.mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v).trans (Formalism.L2.Col.mem_latS_std _)

private theorem finE_val {D : D7} (V : HSp D) (g : Formalism.L2.Theta.GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := by
  ext i j
  rfl

private theorem emb_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (y u' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin N) (Fin n) R) (hx : x * P = P * y) (hu : u * P = P * u') :
    x.map f * u.map f * P.map f = P.map f * (y.map f * u'.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, hx,
    Matrix.mul_assoc]

private theorem vec_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (a : Fin N → R) (hx : x *ᵥ a = a) (hu : u *ᵥ a = a) :
    (x.map f * u.map f) *ᵥ (fun i => f (a i)) = fun i => f (a i) := by
  funext i
  rw [← Matrix.map_mul]
  refine (RingHom.map_mulVec f (x * u) a i).symm.trans ?_
  rw [← Matrix.mulVec_mulVec, hu, hx]

end GlobalTheory.TopLatSplit

open GlobalTheory.TopLatSplit in
set_option maxHeartbeats 800000 in
theorem _root_.GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) (v : Fin (G.V (.top D.R.m)).rank → D.host.E),
    v ∈ GlobalTheory.SumSize.latAt S (.top D.R.m) (finEmb G.sp.topDec y) ↔
      (fun k => v (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k)) ∈ GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y ∧
        ∃ c : 𝓞 D.host.E, (c : D.host.E) = v (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) := by
  intro D T L sc G W S y v
  have hrel := finEmb_rel G.sp.topDec y
  have hx1 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * topEmb G = topEmb G * mt (G.V (.grid D.R.m D.R.m)) y.1 := hrel.1
  have hx2 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 *ᵥ topVec G = topVec G :=
    hrel.2 (fun i => G.sp.topDec.a i 0) (funext fun k => congr_fun (congr_fun G.sp.topDec.perp k) 0)
  have hb := block (R := Lev.EAf D) (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm
    (Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * Lev.finE (G.V (.top D.R.m)) (S.N.u (.top D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.top D.R.m)))
    (Lev.finE (G.V (.grid D.R.m D.R.m)) y.1 * Lev.finE (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.grid D.R.m D.R.m)))
    ((topEmb G).map (toEAf D)) (fun i => toEAf D (topVec G i))
    (by
      rw [Units.val_mul, Units.val_mul, finE_val, finE_val, finE_val, finE_val]
      exact emb_map (toEAf D) _ _ _ _ _ hx1 S.N.u_top)
    (by
      rw [Units.val_mul, finE_val, finE_val]
      exact vec_map (toEAf D) _ _ _ hx2 S.N.u_last)
    (fun i k => by
      have e := congrArg (eToEAf D) (S.N.fr_top i k)
      exact e.trans (congr_fun (congr_fun (Matrix.map_mul (f := eToEAf D)) i) k))
    (fun i => congrArg (eToEAf D) (S.N.fr_last i))
    (fun i => eToEAf D (v i))
  refine (mem_latAt S (.top D.R.m) (le_refl D.R.m) (finEmb G.sp.topDec y) v).trans ?_
  refine (forall_idx (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm _).trans ?_
  refine and_congr ?_ ?_
  · refine Iff.trans ?_ (mem_latAt S (.grid D.R.m D.R.m) ⟨le_refl _, rfl⟩ y _).symm
    exact forall_congr' fun k => Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hb.1 k))
  · refine (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) hb.2)).trans ?_
    exact GlobalTheory.NormSum.AdLattice.incl_mem_iff _
