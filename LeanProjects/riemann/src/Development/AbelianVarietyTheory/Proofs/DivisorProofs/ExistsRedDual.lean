import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittDualReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigToLieBijectiveAndDualRigOfOmegaBijectiveOfIsE

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

theorem dual_conn {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k}
    (hG : G.IsEt) : G.dual.IsConn :=
  PDivGroup.dual_isConn_of_isEt p k G hG

abbrev Mod {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsEt) : Type :=
  Module.Dual (WittVector p k) (B.M G.dual (dual_conn hG))

def IsTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG') : Prop :=
  letI : Algebra k k' := σ.toAlgebra
  ∃ (hb : (G.dual.baseChange k').IsConn)
    (lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb)),
    (∀ x, lb (B.smap hb (dual_conn hG) (G.dual.toBase k') x) = WittVector.map σ (l x)) ∧
    ∀ y, l' y = lb (B.map hb (dual_conn hG')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y)

open Classical in

def tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) : Mod B G' hG' :=
  if h : ∃ l', IsTr B σ hG' hG s l l' then Classical.choose h else 0

theorem tr_spec {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (h : ∃ l', IsTr B σ hG' hG s l l') :
    IsTr B σ hG' hG s l (tr B hG' hG s l) := by
  rw [tr, dif_pos h]
  exact Classical.choose_spec h

section Red

variable {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsEt)

theorem exists_redDual : ∃ r' : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k G.dual.RigExt,
    (∀ l m, r' l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  haveI := B.free G.dual (dual_conn hG)
  haveI := B.finite G.dual (dual_conn hG)
  exact wittDual_reduction p k _ _ (B.red G.dual (dual_conn hG))
    (B.red_surjective G.dual (dual_conn hG)) (B.red_eq_zero G.dual (dual_conn hG))

def redDual : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
    Module.Dual k G.dual.RigExt :=
  Classical.choose (exists_redDual B G hG)

theorem redDual_spec :
    (∀ l m, redDual B G hG l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective (redDual B G hG) ∧ ∀ l, redDual B G hG l = 0 ↔ ∃ l', l = p • l' :=
  Classical.choose_spec (exists_redDual B G hG)

def rigLie : G.RigExt ≃ₗ[k] G.dual.Lie :=
  LinearEquiv.ofBijective (G.rigToLie (p_eq_zero p k))
    (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k (p_eq_zero p k) G hG).1

def red : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt :=
  (rigLie G hG).symm.toLinearMap.comp (G.dual.rigOfOmega.dualMap.comp (redDual B G hG))

theorem rigToLie_red (l : Mod B G hG) :
    G.rigToLie (p_eq_zero p k) (red B G hG l) = G.dual.rigOfOmega.dualMap (redDual B G hG l) :=
  (rigLie G hG).apply_symm_apply _

end Red

end GlobalTheory.Dieu.EtFromConn
