import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvOfNear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.EntryAny

open GlobalTheory.Transport.Entry

theorem entry_transport_any : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 < B.R.m) (al : (I.idx a).β i) (be : (I.idx a).β (i + 1)) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀) =
        Formalism.L2.Col.XiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P) ((I.idx a).h (i + 1) be P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) := by
  intro B X I hI l u a i hm al be P p q p' q' k y k' y' hp hpN hp' hpN' hq hq'
  have hX := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hL := hI.idx_ok a
  have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.Transport.Entry.qOf_pos P.1).ne'
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · obtain ⟨M, hM, H⟩ := exists_modulus hp hp' hq hq' ⟨P.1, hP⟩ (pow_ne_zero (I.cst a).B hq0)
    refine ⟨M, hM, fun M₀ hM₀ x x₀ hx => ?_⟩
    obtain ⟨U, U', hU, hU', h⟩ := H M₀ hM₀ x x₀ hx
    have hu := exp_le_val_qOf (GlobalTheory.UnfoldTwoSided.degOne_bad hX.ok l.pr hI.sel_ok P)
    unfold Formalism.L2.Col.frsF
    simp only [dif_pos hP]
    refine (eq_of_near (P := P.1) _ hq0 (val_qOf_lt_one P.1) (pow_ne_zero (I.cst a).B hq0) (fun κ κ' hκ hκ' z => ?_)
      (hL.xiInv i (by omega) al be P) _ _ U U' (hU.mono hu) (hU'.mono hu) h).symm
    refine xiAt_inFr hX l.pr hI.ch_ok hI.sel_ok hL (by omega) al be P κ κ' ?_ ?_ z
    · rw [hL.depthG P hP, pow_one]
      exact hκ
    · rw [hL.depthG P hP, pow_one]
      exact hκ'
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (GlobalTheory.Transport.Entry.qOf_pos P.1) _, fun M₀ hM₀ x x₀ hx => ?_⟩
    have hd := GlobalTheory.Transport.TwistRead.qread I u a i P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hx
    set z₀ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hz₀
    set z₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hz₁
    have hMv : P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) ≤
        P.1.valuation B.fields.E (((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).B) := by
      obtain ⟨c, rfl⟩ := hM₀
      rw [Nat.cast_mul, map_mul, Nat.cast_pow]
      refine mul_le_of_le_one_right' ?_
      simpa using P.1.valuation_le_one (K := B.fields.E) (c : 𝓞 B.fields.E)
    have e : z₁ = z₀ + (z₁ - z₀) := by abel
    rw [e]
    refine (hL.xiInv i (by omega) al be P z₀ (z₁ - z₀) fun s l => ?_).symm
    refine intAt_inv_mul (pow_ne_zero _ hq0) ?_
    have e2 : (z₁ - z₀) (Pi.single s 1) l = (LinearMap.toMatrix' z₁ - LinearMap.toMatrix' z₀) l s := by
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, LinearMap.sub_apply, Pi.sub_apply]
    rw [e2]
    exact (hd l s).trans hMv

end GlobalTheory.Transport.EntryAny
