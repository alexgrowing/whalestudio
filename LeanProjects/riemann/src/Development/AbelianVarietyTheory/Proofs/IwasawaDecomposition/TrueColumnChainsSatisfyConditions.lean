import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsAtFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

theorem GStep.Ok.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Ok)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Ok :=
  ⟨h.fin_orb, h.fin_stab, h.unit, h.root, h.lsh_smul, h.lsh_lat, h.stab_inj⟩

theorem GStep.Free.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Free)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Free := fun b g d hd => h b g d hd

namespace TC

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary (h : I.Ok) (a : I.ι) : (I.xi a).IsUnitary := by
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  exact HChar.isUnitary_of_order hn ((h.xi_reads a).orderDvd hpow)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.unrepresented_step_conditions (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp0 u a i).Ok := by
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  refine StepOk.stepY_ok _ _ _ _ hX _ _ ?_ ?_ ?_
  · rintro ⟨_ | b, hb⟩ P
    · exact topLev_finiteIndex I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P g
    · obtain ⟨m, hm, hk⟩ := topLev_root I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
      exact ⟨m, hm, hk g⟩
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).2 g
  · exact fun N hN => (CosetFin.ysAt_finite_nonempty B.R I.sel (I.tup a) (I.cst a) i N hN).1

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_ok (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp u a i).Ok := (h.unrepresented_step_conditions u a i).reRep _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_zero_free (h : I.Ok) (u : B.Word) (a : I.ι) : (I.stp u a 0).Free :=
  GStep.Free.reRep (stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u (base_fields_primes_ok B X).1
    (base_fields_primes_ok B X).2.1 (base_fields_primes_ok B X).2.2.2.2 (h.idx_ok a).zero_G) _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.chIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.chIn u a).Ok where
  step i := h.stp_ok u a i
  rho_norm i _ c := by
    show ‖((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt I.SQ I.C (h.xi_unitary a) i _
  rho'_norm i _ c := by
    show ‖((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt' I.SQ I.C (h.xi_unitary a) i _
  DG_pos := DGam_pos (posStar_of_ok (base_fields_primes_ok B X).1) B.R
  dvd_DG i hi c := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hf := h.stp_zero_free u a
      haveI : Subsingleton ((I.stp u a 0).Stab c) :=
        ⟨fun x y => Subtype.ext ((hf c.1 x.1 _ x.2).trans (hf c.1 y.1 _ y.2).symm)⟩
      rw [Nat.card_unique]
      exact one_dvd _
    · exact stepY_dvd _ _ _ _ ((I.Tp a).pref u i) (base_fields_primes_ok B X).1 B.R (N_mem_gamRanks B.R hpos hi) c.1 ((I.stp u a i).rep c)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.idx0 (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b, by simp only [Option.isSome_some, true_iff]; exact lt_of_lt_of_le (by norm_num) B.R.two_le_m⟩⟩

theorem rep_L_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  ((I.stp u a i).rep c).1.1.deco.2.L_lattice

theorem ok_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  fun _ h u a => ⟨h.chIn_ok u a, h.idx0 a, fun i c => rep_L_lattice u a i c⟩

end TC

end GlobalTheory.Mem.Col2

end
