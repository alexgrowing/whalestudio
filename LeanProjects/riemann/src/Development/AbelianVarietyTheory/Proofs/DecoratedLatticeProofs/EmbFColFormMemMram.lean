import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

noncomputable section

namespace GlobalTheory.Core.ColRam

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (u : B.Word) (a : I.ι)

include h in

theorem col_smul (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (g : (I.stp u a 0).G b) (p : (I.stp u a 0).D b) :
    φ.1 ((I.stp u a 0).act b g p).1.1.deco = (I.stp u a 0).rho B.fields.emb (lamT (B.hcW u) 0) b g (φ.1 p.1.1.deco) :=
  StepZero.form_smul ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (StepZero.levGAt_zero (I.Tp a) (h.idx_ok a))
    (StepZero.levQAt_zero (I.Tp a) (h.idx_ok a)) φ b g p

variable (hf : ((I.stp u a 0).fam B.fields.emb (lamT (B.hcW u) 0)).Ok)

def colForm : ColsK I u →ₗ[B.fields.K] (I.stp u a 0).FormsK B.fields.emb (lamT (B.hcW u) 0) hf where
  toFun φ := ⟨fun c => φ.1 ((I.stp u a 0).rep c).1.1.deco, fun c g =>
    (col_smul I h u a φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colForm_eq_zero (φ : ColsK I u) (h0 : colForm I h u a hf φ = 0) : φ = 0 := by
  apply Subtype.ext
  funext d
  obtain ⟨p, rfl⟩ := StepZero.exists_pt (Q := I.Q a) (StepZero.ysAt_zero (R := B.R) I.sel (I.tup a) (I.cst a)) d
  let b : Idx I.sel (I.tup a) (I.idx a) 0 := (StepZero.idxUnique (h.idx_ok a)).default
  have h1 : φ.1 ((I.stp u a 0).rep ((I.stp u a 0).cl b p)).1.1.deco = 0 :=
    congrFun (congrArg Subtype.val h0) ((I.stp u a 0).cl b p)
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  exact h2.trans ((congrArg _ h1).trans (map_zero _))

theorem trTo_colForm (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (p : (I.stp u a 0).D b) :
    (I.stp u a 0).trTo B.fields.emb B.embLL b p
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ((I.stp u a 0).cl b p)) =
      evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL
        (φ.1 p.1.1.deco) := by
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  refine Eq.trans ?_ (congrArg _ h2).symm
  exact (GStep.evV_rho_eq_tr (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) b _ _).symm

theorem embF_colForm_diaOp (P : (B.primes X).vT u) (e : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ)) =
      (I.atIn u a).diaLin B.fields.emb B.embLL P e
        ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) := by
  funext c
  refine Eq.trans ?_ (trTo_colForm I h u a hf φ c.1 (((I.atIn u a).A 0).diaPt P e c)).symm
  have e1 : (((I.atIn u a).A 0).diaPt P e c).1.1.deco = DecoSet.dia1 P e ((I.stp u a 0).rep c).1.1.deco :=
    congrArg (fun q => q.1.1.deco) (PtY.mv_dia ((I.stp u a 0).rep c) P e)
  rw [e1]
  exact congrArg (evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL)
    (LocOp.ofMap_op_apply _ _ _ _ _ φ _)

theorem embF_colForm_mem_Mram (l : I.Laws) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ∈ (I.atT l u a).Mram ↔
      φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have key : ∀ P : (B.primes X).vT u, (I.atT l u a).Nm P
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) =
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ)) := by
    intro P
    have e : NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ =
        ∑ e ∈ @Finset.univ _ (Fintype.ofFinite (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ), diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ :=
      LinearMap.sum_apply _ _ _
    rw [e, map_sum, map_sum]
    refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr (Finset.ext fun e => ?_) fun e _ => ?_)
    · exact iff_of_true (@Finset.mem_univ _ (_) _) (@Finset.mem_univ _ (_) _)
    · exact (embF_colForm_diaOp I h u a hf P e φ).symm
  have hz : ∀ ψ : ColsK I u,
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf ψ) = 0 ↔ ψ = 0 := fun ψ =>
    (map_eq_zero_iff _ (StepZero.embF_injective _ _ _ _ hf)).trans
      ⟨colForm_eq_zero I h u a hf ψ, fun h0 => by rw [h0]; exact map_zero _⟩
  constructor
  · intro hm
    refine (Submodule.mem_iInf _).2 fun P => (hz _).1 ?_
    exact (key P).symm.trans ((Submodule.mem_iInf _).1 hm.2 P)
  · intro hm
    refine ⟨StepZero.embF_mem_Fi _ _ _ _ hf _, (Submodule.mem_iInf _).2 fun P => ?_⟩
    exact (key P).trans ((hz _).2 ((Submodule.mem_iInf _).1 hm P))

theorem isCol_mem_ramSub_iff {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (_hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) (hc : IsCol I u a l x φ) :
    x ∈ (I.fm l u a).ramSub ↔ φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have hx : x = colForm I h u a ((l.fmL u a).fam 0) φ := Subtype.ext (funext hc)
  rw [hx]
  exact embF_colForm_mem_Mram I h u a ((l.fmL u a).fam 0) l φ

end GlobalTheory.Core.ColRam

end
