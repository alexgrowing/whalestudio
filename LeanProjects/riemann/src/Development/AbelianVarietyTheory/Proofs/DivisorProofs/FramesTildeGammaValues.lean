import Mathlib
import Formalism.LocalToGlobal.Divisibility.ColPins
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumLeFrameNormSqGoodPartStatement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColEvNorm

open Formalism.L2.Col in
theorem rowCast_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
    (Λ' : LevFam X.E X.K (R.N R.m - 1) SG') (hΛ : Λ' = e ▸ A) :
    Function.Injective (rowCast W e A Λ' hΛ) := by
  subst hΛ
  subst e
  intro F G h
  exact h

open Formalism.L2.Col in
theorem zOfRow_injective {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S)
    (hQ : QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs) (σ₀ : X.K →+* ℂ)
    (hM : (rowGSD W (rowTyG Ch P).inv).Ok) :
    Function.Injective (zOfRow W Ch sel mu hQ P σ₀ hM) := by
  intro F G h
  apply rowCast_injective W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P)
  apply ((rowGSD W (rowTyG Ch P).inv).hB hM).repr.injective
  ext a
  exact σ₀.injective (congrFun h a)

end GlobalTheory.ColEvNorm

namespace GlobalTheory.ColEvNorm

open Formalism.L2.Col in

theorem ipAt_le_of_ties {Xf : Fields} [IsTotallyComplex Xf.K]
    (Pr : Primes Xf) (Rk : Ranks) (W : Wts Xf Pr.Word Rk) (Ch : Chars Xf Pr Rk.m)
    (sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)) {Sg : Set ℕ} (hX : Xf.Ok)
    (Lv : LevFam Xf.E Xf.K Rk.r Pr.vGs) (Xg : Finset (G0 Xf.E Pr.vGs Rk.r → Xf.K)) (v0 : InfinitePlace Xf.K)
    (TU : Finset (Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg))
    (xiVal : Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg → HeightOneSpectrum (𝓞 Xf.E) → Xf.Kˣ)
    (trIv : Fin Rk.m → (LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K) → LevOffI ∅ Pr.vGs ∅ × List ℕ → Xf.K)
    {Gp : Type} [grp : Group Gp] [fin : Fintype Gp] {Pl0 I0 Tt : Type} {m : ℕ}
    (A3 : FamIn3 Xf.K Gp Pl0 I0 (List ℕ) Tt m) (Ps : Subgroup Gp) (ψs : Ps →* Xf.Kˣ) (Zs : DefSub A3.fam3.amb3)
    (mu : A3.fam3.base3.Tup → Formalism.L2.DIV.Tup Xf.F Xf.E Xf.K Sg) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) Lv).Ok)
    (gEq : Gp = G0 Xf.E Pr.vGs Rk.r) (hgrp : HEq grp (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)))
    (hm3 : Rk.m = m) (plEq : Pl0 = LevOff ∅ Pr.vGs ∅) (i0Eq : I0 = LevOffI ∅ Pr.vGs ∅) (tEq : Tt = TupF TU)
    (famEq : HEq A3 (colIn3 W Ch sel hX v0 TU Xg ∅ xiVal trIv))
    (muTie : ∀ t, mu t = (cast tEq t).1) (ok1 : A3.fam3.Ok3 1)
    (hps1 : HEq Ps Lv.grp) (hps2 : HEq ψs Lv.chr)
    (X0 : InfinitePlace Xf.K → Matrix (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))
      (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0)) ℂ)
    (hX0 : GlobalTheory.ColRows.IsFrames (A3.side3 Ps ψs Zs) X0) (v : InfinitePlace Xf.K)
    (F : Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0) → Xf.K)
    (F' : (mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).EqFun)
    (hm : F'.1 ∈ (mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).EqFun)
    (hres : HEq ((mtildeKGSD W Ch sel (mu A3.fam3.base3.μ0)).res (mtildeKOk W Ch sel (mu A3.fam3.base3.μ0) hX) F')
      ((A3.A.fam.R A3.fam3.base3.μ0).S.basis.equivFun.symm
        (((A3.A.fam.R A3.fam3.base3.μ0).S.cutE (A3.A.fam.R A3.fam3.base3.μ0).r
          (lvlIdem (A3.A.fam.lvl Ps ψs).P (A3.A.fam.lvl Ps ψs).ψ)).mulVec
          (((A3.A.fam.R A3.fam3.base3.μ0).S.lvlPr (A3.A.fam.R A3.fam3.base3.μ0).r (A3.A.fam.lvl Ps ψs).P
            (A3.A.fam.lvl Ps ψs).ψ * (A3.A.fam.R A3.fam3.base3.μ0).vE (A3.A.fam.lvl Ps ψs)).mulVec F)))) :
    ((mtildeGSD W Ch sel (mu A3.fam3.base3.μ0) Lv).ipAt (hP A3.fam3.base3.μ0) v F'.1 F'.1).re ≤
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun Xf.K (Fin ((A3.side3 Ps ψs Zs).nV A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  subst gEq
  have hg : grp = (Pi.group : Group (G0 Xf.E Pr.vGs Rk.r)) := eq_of_heq hgrp
  subst hg
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let g' ← g.withContext do
      let lctx ← Lean.getLCtx
      let some fe := lctx.findFromUserName? `famEq | throwError "famEq"
      let some fi := lctx.findFromUserName? `fin | throwError "fin"
      let t ← Lean.instantiateMVars fe.type
      let ty ← Lean.Meta.whnf (← Lean.Meta.inferType t.appArg!)
      let inst := ty.getAppArgs[6]!
      let pf ← Lean.Meta.mkAppM ``Subsingleton.elim #[fi.toExpr, inst]
      let (_, g') ← g.note `hfin pf
      pure g'
    Lean.Elab.Tactic.replaceMainGoal [g']
  subst hfin
  subst hm3
  subst plEq
  subst i0Eq
  subst tEq
  have hA := eq_of_heq famEq
  subst hA
  have hp1 := eq_of_heq hps1
  subst hp1
  have hp2 := eq_of_heq hps2
  subst hp2
  have hmuE : mu = fun t => t.1 := funext muTie
  subst hmuE
  exact GlobalTheory.T.classSum_le_frameNorm_sq_good_part Xf Pr Rk W Ch sel Sg hX v0 TU Xg ∅ xiVal trIv Lv Zs _ (hP _) ok1 F F' hm hres v X0
    (hX0 v).1 (hX0 v).2

end GlobalTheory.ColEvNorm

theorem GlobalTheory.ColEvNorm.ev_ipAt_le_normAt_sq : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : Formalism.L2.TiedDataSK ex) (P : RowSideFamily ex) (K : SquareIntegrableColumnsCompatible T P), ColPins K → K.c.mu P.A3.fam3.base3.μ0 = 1 → ∀ X0, IsFrames (P.A3.side3 P.Ps P.ψs P.Zs) X0 → ∀ v F, ((Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu P.A3.fam3.base3.μ0) K.c.Lv).ipAt (K.c.hP P.A3.fam3.base3.μ0) v ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1 ((K.c.ev P.Zs P.A3.fam3.base3.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.fam3.base3.μ0))) X0 v F ^ 2 := by
  intro D L hT Gi Gl Kc Y cX ex _ T P K hpin hmu X0 hX0 v F
  have ht : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu P.A3.fam3.base3.μ0 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
    rw [hmu]
    have h : Formalism.L2.DIV.Qprime ((1 : Formalism.L2.DIV.Tup K.X.F K.X.E D.what₂.LL K.c.Sg) : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅ := by
      change Formalism.L2.DIV.Qprime (1 : Formalism.L2.DIV.Chr K.X.F K.X.E D.what₂.LL) = ∅
      ext w
      simp [Formalism.L2.DIV.Qprime, MonoidHom.ker_one]
    unfold Formalism.L2.Col.QE
    split_ifs with hf
    · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
      rfl
    · rfl
  obtain ⟨hM, hev⟩ := hpin.columnEvaluationOk
  obtain ⟨ι, h1, h2⟩ := hev D.u₀
  obtain ⟨F', hm, hres, hι1⟩ := h1 _ ht hQ ((Formalism.L2.DIV.rV0 D P.A3.A P.Ps P.ψs P.A3.fam3.base3.μ0).mulVec F)
  obtain ⟨hm2, hι2⟩ := h2 _ ht hQ F
  have hz := hι1.symm.trans hι2

  have hF := congrArg Subtype.val (GlobalTheory.ColEvNorm.zOfRow_injective _ _ _ _ _ _ _ _ hz)
  rw [← hF]
  exact GlobalTheory.ColEvNorm.ipAt_le_of_ties (Xf := fieldsLL D K.X K.e) K.c.Pr K.c.Rk K.c.W K.c.Ch K.c.sel K.c.hX K.c.Lv K.c.Xg
    K.v0 K.TU K.xiVal K.trIv P.A3 P.Ps P.ψs P.Zs K.c.mu K.c.hP K.gEq hpin.grpTie
    (congrArg Ranks.m K.kerTie.2.1) K.plEq K.i0Eq K.tEq K.famEq K.muTie K.ok1 hpin.psTie.1 hpin.psTie.2
    X0 hX0 v F F' hm hres
