import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.DiaTheta

theorem decoratedPoint_move_diamondOperator_eq {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    p.mv (DecoSet.dia1 P a p.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ :=
  dif_pos ⟨p.1.1.2, p.2⟩

theorem xiAt_dia {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (u : Pr.Word) (i : ℕ) (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)) (p : PtAt R sel mu cst u i)
    (p' : PtAt R sel mu cst u (i + 1)) (P : Pr.vT u) (s : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    xiAt Ch sel mu cst L u i b b' (p.mv (DecoSet.dia1 P s p.1.1.deco)) (p'.mv (DecoSet.dia1 P s p'.1.1.deco)) =
      xiAt Ch sel mu cst L u i b b' p p' := by
  rw [decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  have hT := GlobalTheory.LvT.Built.levelPrimeDatum_diamond_invariant X.K p.1.1.deco p'.1.1.deco P s
  funext x
  unfold xiAt
  split_ifs with h1 h2 h3
  · unfold XiEntry
    exact congrArg (· * _) (congrFun hT x)
  · unfold XiCpl1
    exact congrArg (· * _) (congrFun hT x)
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by have := R.two_le_m; omega⟩
    show xiOver Ch sel mu cst n h3 _ _ _ x = xiOver Ch sel mu cst n h3 _ _ _ x
    unfold xiOver
    exact congrArg (· * _) (congrFun hT x)
  · rfl

end GlobalTheory.DiaTheta

namespace GlobalTheory.DiaTheta

theorem th_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (b' : (I.stp u a (i + 1)).β) (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.th u a i b b' (((I.atIn u a).A i).dia b P s p) (((I.atIn u a).A (i + 1)).dia b' P s p') = I.th u a i b b' p p' := by
  intro B X I _ u a i b b' p p' P s
  have e1 : ((I.atIn u a).A i).dia b P s p = PtY.mv p (DecoSet.dia1 P s p.1.1.deco) := rfl
  have e2 : ((I.atIn u a).A (i + 1)).dia b' P s p' = PtY.mv p' (DecoSet.dia1 P s p'.1.1.deco) := rfl
  rw [e1, e2]
  unfold TC.th thAt
  rw [xiAt_dia I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i b b' p p' P s, decoratedPoint_move_diamondOperator_eq, decoratedPoint_move_diamondOperator_eq]
  rfl

end GlobalTheory.DiaTheta
