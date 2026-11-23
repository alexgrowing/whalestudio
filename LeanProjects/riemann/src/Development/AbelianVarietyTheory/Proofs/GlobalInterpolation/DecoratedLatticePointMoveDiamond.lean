import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL

noncomputable section

namespace GlobalTheory.LvT.Built

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem levelPrimeDatum_diamond_invariant {E : Type} [Field E] [NumberField E] [StarRing E] (K : Type) [Field K] {n n' : ℕ}
    {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ST SG) (d' : DecoSet E n' ST SG') (P : ST)
    (a : (𝓞 E ⧸ P.1.asIdeal)ˣ) : phiT K (DecoSet.dia1 P a d).1 (DecoSet.dia1 P a d').1 = phiT K d.1 d'.1 := by
  funext x
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun Q => forall_congr' fun y => ?_
  refine imp_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [DecoSet.dia1, DecoSet.dia, Deco.dia]
  exact Units.mul_right_inj _

theorem decoratedLatticePoint_move_diamond {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} (p : PtY ST SG Q y) (P : ST)
    (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.deco = DecoSet.dia1 P a p.1.1.deco ∧
      (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.1.fr = p.1.1.fr ∧ (p.mv (DecoSet.dia1 P a p.1.1.deco)).1.2 = p.1.2 := by
  have h : p.mv (DecoSet.dia1 P a p.1.1.deco) =
      ⟨(⟨(DecoSet.dia1 P a p.1.1.deco, p.1.1.1.2), p.1.1.2⟩, p.1.2), p.2⟩ := dif_pos ⟨p.1.1.2, p.2⟩
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

theorem kAt_dia : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → ∀ b b' d d' (P : Pr.vT u) a, kAt W Ch sel mu cst L A u i b b' ((tdatAt sel mu cst L Tp u i).dia b P a d) ((tdatAt sel mu cst L Tp u (i + 1)).dia b' P a d') = kAt W Ch sel mu cst L A u i b b' d d' := by
  intro X Pr R W Ch sel S mu cst L G m2 u i _ _ _ _ _ Tp A h b b' d d' P a
  obtain ⟨Ξ, -, -, -, -, h⟩ := h b b' d d'
  have key : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p (p.mv (DecoSet.dia1 P a p.1.1.deco)) := by
    intro j p
    obtain ⟨h1, h2, h3⟩ := decoratedLatticePoint_move_diamond p P a
    refine ⟨?_, ?_, h2.symm, h3.symm⟩
    · rw [h1]; exact fun _ _ => rfl
    · rw [h1]; rfl
  have h0 := h d d' ⟨fun _ _ => rfl, rfl, rfl, rfl⟩ ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have h1 := h _ _ (key d) (key d')
  refine h1.trans (Eq.trans ?_ h0.symm)
  rw [(decoratedLatticePoint_move_diamond d P a).1, (decoratedLatticePoint_move_diamond d' P a).1]
  unfold GlobalTheory.KerT.term
  rw [levelPrimeDatum_diamond_invariant]
  rfl

end GlobalTheory.LvT.Built
