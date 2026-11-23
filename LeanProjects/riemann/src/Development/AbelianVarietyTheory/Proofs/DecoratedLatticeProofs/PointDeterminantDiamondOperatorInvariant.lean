import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DecoratedLatticePointMoveDiamond
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section
namespace GlobalTheory.KerDia.RhoDia

section Gen
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pointDeterminant_diamondOperator_invariant {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 H.E))} (p q : DecoF H.E n ST SG Q) (P : ST) (c : (𝓞 H.E ⧸ P.1.asIdeal)ˣ)
    (hd : q.deco = DecoSet.dia1 P c p.deco) (hfr : q.fr = p.fr) : detPt H SQ q = detPt H SQ p := by
  have hN : q.deco.1.N = p.deco.1.N := by rw [hd]; rfl
  have hbe : q.deco.1.be = p.deco.1.be := by rw [hd]; rfl
  have h := ptFr_congr (p := q) (p' := p) hN hbe hfr
  unfold detPt ptIdl
  rw [h, hN]

end Gen

theorem rho_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Laws → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (b : (I.stp u a i).β) (p : (I.stp u a i).D b) (b' : (I.stp u a (i + 1)).β) (p' : (I.stp u a (i + 1)).D b') (P : (I.atIn u a).ST) (s : (Res P.1)ˣ), I.rho u a i b (((I.atIn u a).A i).dia b P s p) = I.rho u a i b p ∧ I.rho' u a i b' (((I.atIn u a).A (i + 1)).dia b' P s p') = I.rho' u a i b' p' := by
  intro B X I _ u a i b p b' p' P s
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p P s
  obtain ⟨h1', h2', -⟩ := GlobalTheory.LvT.Built.decoratedLatticePoint_move_diamond p' P s
  have e := pointDeterminant_diamondOperator_invariant B.host I.SQ p.1.1 _ P s h1 h2
  have e' := pointDeterminant_diamondOperator_invariant B.host I.SQ p'.1.1 _ P s h1' h2'
  constructor
  · show ((rhoAt I.SQ I.C (I.xi a) i (p.mv (DecoSet.dia1 P s p.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt I.SQ I.C (I.xi a) i p.1.1 : ℂˣ) : ℂ)
    rw [rhoAt_eq, rhoAt_eq, e]
  · show ((rhoAt' I.SQ I.C (I.xi a) i (p'.mv (DecoSet.dia1 P s p'.1.1.deco)).1.1 : ℂˣ) : ℂ) = ((rhoAt' I.SQ I.C (I.xi a) i p'.1.1 : ℂˣ) : ℂ)
    rw [rhoAt'_eq, rhoAt'_eq, e']

end GlobalTheory.KerDia.RhoDia
