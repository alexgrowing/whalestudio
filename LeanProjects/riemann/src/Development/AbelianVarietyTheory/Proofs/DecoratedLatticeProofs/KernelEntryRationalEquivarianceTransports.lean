import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne

noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
