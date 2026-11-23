import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def LocMv (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1) : Prop :=
  (I.stp u a i).gam c.1 κ = 1 ∧
    cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
    ∀ g : GA B (B.R.N i), PtOf g ((I.stp u a i).rep c).1.1 → PtOf (g * s) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1

theorem reads_of_locMv (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (κ : (I.stp u a i).G c.1) (h : LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ) :
    ∃ hx : x ∈ U (chOf c), ((chi (chOf c) ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hq := h.2.2 _ hp
  rw [e] at hq
  have hx : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ, h.1, rfl, h.2.1⟩
  exact ⟨hx, hR.chr c ⟨x, hx⟩ κ h.1 hq⟩

end GlobalTheory.Mem.Col2.TC.ChTw
