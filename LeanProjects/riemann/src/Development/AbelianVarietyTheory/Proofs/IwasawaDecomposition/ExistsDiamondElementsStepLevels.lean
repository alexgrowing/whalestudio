import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

theorem exists_int_isDia {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) :
    ∃ k : ℤ, (k : (D.mem u).A.Fv v) = a ∧
      ∀ {n f : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
        (S : StepLevel D.host.F D.host.E (sigD D) J (D.mem u).A.T f bad), ∃ δ, IsDia S (A.eV v).1 (A.eV v).2 k δ := by
  obtain ⟨k, hk, hkT⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.unit_lift_int_prime_field (D.mem u).A.T_prime ((D.mem u).A.card_Fv v) a
  obtain ⟨e, he, hee, hσ⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.splitAtT_of_tied A v
  exact ⟨k, hk, fun S => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.is_diamond_of_local_diamond S _ _ k
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.local_diamond_of_split_idempotent S _ _ (D.mem u).A.T_prime k hkT e he hee hσ)⟩

set_option maxHeartbeats 1000000 in

theorem exists_isDia_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : ((I.rec7 l Z).mem u).A.Fv v) = a ∧ (∀ h : i = 0 ∨ i = (I.rec7 l Z).R.m, ∃ δ, IsDia ((F u).cls i hi h).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ) ∧ ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), ∃ δ, IsDia ((F u).ch i h1 h2 β).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ := by
  intro B X I _ _ l Z H F _ _ u i hi v a
  obtain ⟨k, hk, h⟩ := exists_int_isDia (F u).atT v a
  exact ⟨k, hk, fun _ => h _, fun _ _ _ => h _⟩

end GlobalTheory.Mem.Col2.HAt
