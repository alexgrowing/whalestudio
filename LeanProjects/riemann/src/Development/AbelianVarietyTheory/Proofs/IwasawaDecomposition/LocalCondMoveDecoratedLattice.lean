import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

def LocalCondMoveDecoratedLattice (u : B.Word) (n : ℕ) (s : GA B n) (h : GLG B.fields.E n (B.primes X).vGs) : Prop :=
  s ∈ Formalism.L2.Herm.UstdAf B.sp.cm n ∧ Formalism.L2.Herm.Carries s (stdLat B.fields.E n) (stdLat B.fields.E n) ∧
  (∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n →
    HasRes P.1 (adAt B.host.F P.1 ((s⁻¹ : GA B n).1 r j)) (if j = r then 1 else 0)) ∧
  ∀ (w : (B.primes X).vGs) (r j : Fin n), HasRes w.1 (adAt B.host.F w.1 ((s⁻¹ : GA B n).1 r j)) ((h w).1 r j)

def LocCQ (Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))) (n : ℕ) (s : GA B n) (θ : GLQ B.fields.E n Q) : Prop :=
  ∀ (P : Q) (r j : Fin n), adAt B.host.F P.1 ((s : Matrix (Fin n) (Fin n) _) r j) =
    algebraMap B.host.E _ ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
