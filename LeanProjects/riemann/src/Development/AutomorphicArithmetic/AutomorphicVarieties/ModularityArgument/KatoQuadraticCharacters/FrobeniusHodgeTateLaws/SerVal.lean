import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu

noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.EisM GlobalTheory.KummerEisensteinGalois

namespace UpperTheory.V.Z.Kato.Joint

def ser {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) : ℕ → PadicAlgCl l :=
  up (l ^ m) fun i => ∑ x : ZMod N, ι.symm (hat θ (x.val : ℤ) / 2) * coPtMu N l m k ψ ((x.val : ℤ) * a) b i

def frm (l N m k : ℕ) (θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) : ℕ → ℂ :=
  (Uo l)^[m] (Zm k l (hat θ) (ch ν) fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))

def AvgEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ χ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ), l ≠ 2 → 1 ≤ m → 3 ≤ k → Odd k → χ (-1) = -1 → IsCoprime a N → IsCoprime b N →
    (ι (ψ (-1)) ≠ θ (-1) → ser ι N θ m k ψ a b = 0) ∧
    (∀ a' b' : ℤ, a ≡ a' [ZMOD N] → b ≡ b' [ZMOD N] → ser ι N θ m k ψ a b = ser ι N θ m k ψ a' b') ∧
    (ι (ψ (-1)) = θ (-1) → ∀ i, ∑ u : (ZMod N)ˣ, χ u * ι (ser ι N θ m k ψ (((u : ZMod N).val : ℤ) * a) (((u : ZMod N).val : ℤ) * b) i) =
      2 * θ (a : ZMod N) * (θ * χ)⁻¹ (b : ZMod N) * frm l N m k θ (θ * χ) (fun y => ι (ψ y)) i)

def AvgMF : Prop :=
  ∀ (k l N m : ℕ) (θ χ : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), l.Prime → 3 ≤ k → Odd k →
    0 < N → ¬ l ∣ N → 1 ≤ m → χ (-1) = -1 → (∀ y, f (-y) = θ (-1) * f y) → α ≠ 0 → EigAll k N l χ t α B c →
    MF k (N * l) (ch χ) (frm l N m k θ (θ * χ) f) ∧
      2 * lam B c (frm l N m k θ (θ * χ) f) = (N.totient : ℂ) * α ^ m * mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m f

def SerVal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (N : ℕ) [NeZero N] (θ χ : DirichletCharacter ℂ N) (m k : ℕ)
    (ψ : DirichletCharacter (PadicAlgCl l) (l ^ m)) (a b : ℤ) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ), l ≠ 2 → ¬ l ∣ N → 1 ≤ m → 3 ≤ k → Odd k →
    χ (-1) = -1 → IsCoprime a N → IsCoprime b N → α ≠ 0 → EigAll k N l χ t α B c → ι (ψ (-1)) = θ (-1) →
    lam B c (fun i => ι (ser ι N θ m k ψ a b i)) =
      θ (a : ZMod N) * (θ * χ)⁻¹ (b : ZMod N) * α ^ m * mesMu k l (hat θ) (tw2 N (θ (-1))) α B c m fun y => ι (ψ y)

end UpperTheory.V.Z.Kato.Joint

end
