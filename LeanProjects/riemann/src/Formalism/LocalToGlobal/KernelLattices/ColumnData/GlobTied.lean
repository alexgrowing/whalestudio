import Mathlib
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.ReferenceKernelEquivOfLastComponent
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivStmt

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Sel

variable {X : Fields} (Pr : Primes X)

def ReadAt (P : HeightOneSpectrum (𝓞 X.E)) : Prop := P ∈ Pr.vGs ∨ ∃ u, P ∈ Pr.vT u

theorem exists_over (X : Fields) (v : HeightOneSpectrum (𝓞 X.F)) :
    ∃ P : HeightOneSpectrum (𝓞 X.E), P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 X.F) (𝓞 X.E)) := FaithfulSMul.algebraMap_injective (𝓞 X.F) (𝓞 X.E)
  have hv := v.isPrime
  obtain ⟨Q, _, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 X.E))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  refine ⟨⟨Q, hQ, ?_⟩, hc⟩
  rintro rfl
  exact v.ne_bot (hc ▸ Ideal.comap_bot_of_injective _ hinj)

open Classical in

def selC (v : HeightOneSpectrum (𝓞 X.F)) : HeightOneSpectrum (𝓞 X.E) :=
  if h : ∃ P, ReadAt Pr P ∧ P.asIdeal.under (𝓞 X.F) = v.asIdeal then h.choose
  else (exists_over X v).choose

end Sel

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m)

abbrev chr0 (X : Fields) (S : Set ℕ) : Chr X.F X.E X.K := ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K)

def cstC (n : ℕ) : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S)) :=
  { ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) (ciMuq Gc (chr0 X S)) with A := n, B := n, sharp := true }

abbrev idxC (m2 : ℕ) : ChIdx X Pr R (QE sel (chr0 X S)) := oneIdx Λ (QE sel (chr0 X S)) m2

abbrev alC (m2 : ℕ) : ∀ j, j ≤ m2 + 1 → (idxC Λ sel S m2).β j := oneAl Λ sel (mu0 X.F X.E X.K S) m2

structure DepthOk (n m2 : ℕ) : Prop where
  deep : ∀ A' B', n ≤ A' → n ≤ B' → ∀ i, i < m2 → ∀ P : rowSG Pr sel (mu0 X.F X.E X.K S),
    E1at Ch sel _ { cstC Ch sel S Gc n with A := A', B := B' } i P 1 1 = E1at Ch sel _ (cstC Ch sel S Gc n) i P 1 1
  xiSupp : ∀ i, i < m2 → ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x : HomE X.E (R.N i) (R.N (i + 1))),
    XiAt Ch sel _ (cstC Ch sel S Gc n) i P 1 1 x ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ n * x (Pi.single s 1) l)
  xiInv : ∀ i, i < m2 → ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x z : HomE X.E (R.N i) (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ n)⁻¹ * z (Pi.single s 1) l)) →
      XiAt Ch sel _ (cstC Ch sel S Gc n) i P 1 1 (x + z) = XiAt Ch sel _ (cstC Ch sel S Gc n) i P 1 1 x
  psiSuppX : ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    PsiAt Ch sel _ (cstC Ch sel S Gc n) m2 P 1 x₀ y' ≠ 0 → ∀ s l, IntAt P.1 ((qOf P.1 : X.E) ^ n * x₀ (Pi.single s 1) l)
  psiInvX : ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ n)⁻¹ * z (Pi.single s 1) l)) →
      PsiAt Ch sel _ (cstC Ch sel S Gc n) m2 P 1 (x₀ + z) y' = PsiAt Ch sel _ (cstC Ch sel S Gc n) m2 P 1 x₀ y'

open Classical in

def PsiInvY (n m2 : ℕ) : Prop :=
  ∀ (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' z : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else (cstC Ch sel S Gc n).M))⁻¹ * z i)) →
      PsiAt Ch sel _ (cstC Ch sel S Gc n) m2 P 1 x₀ (y' + z) = PsiAt Ch sel _ (cstC Ch sel S Gc n) m2 P 1 x₀ y'

variable (R) in

def PrInt (m2 : ℕ) : Prop :=
  ∀ j, j ≤ m2 + 1 → ∀ P : rowSG Pr sel (mu0 X.F X.E X.K S), prCat (Pr := Pr) true j P.1 (1 : AutY X R j) ≤ GLint X.E (R.N j) P.1

structure GlobTied : Prop where
  weil : Ch.WeilTied Gc.σ₀ Gc.xi0
  xi : ∀ w ∈ Pr.vGs, IntAt w Gc.xi0 ∧ redP w Gc.xi0 ≠ 0
  mu : ∀ (j : Fin R.m) (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
    (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
    (((Gc.mu0 j).locK w.1 x : ℂˣ) : ℂ) = Gc.σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K)
  val : ∀ (j : Fin R.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
    ∃ y : X.K, Gc.σ₀ y = ((((Gc.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹

structure IdxHyp (n m2 : ℕ) : Prop where
  zero : Λ 0 = colLev Ch 0
  depth : DepthOk Ch sel S Gc n m2
  one : OneCosetSym Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) Λ m2
  nonvan : NonVanSym Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) m2
  psiInv : PsiInvY Ch sel S Gc n m2
  prInt : PrInt (Pr := Pr) R sel S m2

end Fin

section Dat

variable (d : ColDat) (S : Set ℕ)

def globD (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E) : ChGlob d.X d.R.m := ⟨d.σ₀, d.host.xi0, m0⟩

abbrev selD : HeightOneSpectrum (𝓞 d.X.F) → HeightOneSpectrum (𝓞 d.X.E) := selC d.Pr

abbrev cstD (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E) (n : ℕ) : LocCst d.X (rowSG d.Pr (selD d) (mu0 d.X.F d.X.E d.X.K S)) :=
  cstC d.Ch (selD d) S (globD d m0) n

abbrev idxD (m2 : ℕ) : ChIdx d.X d.Pr d.R (QE (selD d) (chr0 d.X S)) := idxC d.lev (selD d) S m2

abbrev alD (m2 : ℕ) : ∀ j, j ≤ m2 + 1 → (idxD d S m2).β j := alC d.lev (selD d) S m2

end Dat

end Formalism.L2.Ker
