import Formalism.LocalToGlobal.Columns.RecChainUnfOne

open NumberField IsDedekindDomain Module
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure DetChr.Loc (Dc : DetChr X R.m) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.E →ₐ[X.F] X.E) : Prop where
  trivF : ∀ i, i < R.m → (Formalism.L2.DIV.h90 σ).ker ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  unr : ∀ i, i < R.m → ∀ y ∈ intU X.F X.E,
    (∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → Units.map (Formalism.UG.prV (E := X.E) v).toMonoidHom y = 1) →
    (Dc.muAt i * (mu : Chr X.F X.E X.K)) y = 1
  unif : ∀ i, i < R.m → ∀ P : HeightOneSpectrum (𝓞 X.E),
    (¬ ∃ P' ∈ rowSG Pr sel mu, P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)) →
    IsUnifVal (Dc.muAt i * (mu : Chr X.F X.E X.K)) P (mUof Ch mu i P)⁻¹
  tame : ∀ i, i < R.m → ∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    wildAt X.E v ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  res : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu,
    IsResChar (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1
      (open Classical in if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1)
  atq : ∀ i, i < R.m → ∀ (P : rowSG Pr sel mu) (k : X.Kˣ), IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k →
    cst.muq (i + 1) P = ((k⁻¹ : X.Kˣ) : X.K)
  atq_ex : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu, ∃ k : X.Kˣ, IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k
  trivChi : (Formalism.L2.DIV.h90 σ).ker ≤ Dc.chi.ker
  unrChi : ∀ y ∈ intU X.F X.E, Dc.chi y = 1

def PtSurjAll (hc : Formalism.BasicNotions.CMData X.F X.E) (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Prop :=
  ∀ n, n ≤ R.m → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
    letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
    decoOf (Pr.vT u) Pr.vGs (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) = p

def MuDetOfLoc : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (Dc : DetChr X R.m) (hc : Formalism.BasicNotions.CMData X.F X.E) (u : Pr.Word),
    X.Ok → Pr.Ok → (∀ v, (sel v).asIdeal.under (𝓞 X.F) = v.asIdeal) → Dc.Loc Ch sel (mu0 X.F X.E X.K S) cst hc.sig → PtSurjAll hc Pr R u →
    ∀ i, i < R.m → ∀ n, (n = i ∨ n = i + 1) → ∀ p : DecoSet X.E (R.N n) (Pr.vT u) Pr.vGs,
      letI : NeZero (R.N n) := ⟨(R.N_pos n).ne'⟩
      (((Formalism.L2.DIV.detTw hc.sig (Dc.muAt i)
          (ptOf hc (R.N n) (Pr.vT u) Pr.vGs p : GL (Fin (R.N n)) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))⁻¹ : X.Kˣ) : X.K) =
        muInvDet sel (rowSG Pr sel (mu0 X.F X.E X.K S)) (mUof Ch (mu0 X.F X.E X.K S) i) (muAt Ch sel (mu0 X.F X.E X.K S) cst i) p.1.N
          (frsD sel (mu0 X.F X.E X.K S) p)

end Loc

end Formalism.L2.Col
