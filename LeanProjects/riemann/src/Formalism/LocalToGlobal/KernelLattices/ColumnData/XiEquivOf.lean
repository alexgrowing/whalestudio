import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.GlobTied
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainOneP
import Formalism.LocalToGlobal.Columns.ExistsYOfOfMemYbSet

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Sel

variable {X : Fields} (Pr : Primes X)

end Sel

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (Gc : ChGlob X R.m)

theorem cstC_ok {n : ℕ} (hn : 1 ≤ n) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) : (cstC Ch sel S Gc n).Ok :=
  have h := ciCst_ok hPr hCh (SB := rowSG Pr sel (mu0 X.F X.E X.K S)) (fun P hP => bad_primes_over_g_trivial_tuple sel S ⟨P, hP⟩)
    (fun P hP => h4 P (bad_primes_over_g_trivial_tuple sel S ⟨P, hP⟩)) (mq := ciMuq Gc (chr0 X S))
  { psi_add := h.psi_add
    psi_int := h.psi_int
    psi_ne := h.psi_ne
    D_pos := h.D_pos
    sq_sq := h.sq_sq
    M_pos := h.M_pos
    M_le_A := hn
    M_le_B := hn
    B_pos := hn }

variable {Λ Ch sel S Gc}

theorem idxC_ok {n m2 : ℕ} (hm : R.m = m2 + 2) (hn : 1 ≤ n) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1)
    (hG : GlobTied Ch Gc) (H : IdxHyp Λ Ch sel S Gc n m2) :
    (idxC Λ sel S m2).Ok Ch sel (mu0 X.F X.E X.K S) (cstC Ch sel S Gc n) Gc m2 :=
  { hm := hm
    cst_ok := cstC_ok Ch sel S Gc hn hPr hCh h4
    xiUnitAtPrime := fun P => hG.xi P.1 (bad_primes_over_g_trivial_tuple sel S P)
    weil := ciCst_weil Ch hX hPr (fun P hP => bad_primes_over_g_trivial_tuple sel S ⟨P, hP⟩) (ciMuq Gc (chr0 X S)) hG.weil (fun P hP => (hG.xi P (bad_primes_over_g_trivial_tuple sel S ⟨P, hP⟩)).1)
    muqQ := fun _ _ P hP => absurd (bad_primes_over_g_trivial_tuple sel S P) hP
    muqG := fun i h P hP qu hqu => ciMuq_tie Gc _ hG.val i h P hP qu hqu
    mu0G := hG.mu
    psi0 := by
      intro P a _ ha
      show ciPsi Ch P _ = _
      have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr (bad_primes_over_g_trivial_tuple sel S P)).ne_zero
      unfold ciPsi
      rw [mul_div_cancel₀ _ hq0, if_pos ha]
    deep := fun A' B' hA hB i hi _ _ P => H.depth.deep A' B' hA hB i hi P
    zero_uniq := ⟨⟨(), Nat.zero_le _⟩, fun _ => Subtype.ext rfl⟩
    zero_h := fun _ _ => rfl
    zero_G := fun _ => H.zero
    zero_Q := fun _ => rfl
    last_uniq := ⟨⟨(), le_refl _⟩, fun _ => Subtype.ext rfl⟩
    last_h := fun _ _ => rfl
    nonvan := (oneIdx_clauses H.one H.nonvan).1
    inj := fun i hi b b' _ => (oneIdx_clauses H.one H.nonvan).2.1 i hi b b'
    surj := (oneIdx_clauses H.one H.nonvan).2.2
    stabG := fun _ _ _ _ => Subgroup.one_mem _
    depthG := fun _ _ => rfl
    depthQ := fun P hP => absurd (bad_primes_over_g_trivial_tuple sel S P) hP
    depthQ' := fun P hP => absurd (bad_primes_over_g_trivial_tuple sel S P) hP
    boundQ := fun _ _ P hP => absurd (bad_primes_over_g_trivial_tuple sel S P) hP
    psiSupp := fun _ P x₀ y' h i => by
      rw [if_pos (bad_primes_over_g_trivial_tuple sel S P), pow_one]
      exact ((oneYbSym_of_m Ch sel _ (cstC Ch sel S Gc n) hm rfl) P (bad_primes_over_g_trivial_tuple sel S P) x₀ y' h i).1
    psiInv := fun _ P x₀ y' z hz => H.psiInv P x₀ y' z hz
    xiSupp := fun i hi _ _ P x h => H.depth.xiSupp i hi P x h
    xiInv := fun i hi _ _ P x z hz => H.depth.xiInv i hi P x z hz
    psiSuppX := fun _ P x₀ y' h => H.depth.psiSuppX P x₀ y' h
    psiInvX := fun _ P x₀ z y' hz => H.depth.psiInvX P x₀ z y' hz
    int := fun j b P => H.prInt j b.2 P
    grpQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
    chrQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
    grpG := fun j b w hbar => H.one.grpG j b.2 w hbar
    chrG := fun j b w hbar g r hr hrg hred => H.one.chrG j b.2 w hbar g r hr hrg hred }

end Fin

section Hyp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (al : ∀ j, j ≤ m2 + 1 → L.β j) (Am : Amb X) (u : Pr.Word)

variable {W Λ Ch sel mu cst hQ m2 Am u}

end Hyp

end Formalism.L2.Ker
