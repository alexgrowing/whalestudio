import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PtTwist

open GlobalTheory.Mem.Col2.PtExist

theorem exists_ptOf_twists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ)
    (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  classical
  intro B X I hI u n p
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨hlev, hGQ, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)

  have hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P hP => by
    have h1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 hP
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h1

  have hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ),
      ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P m => by
    rw [mem_conjP, map_natCast]

  have hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP =>
    T_notMem_vGs hPr u ⟨P, hP⟩

  have hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP h => by
    have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u
  have hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs :=
    Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)
  have hTQ : Disjoint ((B.primes X).vT u) I.SQ :=
    Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)
  have hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP => by
    rcases Finset.mem_union.1 hP with h | h
    exacts [hG P h, hQ P h]
  refine PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  ·
    have a1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 h1
    have a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := (mem_divs hT0 _).1 h2
    rw [mem_conjP] at a2
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    have : (1 : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · exact hout _ h2 ((hcj P _).2 (hTin P h1))
  · exact hout P h1 ((hcj P _).1 (hTin _ h2))
  · exact hlev.split P h1 h2

end GlobalTheory.Mem.Col2.PtTwist
