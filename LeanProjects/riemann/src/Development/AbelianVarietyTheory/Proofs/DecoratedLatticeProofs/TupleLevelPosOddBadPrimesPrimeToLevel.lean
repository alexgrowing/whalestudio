import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TupLevel

theorem odd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (h : (2 : 𝓞 E) ∉ P.asIdeal) :
    Odd (Ideal.absNorm P.asIdeal) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  haveI := P.isPrime
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h2
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) 2 h2
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact absurd hx (by norm_num)
  have h1 : (2 : 𝓞 E ⧸ P.asIdeal) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, two_nsmul] at this
    rw [two_mul, this]
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact h (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_ofNat]; exact h3))
  · exact h0 h3

theorem odd_levC {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    (hX : X.Ok) (hPr : Pr.Ok) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (u : Pr.Word)
    (h2 : ∀ P ∈ Formalism.L2.Col.Sall sel mu u, (2 : 𝓞 X.E) ∉ P.asIdeal) : Odd (levC sel mu cst u) := by
  have hp : Odd (∏ P : Formalism.L2.Col.rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) :=
    Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun P _ =>
      odd_absNorm P.1 (h2 P.1 (Finset.mem_union.2 (Or.inr P.2)))
  obtain ⟨P₀, hP₀⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  have hT : Odd (Pr.T u) := hPr.vT_norm u P₀ hP₀ ▸ odd_absNorm P₀ (h2 P₀ (Finset.mem_union.2 (Or.inl hP₀)))
  exact hp.pow.mul (hT.mul hp.pow)

theorem levC_pos_odd_and_off : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  intro B X I hI _ u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hc : (B.primes X).cond = B.host.QS * B.host.q * B.host.d := rfl
  have h2 := fun Q (hQ : Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u) =>
    GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u Nat.prime_two (hI.ram_mem 2 Nat.prime_two B.host.toHostRaw.two_dvd_condN)
      (by rw [hc]; exact B.host.toHostRaw.two_dvd_condN) hQ
  have ho : Odd (levC I.sel (I.tup a) (I.cst a) u) :=
    odd_levC hXo hPr (I.cst a) u fun Q hQ h => h2 Q hQ (by exact_mod_cast h)
  refine ⟨ho.pos, ho, fun Q hQ h => ?_⟩
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q.asIdeal
  by_cases hd : l ∣ B.host.QS * B.host.q * B.host.d
  · exact GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u hl (hI.ram_mem l hl hd) (by rw [hc]; exact hd) hQ hlP
  · exact UpperTheory.Ram.natCast_notMem_of_coprime Q.isPrime.ne_top hlP ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm h

end GlobalTheory.TupLevel
