import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupleUnitaryFormsEquivPeriodRowForms

noncomputable section

namespace GlobalTheory.Transport.TwistCpl

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem intAt_inv_pow_mul {P : HeightOneSpectrum (𝓞 E)} {q B c : ℕ} (hq : (q : E) ≠ 0) {z : E}
    (hz : P.valuation E z ≤ P.valuation E (((q ^ B * c : ℕ) : ℕ) : E)) : IntAt P (((q : E) ^ B)⁻¹ * z) := by
  rw [intAt_iff_val, map_mul, map_inv₀]
  have hc : P.valuation E ((c : ℕ) : E) ≤ 1 :=
    (intAt_iff_val P _).1 ⟨(c : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have h1 : P.valuation E z ≤ P.valuation E ((q : E) ^ B) := by
    refine hz.trans ?_
    rw [Nat.cast_mul, Nat.cast_pow, map_mul]
    exact mul_le_of_le_one_right' hc
  have h0 : P.valuation E ((q : E) ^ B) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq)
  exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h1

end GlobalTheory.Transport.TwistCpl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

theorem GlobalTheory.Transport.TwistCpl.psiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 = B.R.m) (al : (I.idx a).β i) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q' = cosetIn p' →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                ((Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2)) =
        Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2)) := by
  intro B X I hI l u a i hm al P p q p' q' k y k' y' hp hN hp' hN' hq hq' hc
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = i by omega] at hL
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · refine ⟨Formalism.L2.Col.qOf P.1, Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    exact GlobalTheory.Transport.Pen.psiAt_frames (base_fields_primes_ok B X).1 l.pr hL al P hP p q p' q' hp hN hp' hN' hq hq' hc
      (GlobalTheory.Transport.Pen.lt_of_congAt hx)
  · have hPQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hq0n : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 hq0n
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (Nat.pos_of_ne_zero hq0n) _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hr := GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound I u a i P hPQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hm' : i + 1 + 1 = B.R.m := by omega
    set x₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hx₁
    set x₂ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hx₂
    set y₁ := (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2) with hy₁
    set y₂ := (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2) with hy₂
    have s1 := hL.psiInvX al P x₁ (x₂ - x₁) y₁ fun s l => by
      have := hr l s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply] at this
      exact GlobalTheory.Transport.TwistCpl.intAt_inv_pow_mul hq0 (by rw [LinearMap.sub_apply, Pi.sub_apply]; exact this)
    rw [add_sub_cancel] at s1
    rw [← s1]
    have h1 : y₁ ∈ cosetIn p' P := ⟨_, p'.repY_mem hm', by simp [hy₁]⟩
    rw [← hc] at h1
    obtain ⟨z, hz, h2⟩ := h1
    rw [if_neg hP] at h2
    have h3 := add_mem h2 ((GlobalTheory.TopLaw.coset_sub q'.1.1 (q'.mem_ybSet hm') hz (q'.repY_mem hm') P).2 hP)
    rw [← smul_add, sub_add_sub_cancel] at h3
    have h4 := hL.psiInv al P x₂ y₂ (y₁ - y₂) fun j => by
      rw [if_neg hP]
      open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep in exact mem_stdAt.1 h3 j
    rwa [add_sub_cancel] at h4
