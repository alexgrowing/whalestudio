import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.RowEx.DatTw

open Formalism.L2.Host

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have e := congrArg (Int.cast : ℤ → R) huv
  push_cast at e
  rw [← e]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem unrAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v)
    (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  rw [HChar.loc_mul, h x hx, h' x hx, one_mul]

theorem unrAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt v := fun _ _ => rfl

variable {R : Ranks} (H : Host R)

theorem unrAt_of_isTwist {S : Set ℕ} (hS : GlobalTheory.EX.DC.q0H H ∈ S) {ψ : HChar H.E} (hψ : Chr.IsTwist H S ψ)
    {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) : ψ.UnrAt v := by
  by_contra h
  obtain ⟨-, hpr, -, hnot⟩ := hψ.2.2.2 v h
  by_cases e : Ideal.absNorm v.asIdeal = GlobalTheory.EX.DC.q0H H
  · exact hnot (e ▸ hS)
  · exact not_two_primes v.asIdeal hpr (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 e (Ideal.absNorm_mem _) hv

theorem not_overP_pde {v : HeightOneSpectrum (𝓞 H.E)} (hv : ((GlobalTheory.EX.DC.q0H H : ℕ) : 𝓞 H.E) ∈ v.asIdeal) :
    ¬ OverP H H.pde v ∧ ¬ OverP H H.pde' v :=
  ⟨fun h => not_two_primes v.asIdeal H.pde_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).1.symm h hv,
    fun h => not_two_primes v.asIdeal H.pde'_prime (GlobalTheory.EX.DC.globalTwisting_spec_fact H).1 (GlobalTheory.EX.DC.q0H_ne_pde_and_ne_pde' H).2.symm h hv⟩

theorem unrAt_of_mem_set {B : Base} {f : Fr B.toPre} {T : TwDat B} {ξ : HChar B.host.E} (h : ξ ∈ T.set f)
    {v : HeightOneSpectrum (𝓞 B.host.E)} (hv : ((GlobalTheory.EX.DC.q0H B.host : ℕ) : 𝓞 B.host.E) ∈ v.asIdeal) : ξ.UnrAt v := by
  have hd := not_overP_pde B.host hv
  have hdel : f.del.UnrAt v := f.isDel.unr v hd.1
  have hdel' : f.del'.UnrAt v := f.isDel'.unr v hd.2
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at h
  rcases h with (rfl | rfl | rfl) | ⟨w, rfl⟩
  · exact unrAt_one v
  · exact hdel
  · exact hdel'
  · unfold TwDat.xiTw
    refine unrAt_mul ?_ (unrAt_of_isTwist B.host ?_ (T.psi_tw w) hv)
    · split_ifs
      · exact hdel'
      · exact hdel
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

end GlobalTheory.RowEx.DatTw

theorem GlobalTheory.RowEx.twisted_data_off_base_level : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), GlobalTheory.RowEx.TwistPlacesOffPrimeQZero z.R.toLevCh ∧ z.R.C = Fr.at (w.st Z) f ∧
      (T.set f).Finite ∧ ∀ t, z.R.xiH t ∈ T.set f := by
  intro B f T w Z hX Wt z
  have hmem : ∀ t, z.R.xiH t ∈ T.set f := fun t => by
    rw [z.lev.xiH t, ← w.xi_range]
    exact ⟨_, rfl⟩
  refine ⟨fun t PP hPP hq => ?_, ?_, ?_, hmem⟩
  · exact (z.lev.is.Q_ram t PP).2 (Or.inl hPP) (GlobalTheory.RowEx.DatTw.unrAt_of_mem_set (hmem t) hq)
  · rw [z.lev.C, w.C_eq]
  · rw [← w.xi_range]
    exact Set.finite_range _
