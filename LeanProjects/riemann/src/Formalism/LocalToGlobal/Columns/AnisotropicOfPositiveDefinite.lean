import Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Adj

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjugateSplitOff {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : SplitOff S0 :=
  ⟨conjPrime₂ P.1, by
    obtain ⟨h1, h2, h3⟩ := P.2
    refine ⟨?_, ?_, ?_⟩
    · rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime]
      intro e
      exact h1 (by rw [conjIdeal_asIdeal, e])
    · intro hm
      exact h3 _ hm (conjIdeal_asIdeal P.1).symm
    · intro Q hQ e
      rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime] at e
      have hQP : Q = P.1 := HeightOneSpectrum.ext e
      exact h2 (hQP ▸ hQ)⟩

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

theorem mem_neighbour_iff_conj (c : DecoPts S E n ST SG) (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (d d' : S.D) :
    d ∈ c.nb P.asIdeal i d' ↔ d' ∈ c.nb (conjPrime₂ P).asIdeal i d := by
  rw [c.mem_nb, c.mem_nb, DecoSet.mem_heckeNb P.ne_bot (conjIdeal_ne_bot P.ne_bot),
    DecoSet.mem_heckeNb (conjPrime₂ P).ne_bot (conjIdeal_ne_bot (conjPrime₂ P).ne_bot)]
  constructor
  · rintro ⟨hn, hf, hb⟩
    exact ⟨wmp_isHeckeNbr_symm (c.pts d').2.lat (c.pts d).2.lat (c.pts d').2.uni (c.pts d).2.uni hn, hf.symm, hb.symm⟩
  · rintro ⟨hn, hf, hb⟩
    have h' := wmp_isHeckeNbr_symm (c.pts d).2.lat (c.pts d').2.lat (c.pts d).2.uni (c.pts d').2.uni hn
    rw [conjugatePrime_conjugatePrime] at h'
    exact ⟨h', hf.symm, hb.symm⟩

theorem neighbour_smul_iff (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (i : ℕ) (g : S.G) (d' d : S.D) :
    g • d ∈ c.nb P i (g • d') ↔ d ∈ c.nb P i d' := by
  rw [c.mem_nb, c.mem_nb, c.pts_smul, c.pts_smul]
  exact DecoSet.smul_mem_heckeNb_iff (c.hom g)

theorem heckeOperator_adjoint_conj (c : DecoPts S E n ST SG) (h : S.Ok) (P : HeightOneSpectrum (𝓞 E)) (i : ℕ) (φ ψ : S.EqFun) :
    S.ip h ((heckeD c P.asIdeal i).op φ) ψ = S.ip h φ ((heckeD c (conjPrime₂ P).asIdeal i).op ψ) := by
  have key := LocOp.ofNbr_adjoint (S := S) (S' := S) h h (MulEquiv.refl S.G) (c.nb P.asIdeal i)
    (c.nb (conjPrime₂ P).asIdeal i) LinearMap.id LinearMap.id (fun g d' d => neighbour_smul_iff c _ i g d' d) (fun _ _ => rfl)
    (fun g d d' => neighbour_smul_iff c _ i g d d') (fun _ _ => rfl) (fun d d' => mem_neighbour_iff_conj c P i d d') Iff.rfl
    (fun _ _ => rfl) S.outSec S.outSec φ ψ
  exact key

end Adj

section Aniso

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Aniso

section ThZero

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ThZero

section Final2

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Final2

end Formalism.L2.Col
