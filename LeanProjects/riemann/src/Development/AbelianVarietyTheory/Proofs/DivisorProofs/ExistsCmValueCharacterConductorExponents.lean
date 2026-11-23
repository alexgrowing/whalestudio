import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.SqNum.CondExps

theorem exists_condExps : ∀ (D : D7) [IsCMField D.host.E] {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (s : ℕ)
    (κ : D.what₂.Tau → ℕ) (χ : HChar D.host.E), IsValChar (cmPhi D) s κ (condF G.pl) ∅ χ →
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) →₀ ℕ, (∀ v, ExpAt χ v (a v)) ∧
      (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) ≤ levQ G.pl ^ 2 := by
  intro D _ T Lc sc G s κ χ hχ
  let 𝔣 : Ideal (𝓞 D.host.F) := condF G.pl
  let 𝔐 : Ideal (𝓞 D.host.E) := 𝔣.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  have hrank : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 :=
    (IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E).symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
  have hnorm𝔣 : Ideal.absNorm 𝔣 = levQ G.pl := by
    simp only [𝔣, condF, levQ, map_prod, map_pow]
  have hlev : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have hnorm𝔐 : Ideal.absNorm 𝔐 = levQ G.pl ^ 2 := by
    rw [Ideal.absNorm_algebraMap, hrank, hnorm𝔣]
  have h𝔐0 : 𝔐 ≠ ⊥ := fun h => by
    have h' := hnorm𝔐
    rw [h, Ideal.absNorm_bot] at h'
    exact (pow_pos hlev 2).ne' h'.symm
  let f : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun P => expIn (condF G.pl) (P.under (𝓞 D.host.F))
  have hdvd : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal ^ f P ∣ 𝔐 := fun P => by
    have h1 : (P.under (𝓞 D.host.F)).asIdeal ^ f P ∣ 𝔣 := pow_multiplicity_dvd _ _
    have h2 : P.asIdeal ∣ (P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
      Ideal.dvd_iff_le.2 Ideal.map_comap_le
    obtain ⟨c, hc⟩ := h1
    calc P.asIdeal ^ f P ∣ ((P.under (𝓞 D.host.F)).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))) ^ f P :=
          pow_dvd_pow_of_dvd h2 _
      _ ∣ 𝔐 := by
          refine ⟨c.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), ?_⟩
          show 𝔣.map _ = _
          rw [hc, Ideal.map_mul, Ideal.map_pow]
  have hfin : (Function.support f).Finite := by
    refine (Ideal.finite_factors h𝔐0).subset fun P hP => ?_
    exact (dvd_pow_self _ hP).trans (hdvd P)
  refine ⟨Finsupp.ofSupportFinite f hfin, fun P => ?_, ?_⟩
  · exact (hχ.2.2.2 (P.under (𝓞 D.host.F)) P rfl).2 (Finset.notMem_empty _)
  · set a := Finsupp.ofSupportFinite f hfin
    have hJ : (a.prod fun P k => P.asIdeal ^ k) ∣ 𝔐 := by
      refine Finset.prod_dvd_of_coprime (fun P _ Q _ hPQ => ?_) fun P _ => ?_
      · exact (Ideal.isCoprime_of_isMaximal fun h => hPQ (HeightOneSpectrum.ext h)).pow
      · exact hdvd P
    have e : (a.prod fun v k => Ideal.absNorm v.asIdeal ^ k) = Ideal.absNorm (a.prod fun P k => P.asIdeal ^ k) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [e, ← hnorm𝔐]
    exact Nat.le_of_dvd (hnorm𝔐 ▸ pow_pos hlev 2) (map_dvd Ideal.absNorm hJ)

end GlobalTheory.FunObj.SqNum.CondExps
