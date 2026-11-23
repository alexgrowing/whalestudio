import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ShapeDegreeParity
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TeichmullerFactorisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TauPlBijective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.InertCompare

open Formalism.FrobeniusOrbits GlobalTheory.Proof.IdempotentLatticeSequence

theorem ne_of_inert (D : D7) (l : ℕ) (h : IsResidueClassZero D l ∨ IsSg D l) : l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d := by
  rcases h with h | h
  · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩
  · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩

theorem primeOf_liesOver {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).LiesOver (Ideal.span {(l : ℤ)}) := by
  have := primeOf_isPrime ρ
  refine ⟨(span_prime_isMaximal l Fact.out).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeOf ρ

theorem galE_frob_snd (D : D7) (l : ℕ) [Fact l.Prime] (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    (D.host.galE σ).2 = D.R.iota (G.hP D l) := by
  have hc : l.Coprime D.host.condN :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D l := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.toHostAx.frob_iff l hc P σ).1 hσ
  have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx l _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
  unfold Formalism.MainNotions.G.hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
  exact congrArg Prod.snd (e1.trans e2.symm)

theorem plGG_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) :
    plGG D (posPl D l z 1) = plGG D z * D.host.galE σ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  have hC := factClassFrob D.R D.host l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P σ hσ
  have hH := galE_frob_snd D l h2 hq hd P σ hσ
  have hpl : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
    rintro ⟨b, t⟩
    cases b <;> rfl
  rw [hpl, hpl]
  refine Prod.ext ?_ ?_
  · rcases h with h | h
    · have h1 := hC.2.2.1 h
      have hs : ¬ IsSg D l := fun hs => by
        have := h.symm.trans hs
        cases this
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, partner, hs]
      cases z.1 <;> simp
    · have h1 := hC.2.1.1 h
      have hp : (partner D l z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, hp]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
    rw [Formalism.HC.Frame.iota_add]

theorem exists_frob_step (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    ∃ φ : D.host.E ≃ₐ[ℚ] D.host.E, IsArithFrobAt ℤ φ P ∧ ∀ z : Bool × HH D,
      plGG D (posPl D l z 1) = plGG D z * D.host.galE φ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  obtain ⟨φ, hφ⟩ := (D.host.der.frob l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P).1
  exact ⟨φ, hφ, plGG_posPl_one D l h P φ hφ⟩

theorem embT_tauPl (D : D7) (z : Bool × HH D) : embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold embT tauPl
  rw [Equiv.apply_symm_apply]

theorem emb_mul_galE {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) :
    H.emb (g * H.galE σ) x = H.emb g (σ x) := by
  have he : H.sigmaOf (g * H.galE σ) = H.sigmaOf g * σ := by
    unfold Host.sigmaOf
    rw [map_mul, MulEquiv.symm_apply_apply]
  change H.φ₀ (H.sigmaOf (g * H.galE σ) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem rhoH_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) (x : D.host.E) :
    rhoH D lam (tauPl D (posPl D l z 1)) x = rhoH D lam (tauPl D z) (σ (D.host.conj x)) := by
  rw [rhoH_apply, rhoH_apply, embT_tauPl, embT_tauPl, plGG_posPl_one D l h P σ hσ z,
    ← D.host.galE_conjE, emb_mul_galE, emb_mul_galE]

theorem samePrime_step : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), (IsResidueClassZero D l ∨ IsSg D l) →
    ∀ z : Bool × HH D, SamePrime (rhoH D lam (tauPl D (posPl D l z 1))) (rhoC D lam (tauPl D z)) := by
  intro D l _ lam h z a
  have := primeOf_isPrime (rhoH D lam (tauPl D z))
  have := primeOf_liesOver (rhoH D lam (tauPl D z))
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D l h (primeOf (rhoH D lam (tauPl D z)))
  rw [rhoH_posPl_one D l lam h _ φ hφ]
  have hc := AlgHom.IsArithFrobAt.comap_eq hφ
  have := Ideal.ext_iff.1 hc (D.host.conj • a)
  exact this

end GlobalTheory.InertCompare
