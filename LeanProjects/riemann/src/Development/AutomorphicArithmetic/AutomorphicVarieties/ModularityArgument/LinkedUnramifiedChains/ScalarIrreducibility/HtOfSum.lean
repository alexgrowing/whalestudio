import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatHt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CmOfRegularLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatAss
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem ht_of_sum {h : ℕ∞} {N : ℕ} {D : WithBot ℕ∞} (hD : D = 1)
    (e : (h : WithBot ℕ∞) + D = (N + 1 : ℕ)) : h = N := by
  subst hD
  have e2 : ((h + 1 : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast]
    exact e
  have e3 : h + 1 = ((N + 1 : ℕ) : ℕ∞) := WithBot.coe_injective e2
  induction h using ENat.recTopCoe with
  | top =>
    rw [top_add] at e3
    exact absurd e3.symm (ENat.coe_ne_top _)
  | coe k =>
    norm_cast at e3 ⊢
    omega

private theorem le_of_add {a : ℕ∞} {b c : ℕ} (h : ((c + b : ℕ) : ℕ∞) ≤ a + b) : (c : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    norm_cast at h ⊢
    omega

theorem UpperTheory.V.J.htLow :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q →
          ((n * F.d + 1 : ℕ) : ℕ∞) ≤ q.height ∧ (Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) → ∀ P ∈ associatedPrimes S.A S.A, P ≤ q → P ∈ minimalPrimes S.A) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO
  obtain ⟨hQ, him, hmin, hdim⟩ := hO
  obtain ⟨N, N', p, f, hN, hp, hker⟩ := Fr.pres hF hn S x L
  obtain ⟨hfl, -, -⟩ := Fr.loc_flat hF hn S x L
  have hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  have hR : IsNoetherianRing L.R := inferInstance
  obtain ⟨h1, h2⟩ := htPres L.O' N N' L.R p f hp hker Q hQ
  have hc : (Ideal.comap p Q).height = N := ht_of_sum hdim h1
  have hfh : Q.height = q.height := flatHt S.A L.R L.ι hfl q Q hQ him hmin
  have hlow : ((n * F.d + 1 : ℕ) : ℕ∞) ≤ Q.height := by
    apply le_of_add (b := N')
    rw [Nat.add_comm, ← hN, ← hc]
    exact h2
  refine ⟨hfh ▸ hlow, fun hle P hP hPq => ?_⟩
  have hu : Q.height + N' ≤ (Ideal.comap p Q).height := by
    rw [hc, hN, Nat.cast_add, add_comm (N' : ℕ∞)]
    exact add_le_add hle le_rfl
  refine flatAss S.A L.R L.ι hfl Q hQ (unmix L.O' N N' L.R p f hp hker Q hQ hu) P hP ?_
  change P ≤ L.im Q
  rw [him]
  exact hPq
