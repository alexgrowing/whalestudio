import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.HtPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne

set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem dim_arith {h : ℕ∞} {D E : WithBot ℕ∞} {N N' a : ℕ}
    (h1 : (h : WithBot ℕ∞) + D = ((N + 1 : ℕ) : WithBot ℕ∞)) (h2 : h ≤ (N' : ℕ∞)) (h3 : N = N' + (a + 1))
    (h4 : D ≤ E + ((1 : ℕ) : WithBot ℕ∞)) : ((1 + a : ℕ) : WithBot ℕ∞) ≤ E := by
  induction E using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add, le_bot_iff] at h4
    rw [h4, WithBot.add_bot] at h1
    exact absurd h1.symm (WithBot.natCast_ne_bot _)
  | coe E =>
    induction D using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.add_bot] at h1
      exact absurd h1.symm (WithBot.natCast_ne_bot _)
    | coe D =>
      have h1' : h + D = ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
      have h4' : D ≤ E + ((1 : ℕ) : ℕ∞) := by exact_mod_cast h4
      have : ((1 + a : ℕ) : ℕ∞) ≤ E := by
        induction E using ENat.recTopCoe with
        | top => exact le_top
        | coe e =>
          induction D using ENat.recTopCoe with
          | top => simp at h4'
          | coe d =>
            induction h using ENat.recTopCoe with
            | top => simp at h2
            | coe k =>
              have a1 : k + d = N + 1 := by exact_mod_cast h1'
              have a2 : k ≤ N' := by exact_mod_cast h2
              have a4 : d ≤ e + 1 := by exact_mod_cast h4'
              have : 1 + a ≤ e := by omega
              exact_mod_cast this
      exact_mod_cast this

private theorem min_below {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (hf : f.Flat) (Q : Ideal R)
    (hQ : Q.IsPrime) (P : Ideal A) (hP : P ∈ minimalPrimes A) (h : P ≤ Q.comap f) :
    ∃ P' ∈ minimalPrimes R, P'.comap f = P := by
  letI := f.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : P.IsPrime := hP.1.1
  haveI : (Q.comap f).IsPrime := Ideal.IsPrime.comap f
  haveI : Q.LiesOver (Q.comap f) := ⟨rfl⟩
  obtain ⟨Q', -, hQ', hl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := Q.comap f) Q h
  obtain ⟨P', hP', hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Q') bot_le
  refine ⟨P', hP', ?_⟩
  have e : Q'.comap f = P := hl.over.symm
  have h1 : P'.comap f ≤ P := e ▸ Ideal.comap_mono hle
  haveI : P'.IsPrime := hP'.1.1
  exact le_antisymm h1 (hP.2 ⟨Ideal.IsPrime.comap f, bot_le⟩ h1)

theorem UpperTheory.V.J.compDim :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → ∀ P ∈ minimalPrimes S.A, P ≤ q →
          ((1 + n * F.d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.B ⧸ S.π P) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO hTI P hP hPq
  obtain ⟨hQ, hQq, -, -⟩ := hO
  have hflat := (Fr.loc_flat hF hn S x L).1
  obtain ⟨P', hP', hc⟩ := min_below (L.ι : S.A →+* L.R) hflat Q hQ P hP (by
    have : Q.comap (L.ι : S.A →+* L.R) = q := hQq
    rw [this]; exact hPq)
  have hPp : P'.IsPrime := hP'.1.1
  have him : L.im P' = P := hc
  have hoff : S.u.OffTri P :=
    ⟨fun h => hTI.1.1 (h.trans hPq), fun h => hTI.1.2 (h.trans hPq)⟩
  have htd : S.td (L.im P') ≤ ((1 : ℕ) : Cardinal) := by
    rw [him, Nat.cast_one]
    exact Fr.fibre hF hn S P hP.1.1 hoff
  have hdim := (Fr.loc_dim hF hn S x L).1 P' hPp 1 htd
  have hπ : L.π P' = S.π P := by
    show S.π (L.im P') = _
    rw [him]
  rw [hπ] at hdim
  obtain ⟨N, N', p, f, hN, hs, hk⟩ := Fr.pres hF hn S x L
  obtain ⟨e1, e2⟩ := htPres L.O' N N' L.R (p : MvPowerSeries (Fin N) L.O' →+* L.R) f hs hk P' hPp
  have h0 : P'.height = 0 := Ideal.height_eq_zero_iff.mpr hP'
  rw [h0, zero_add] at e2
  exact dim_arith e1 e2 (by rw [hN]) hdim
