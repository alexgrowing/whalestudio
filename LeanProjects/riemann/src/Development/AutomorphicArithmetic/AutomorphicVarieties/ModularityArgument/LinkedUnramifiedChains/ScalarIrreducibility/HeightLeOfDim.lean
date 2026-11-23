import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem height_le_of_dim {R : Type} [CommRing R] [IsLocalRing R] (Q : Ideal R) [hQ : Q.IsPrime]
    (h1 : ringKrullDim (R ⧸ Q) = 1) (N : ℕ)
    (h : ∀ P : Ideal R, P.IsPrime → P ≤ Q → ringKrullDim (R ⧸ P) ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) :
    Q.height ≤ (N : ℕ∞) := by
  have e : Q.height = Order.height (⟨Q, hQ⟩ : PrimeSpectrum R) :=
    PrimeSpectrum.height_eq_orderHeight (⟨Q, hQ⟩ : PrimeSpectrum R)
  rw [e, Order.height_le_iff]
  intro p hp
  have hQm : Q < maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ.ne_top) ?_
    intro hEq
    haveI : Q.IsMaximal := hEq ▸ IsLocalRing.maximalIdeal.isMaximal R
    letI := Ideal.Quotient.field Q
    rw [ringKrullDim_eq_zero_of_field] at h1
    exact absurd h1 (by decide)
  have hlt : p.last < (⟨maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) :=
    lt_of_le_of_lt hp hQm
  let s : LTSeries (PrimeSpectrum R) := p.snoc _ hlt
  set P := p.head.asIdeal with hPdef
  have hPp : P.IsPrime := p.head.isPrime
  have hPQ : P ≤ Q := (LTSeries.monotone p (Fin.zero_le (Fin.last _))).trans hp
  have hmem : ∀ i, s i ∈ PrimeSpectrum.zeroLocus (P : Set R) := by
    intro i
    have h0 := LTSeries.monotone s (Fin.zero_le i)
    rw [show s 0 = p.head from RelSeries.head_snoc _ _ _] at h0
    rw [PrimeSpectrum.mem_zeroLocus]
    exact fun a ha => h0 ha
  let t : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
    ⟨s.length, fun i => ⟨s i, hmem i⟩, fun i => s.step i⟩
  have ht : ((s.length : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
    rw [ringKrullDim_quotient]
    exact Order.le_krullDim_iff.2 ⟨t, rfl⟩
  have hb := ht.trans (h P hPp hPQ)
  have hsl : s.length = p.length + 1 := RelSeries.snoc_length _ _ _
  rw [hsl] at hb
  have hb' : p.length + 1 ≤ N + 1 := by exact_mod_cast hb
  exact_mod_cast (by omega : p.length ≤ N)

theorem UpperTheory.V.J.htUp :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (M : Ideal S.B), AllGood S M → (∀ Z : Ideal S.B, Z.IsPrime → M ≤ Z → ringKrullDim (S.B ⧸ Z) ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞)) →
          ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q → S.u.TI q → Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) := by
  intro l _ c _ F C₀ n hF hn S M hM hZ q x L Q hO hT
  obtain ⟨hQp, him, -, hdim⟩ := hO
  refine height_le_of_dim Q hdim (n * F.d + 1) ?_
  intro P hP hPQ
  have hPq : L.im P ≤ q := him ▸ Ideal.comap_mono hPQ
  have hTP : S.u.TI (L.im P) :=
    ⟨⟨fun h => hT.1.1 (h.trans hPq), fun h => hT.1.2 (h.trans hPq)⟩,
      fun h3 h => hT.2 h3 (h.trans hPq)⟩
  have hprime : (L.im P).IsPrime := Ideal.comap_isPrime _ _
  have htd : S.td (L.im P) ≤ ((1 : ℕ) : Cardinal) := by
    rw [Nat.cast_one]
    exact Fr.fibre hF hn S _ hprime hTP.1
  have h1 := (Fr.loc_dim hF hn S x L).1 P hP 1 htd
  have hπ : (L.π P).IsPrime := Ideal.comap_isPrime _ _
  have h2 := hZ (L.π P) hπ (hM _ hprime hTP)
  calc ringKrullDim (L.R ⧸ P) ≤ ringKrullDim (S.B ⧸ L.π P) + ((1 : ℕ) : WithBot ℕ∞) := h1
    _ ≤ ((1 + n * F.d : ℕ) : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞) := by gcongr
    _ = ((n * F.d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← Nat.cast_add]
      congr 1
      omega
