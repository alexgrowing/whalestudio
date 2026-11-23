import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IterCancel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Bridge

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_of_univ {R : Type} [CommRing R] (I : Ideal R)
    (h : PrimeSpectrum.zeroLocus (I : Set R) = Set.univ) :
    ringKrullDim (R ⧸ I) = ringKrullDim R := by
  rw [ringKrullDim_quotient, h]
  exact Order.krullDim_eq_of_orderIso OrderIso.Set.univ

private theorem connOn_irr {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (j : WithBot ℕ∞) (hj : j ≤ ringKrullDim R) : ConnOn (⊥ : Ideal R) j := by
  intro I _ hI
  rw [PrimeSpectrum.zeroLocus_bot, ← Set.compl_eq_univ_diff]
  have hne : (PrimeSpectrum.zeroLocus (I : Set R))ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    rw [dim_of_univ I h] at hI
    exact absurd hj (not_le.mpr hI)
  have ho : IsOpen (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hp : IsPreirreducible (PrimeSpectrum.zeroLocus (I : Set R))ᶜ :=
    (PreirreducibleSpace.isPreirreducible_univ).open_subset ho (Set.subset_univ _)
  exact ⟨hne, hp.isPreconnected⟩

private theorem dim_min {R : Type} [CommRing R] [IrreducibleSpace (PrimeSpectrum R)]
    (p : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  have hn : (nilradical R).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have hpp : p.IsPrime := hp.1.1
  have hle : p ≤ nilradical R := hp.2 ⟨hn, bot_le⟩ (nilradical_le_prime p)
  apply dim_of_univ
  refine Set.eq_univ_of_forall fun q => ?_
  rw [PrimeSpectrum.mem_zeroLocus]
  exact hle.trans (nilradical_le_prime q.asIdeal)

private theorem connOn_rad {R : Type} [CommRing R] (a b : Ideal R) (k : WithBot ℕ∞)
    (hab : a.radical = b.radical) (h : ConnOn a k) : ConnOn b k := by
  intro I hbI hI
  have hz : PrimeSpectrum.zeroLocus (a : Set R) = PrimeSpectrum.zeroLocus (b : Set R) := by
    rw [← PrimeSpectrum.zeroLocus_radical a, hab, PrimeSpectrum.zeroLocus_radical]
  have haI : a ≤ I.radical :=
    Ideal.le_radical.trans (hab.le.trans (Ideal.radical_mono hbI))
  have hd : ringKrullDim (R ⧸ I.radical) = ringKrullDim (R ⧸ I) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  have := h I.radical haI (hd ▸ hI)
  rwa [hz, PrimeSpectrum.zeroLocus_radical] at this

theorem UpperTheory.V.AlgebraTools.Conn.main :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IrreducibleSpace (PrimeSpectrum R)], CohenType R →
      ∀ (a : Ideal R) (h k : ℕ), a ≠ ⊤ → ReciprocityTheory.CA.AraLE a h → ((k + h + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R →
        ReciprocityTheory.CA.ConnInDim (R ⧸ a) k := by
  intro R _ _ _ _ hC a h k ha ⟨s, hs, hrad⟩ hdim
  have h1 : ((k + s.card + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card + 1 ≤ k + h + 1)) hdim
  have h0 : ((k + s.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R :=
    le_trans (by exact_mod_cast (by omega : k + s.card ≤ k + s.card + 1)) h1
  have hm : ∀ f ∈ s, f ∈ maximalIdeal R := by
    intro f hf
    have h2 : f ∈ a.radical := hrad ▸ Ideal.le_radical (Ideal.subset_span hf)
    exact le_maximalIdeal (fun ht => ha (Ideal.radical_eq_top.mp ht)) h2
  have key := UpperTheory.V.AlgebraTools.Conn.iter hC ⊥ s k hm (connOn_irr _ h0)
    (fun p hp => (dim_min p hp).symm ▸ h1)
  rw [bot_sup_eq] at key
  exact (UpperTheory.V.AlgebraTools.Conn.bridge a k).mp (connOn_rad _ _ _ hrad key)
