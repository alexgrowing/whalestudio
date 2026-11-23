import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.WithBotAddOneLeAddTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimLeOfForall

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.step_krull {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J : Ideal R) (y : R) (hy : y ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ (J ⊔ Ideal.span {y})) + 1 := by
  have h := Module.supportDim_le_supportDim_quotSMulTop_succ
    (R := R) (M := R ⧸ J) (x := y) hy
  rw [Module.supportDim_quotient_eq_ringKrullDim] at h
  refine h.trans (le_of_eq ?_)
  rw [ringKrullDim_quotient, Module.supportDim, Module.support_quotSMulTop,
    Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_span]

private theorem UpperTheory.V.AlgebraTools.Conn.step_mono {R : Type} [CommRing R] (J I : Ideal R)
    (h : PrimeSpectrum.zeroLocus (J : Set R) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  exact Order.krullDim_le_of_strictMono (Set.inclusion h) (fun _ _ hab => hab)

private theorem UpperTheory.V.AlgebraTools.Conn.step_arith (d e : WithBot ℕ∞) (k : ℕ) (h1 : d ≤ e) (h2 : e < k)
    (h3 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ d + 1) : False := by
  have h4 : d < k := lt_of_le_of_lt h1 h2
  induction d using WithBot.recBotCoe with
  | bot => simp at h3
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h4 (not_lt.2 (WithBot.coe_le_coe.2 le_top))
    | coe d =>
      have h5 : d < k := by exact_mod_cast h4
      have h6 : k + 1 ≤ d + 1 := by exact_mod_cast h3
      omega

theorem UpperTheory.V.AlgebraTools.Conn.step :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R], CohenType R → ∀ (a : Ideal R) (f : R) (k : ℕ),
      f ∈ maximalIdeal R → ConnOn a ((k + 1 : ℕ) : WithBot ℕ∞) →
      (∀ p ∈ a.minimalPrimes, (k : WithBot ℕ∞) + 2 ≤ ringKrullDim (R ⧸ p)) → ConnOn (a ⊔ Ideal.span {f}) k := by
  intro R _ _ _ hC a f k hf hconn hdim I hI hIk
  set X : Ideal R → Set (PrimeSpectrum R) := fun b =>
    PrimeSpectrum.zeroLocus ((b ⊔ Ideal.span {f} : Ideal R) : Set R) \ PrimeSpectrum.zeroLocus (I : Set R)
    with hX
  have hmem : ∀ (b : Ideal R) (z : PrimeSpectrum R),
      z ∈ X b ↔ (b ≤ z.asIdeal ∧ Ideal.span {f} ≤ z.asIdeal) ∧ ¬ I ≤ z.asIdeal := by
    intro b z
    simp only [hX, Set.mem_diff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff]
  have hXc : ∀ p ∈ a.minimalPrimes, IsConnected (X p) := by
    intro p hp
    have h := hyper hC p f k hp.1.1 hf (hdim p hp) ((p ⊔ Ideal.span {f}) ⊔ I) le_sup_left
      (lt_of_le_of_lt (step_mono _ _ (PrimeSpectrum.zeroLocus_anti_mono_ideal le_sup_right)) hIk)
    convert h using 1
    ext z
    rw [hmem]
    simp only [Set.mem_diff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff]
    tauto
  have hsub : ∀ p ∈ a.minimalPrimes, X p ⊆ X a := by
    intro p hp z hz
    rw [hmem] at hz ⊢
    exact ⟨⟨hp.1.2.trans hz.1.1, hz.1.2⟩, hz.2⟩
  have hmeet : ∀ p q : Ideal R, ReciprocityTheory.CA.Linked R ((k + 1 : ℕ) : WithBot ℕ∞) p q →
      (X p ∩ X q).Nonempty := by
    intro p q hl
    by_contra hne
    have hl' : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ (p ⊔ q)) := hl
    refine step_arith _ _ k (step_mono ((p ⊔ q) ⊔ Ideal.span {f}) I ?_) hIk
      (hl'.trans (step_krull _ f hf))
    intro z hz
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, sup_le_iff] at hz ⊢
    by_contra hzI
    exact hne ⟨z, (hmem p z).2 ⟨⟨hz.1.1, hz.2⟩, hzI⟩, (hmem q z).2 ⟨⟨hz.1.2, hz.2⟩, hzI⟩⟩
  have ha : a ≠ ⊤ := by
    rintro rfl
    have h := hconn ⊤ le_rfl (by
      rw [ringKrullDim_eq_bot_of_subsingleton]
      exact WithBot.bot_lt_coe _)
    simpa using h.nonempty
  obtain ⟨p₀, hp₀, -⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := maximalIdeal R)
    (le_maximalIdeal ha)
  have key : ∀ q, Relation.ReflTransGen (fun x y : Ideal R => x ∈ a.minimalPrimes ∧
      y ∈ a.minimalPrimes ∧ ReciprocityTheory.CA.Linked R ((k + 1 : ℕ) : WithBot ℕ∞) x y) p₀ q →
      ∃ t, t ⊆ X a ∧ X p₀ ⊆ t ∧ X q ⊆ t ∧ IsConnected t := by
    intro q hq
    induction hq with
    | refl => exact ⟨X p₀, hsub _ hp₀, le_rfl, le_rfl, hXc _ hp₀⟩
    | @tail b c _ hbc ih =>
      obtain ⟨t, h1, h2, h3, h4⟩ := ih
      refine ⟨t ∪ X c, Set.union_subset h1 (hsub _ hbc.2.1), h2.trans Set.subset_union_left,
        Set.subset_union_right, h4.union ?_ (hXc _ hbc.2.1)⟩
      exact (hmeet b c hbc.2.2).mono (Set.inter_subset_inter_left _ h3)
  obtain ⟨x, hx⟩ := (hXc _ hp₀).nonempty
  change IsConnected (X a)
  refine ⟨⟨x, hsub _ hp₀ hx⟩, isPreconnected_of_forall x fun y hy => ?_⟩
  have hy' := (hmem a y).1 hy
  obtain ⟨q, hq, hqy⟩ := Ideal.exists_minimalPrimes_le (I := a) (J := y.asIdeal) hy'.1.1
  obtain ⟨t, h1, h2, h3, h4⟩ := key q (chain a _ hconn p₀ hp₀ q hq)
  exact ⟨t, h1, h2 hx, h3 ((hmem q y).2 ⟨⟨hqy, hy'.1.2⟩, hy'.2⟩), h4.isPreconnected⟩
