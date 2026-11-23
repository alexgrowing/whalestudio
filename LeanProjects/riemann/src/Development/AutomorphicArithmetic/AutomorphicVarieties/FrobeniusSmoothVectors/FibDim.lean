import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankFrameSpaceEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_le_of_primes {R : Type} [CommRing R] (I : Ideal R) (d : WithBot ℕ∞)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ringKrullDim (R ⧸ P) ≤ d) : ringKrullDim (R ⧸ I) ≤ d := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  let q : PrimeSpectrum R := (s.head).1
  have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp s.head.2
  have hP := h q.asIdeal q.isPrime hIq
  rw [ringKrullDim_quotient] at hP
  have hmem : ∀ i, (s i).1 ∈ PrimeSpectrum.zeroLocus (R := R) q.asIdeal := by
    intro i
    have hle : s.head ≤ s i := s.monotone (Fin.zero_le i)
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hle
  let s' : LTSeries (PrimeSpectrum.zeroLocus (R := R) q.asIdeal) :=
    { length := s.length
      toFun := fun i => ⟨(s i).1, hmem i⟩
      step := fun i => s.step i }
  exact le_trans (Order.LTSeries.length_le_krullDim s') hP

private theorem trdeg_le_of_dim {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (η : Ideal A) [η.IsPrime] (hm : (η.comap (algebraMap B A)).IsMaximal) (t : ℕ)
    (h : ringKrullDim (A ⧸ η) ≤ t) : Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) ≤ t := by
  haveI := hm
  letI : Field (B ⧸ η.comap (algebraMap B A)) := Ideal.Quotient.field _
  haveI : IsDomain (A ⧸ η) := Ideal.Quotient.isDomain η
  haveI : Algebra.FiniteType B (A ⧸ η) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B η) (Ideal.Quotient.mkₐ_surjective B η)
  haveI : Algebra.FiniteType (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  obtain ⟨d, hd1, hd2⟩ :=
    GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (B ⧸ η.comap (algebraMap B A)) (A ⧸ η)
  rw [hd2]
  rw [hd1] at h
  have hdt : d ≤ t := by exact_mod_cast h
  exact_mod_cast hdt

private theorem exists_field_injective_ringHom_of_isDomain (D : Type) [CommRing D] [IsDomain D] :
    ∃ (K : Type) (_ : Field K) (j : D →+* K), Function.Injective j := by
  set_option synthInstance.maxHeartbeats 400000 in
  exact ⟨FractionRing D, inferInstance, algebraMap D _, IsFractionRing.injective D (FractionRing D)⟩

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Fr.fib_dim :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ S.mB.map L.b) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hx
  obtain ⟨hCO, hmB⟩ := co_B hF hn S
  haveI := hCO
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  haveI := hft
  have hl42 := finrank_frameSpace_eq hF hn S
  apply dim_le_of_primes
  intro P hP hbP
  have hπ : S.mB ≤ L.π P := by
    show S.mB ≤ Ideal.comap (S.inc : S.B →+* S.A) (Ideal.comap (L.ι : S.A →+* L.R) P)
    rw [Ideal.comap_comap]
    exact Ideal.map_le_iff_le_comap.mp hbP
  haveI hηp : (L.im P).IsPrime := Ideal.comap_isPrime _ P
  have hπprime : (L.π P).IsPrime := by
    show (Ideal.comap (S.inc : S.B →+* S.A) (L.im P)).IsPrime
    exact Ideal.comap_isPrime _ _
  have hmBmax : S.mB.IsMaximal := by
    rw [← hmB]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hπeq : S.mB = L.π P := hmBmax.eq_of_le hπprime.ne_top hπ
  have hπmax : (L.π P).IsMaximal := hπeq ▸ hmBmax
  have hx0 : S.x0 ≤ L.im P := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr hπ
  have hηx : L.im P ≤ x := by
    have h1 : Ideal.comap (L.ι : S.A →+* L.R) P ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) :=
      Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.ne_top)
    exact h1.trans L.lies.le
  haveI : IsDomain (S.A ⧸ L.im P) := Ideal.Quotient.isDomain _
  obtain ⟨K, hK, j, hj⟩ := exists_field_injective_ringHom_of_isDomain (S.A ⧸ L.im P)
  have hker : RingHom.ker (j.comp (Ideal.Quotient.mk (L.im P))) = L.im P := by
    rw [RingHom.ker_comp_of_injective _ hj, Ideal.mk_ker]
  have htypes := (types hF hn S K (j.comp (Ideal.Quotient.mk (L.im P)))).2
  rw [hker] at htypes
  have hM : S.u.triM ≤ L.im P := by
    rcases htypes hπ with h | h
    · exact absurd (le_trans h hηx) hx
    · exact h
  have hdimA : ringKrullDim (S.A ⧸ L.im P) ≤ ((2 * C₀ : ℕ) : WithBot ℕ∞) := by
    have hle : S.x0 ⊔ S.u.triM ≤ L.im P := sup_le hx0 hM
    exact le_trans (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)) hl42
  have htd : S.td (L.im P) ≤ ((2 * C₀ : ℕ) : Cardinal) := by
    unfold Space.td
    exact trdeg_le_of_dim (L.im P) hπmax (2 * C₀) hdimA
  have hd := (loc_dim hF hn S x L).1 P hP (2 * C₀) htd
  have hB0 : ringKrullDim (S.B ⧸ L.π P) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hπmax)
  rw [hB0, zero_add] at hd
  exact hd
