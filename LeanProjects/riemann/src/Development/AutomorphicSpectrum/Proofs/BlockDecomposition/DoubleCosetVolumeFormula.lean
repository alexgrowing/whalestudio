import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolveUnitriangular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAntitonePairingSum

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.KmVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_of_mem_ker {N m : ℕ} {A : GL (Fin N) 𝒪[k]}
    (hA : A ∈ (Matrix.GeneralLinearGroup.map (n := Fin N)
      (Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}))).ker) (i j : Fin N) :
    (A : Matrix (Fin N) (Fin N) 𝒪[k]) i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈
      Ideal.span {Zls.unif k ^ m} := by
  rw [MonoidHom.mem_ker] at hA
  have h := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => u.val i j) hA
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h
  rw [← Ideal.Quotient.eq]
  rw [h]
  by_cases e : i = j
  · subst e
    simp
  · simp [Matrix.one_apply_ne e]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) (B : Matrix (Fin N) (Fin N) 𝒪[k])
    (hB : ∀ i j, B i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ Ideal.span {Zls.unif k ^ m}) :
    ∃ b ∈ Zls.Km k N m, (b : Matrix (Fin N) (Fin N) k) = B.map (algebraMap 𝒪[k] k) := by
  set J : Ideal 𝒪[k] := Ideal.span {Zls.unif k ^ m} with hJ
  have hmap : B.map (Ideal.Quotient.mk J) = 1 := by
    ext i j
    have := Ideal.Quotient.eq.2 (hB i j)
    simp only [Matrix.map_apply]
    rw [this]
    by_cases e : i = j
    · subst e
      simp
    · simp [Matrix.one_apply_ne e]
  have hdet : Ideal.Quotient.mk J B.det = 1 := by
    have := RingHom.map_det (Ideal.Quotient.mk J) B
    rw [this]
    show (B.map (Ideal.Quotient.mk J)).det = 1
    rw [hmap, Matrix.det_one]
  have hmem : B.det - 1 ∈ J := by
    rw [← Ideal.Quotient.eq, hdet, map_one]
  have hJm : J ≤ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [hJ, Ideal.span_singleton_le_iff_mem]
    have : Zls.unif k ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [Zls.irreducible_unif.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_mem_of_mem _ this m (by omega)
  have hunit : IsUnit B.det := by
    by_contra hn
    have h1 : B.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h2 := hJm hmem
    have h3 : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 h2
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h3
  let G : GL (Fin N) 𝒪[k] := Matrix.GeneralLinearGroup.mk'' B hunit
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) G, ?_, ?_⟩
  · refine ⟨G, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    have h := congrFun (congrFun hmap i) j
    simpa [G, Matrix.GeneralLinearGroup.map_apply] using h
  · rfl

theorem conj_mem_Km {N m : ℕ} {p b : GL (Fin N) k} (hp : p ∈ KO k (Fin N)) (hb : b ∈ Zls.Km k N m) :
    p * b * p⁻¹ ∈ Zls.Km k N m := by
  obtain ⟨P, rfl⟩ := hp
  obtain ⟨A, hA, rfl⟩ := hb
  refine ⟨P * A * P⁻¹, ?_, by simp⟩
  exact (MonoidHom.normal_ker _).conj_mem A hA P

theorem diagPow_val (N : ℕ) (lam : Fin N → ℤ) :
    ((Zls.diagPow k N lam : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal (fun i => (algebraMap 𝒪[k] k (Zls.unif k)) ^ lam i) := by
  ext i j
  simp [Zls.diagPow, Zls.unifU, Matrix.diagonal_apply]

theorem exists_cover (N m : ℕ) (hm : 1 ≤ m) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    ∃ s : Finset (GL (Fin N) k),
      s.card ≤ Nat.card 𝓀[k] ^
        (∑ i : Fin N, ∑ j : Fin N, if i < j then (lam i - lam j).toNat else 0) ∧
      ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m, ∃ c ∈ s, ∃ b ∈ Zls.Km k N m,
        x * Zls.diagPow k N lam * y = c * b := by
  classical
  obtain ⟨s0, hcard, hs0⟩ := GlobalTheory.CompanionTheory.KmCover.double_coset_cover 𝒪[k] k N (Zls.unif k) m
    Zls.irreducible_unif hm lam hlam
  let f : Matrix (Fin N) (Fin N) k → GL (Fin N) k := fun M =>
    if h : ∃ c : GL (Fin N) k, c.val = M then h.choose else 1
  refine ⟨s0.image f, Finset.card_image_le.trans hcard, ?_⟩
  rintro x ⟨A1, hA1, rfl⟩ y ⟨A2, hA2, rfl⟩
  obtain ⟨M, hM, B, hB, e⟩ := hs0 A1.val A2.val (entries_of_mem_ker hA1) (entries_of_mem_ker hA2)
  obtain ⟨b, hb, hbv⟩ := exists_mem_Km hm B hB
  set X : GL (Fin N) k := Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A1 *
    Zls.diagPow k N lam * Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) A2 with hX
  have hXv : X.val = M * b.val := by
    rw [hbv, ← e, hX, Units.val_mul, Units.val_mul, diagPow_val]
    rfl
  have hex : ∃ c : GL (Fin N) k, c.val = M := by
    refine ⟨X * b⁻¹, ?_⟩
    rw [Units.val_mul, hXv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  refine ⟨f M, Finset.mem_image_of_mem f hM, b, hb, ?_⟩
  apply Units.ext
  have hf : (f M).val = M := by
    simp only [f, dif_pos hex]
    exact hex.choose_spec
  rw [Units.val_mul (f M) b, hf]
  exact hXv

theorem measure_translated_doubleCoset_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ m : ℕ, 1 ≤ m → ∀ (p1 p2 : GL (Fin N) k), p1 ∈ KO k (Fin N) → p2 ∈ KO k (Fin N) → ∀ g : Fin (N - 1) → ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2}) ≤ (Nat.card 𝓀[k] : ENNReal) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))) := by
  intro k _ _ _ _ N _ _ μ hμ m hm p1 p2 hp1 hp2 g
  classical
  obtain ⟨hanti, hgap⟩ := GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N g
  obtain ⟨s, hcard, hcov⟩ := exists_cover (k := k) N m hm (Zls.lamOf g) hanti
  rw [hgap] at hcard
  set U : Set (AdGL k N) :=
    (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k)) with hU
  let T : GL (Fin N) k → Set (AdGL k N) := fun c =>
    (fun q => (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * q) ⁻¹' U
  have hsub : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {h | ∃ x ∈ Zls.Km k N m,
      ∃ y ∈ Zls.Km k N m, h = p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2} ⊆ ⋃ c ∈ s, T c := by
    rintro _ ⟨h, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    obtain ⟨c, hc, b, hb, e⟩ := hcov x hx y hy
    refine Set.mem_biUnion hc ?_
    refine ⟨p2⁻¹ * b * p2, ?_, ?_⟩
    · have := conj_mem_Km (inv_mem hp2) hb
      simpa using this
    · have e2 : p1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p2 = p1 * (c * b) * p2 := by
        rw [← e]
        group
      rw [e2]
      show (QuotientGroup.mk (p2⁻¹ * b * p2) : AdGL k N) =
        (QuotientGroup.mk (p1 * c * p2) : AdGL k N)⁻¹ * QuotientGroup.mk (p1 * (c * b) * p2)
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      group
  calc μ _ ≤ μ (⋃ c ∈ s, T c) := measure_mono hsub
    _ ≤ ∑ c ∈ s, μ (T c) := measure_biUnion_finset_le _ _
    _ = ∑ _c ∈ s, μ U := Finset.sum_congr rfl fun c _ => measure_preimage_mul μ _ U
    _ = (s.card : ENNReal) * μ U := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard

end GlobalTheory.CompanionTheory.KmVolume
