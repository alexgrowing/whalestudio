import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeIdealIffSumStatement

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Lat

private theorem exists_sub_iota_mem_of_sub_involution_mem {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (b : B) (hb : b ∈ Lat.sub f ξ l M) : ∃ w : W, f w - b ∈ Lat.IB f ξ := by
  have hη : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    rw [Lat.η, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hle : Lat.sub f ξ l M ≤
      (((Ideal.Quotient.mk (Lat.IB f ξ)).comp f).range).comap (Ideal.Quotient.mk (Lat.IB f ξ)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨w, rfl⟩)
    · cases i with
      | zero => exact Subring.mem_comap.2 (RingHom.mem_range.2 ⟨1, by simp [Lat.dpE]⟩)
      | succ i =>
        have hd : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
          rw [Lat.dpE, Algebra.smul_def, pow_succ']
          exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hη)
        refine Subring.mem_comap.2 (RingHom.mem_range.2 ⟨0, ?_⟩)
        rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
        exact hd
  obtain ⟨w, hw⟩ := RingHom.mem_range.1 (Subring.mem_comap.1 (hle hb))
  exact ⟨w, Ideal.Quotient.eq.1 hw⟩

theorem pow_mem_span_sup_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∉ Lat.I f ξ l M →
      ∃ n : ℕ, (l : Lat.A f ξ l M) ^ n ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m hH x hx
  have hxmem : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (show ↥(Lat.sub f ξ l M) from x).2
  obtain ⟨w, hw⟩ := exists_sub_iota_mem_of_sub_involution_mem f ξ l M _ hxmem
  have hxw : Lat.ofW f ξ l M w - x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M w - x) ∈ Lat.IB f ξ
    rw [map_sub, Lat.ι_ofW]
    exact hw
  have hξI : Lat.ofW f ξ l M ξ ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (Lat.ofW f ξ l M ξ) ∈ Lat.IB f ξ
    rw [Lat.ι_ofW]
    exact Ideal.mem_span_singleton_self _
  have hwnot : ¬ ξ ∣ w := by
    rintro ⟨v, rfl⟩
    apply hx
    have h1 : Lat.ofW f ξ l M (ξ * v) ∈ Lat.I f ξ l M := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hξI
    have h2 := (Lat.I f ξ l M).sub_mem h1 hxw
    simpa using h2
  have hq : Ideal.Quotient.mk (Ideal.span {ξ}) w ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hwnot
  obtain ⟨n, c, hc⟩ := hH.dv _ hq
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : (l : W) ^ n - w * u ∈ Ideal.span {ξ} := by
    rw [← Ideal.Quotient.eq]
    simpa using hc
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨n, ?_⟩
  have e : (l : Lat.A f ξ l M) ^ n = Lat.ofW f ξ l M ((l : W) ^ n) := by
    rw [map_pow, map_natCast]
  rw [e, show (l : W) ^ n = w * u + v * ξ by rw [hv]; ring, map_add, map_mul, map_mul]
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hξI))
  have e2 : Lat.ofW f ξ l M w * Lat.ofW f ξ l M u =
      x * Lat.ofW f ξ l M u + (Lat.ofW f ξ l M w - x) * Lat.ofW f ξ l M u := by ring
  rw [e2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ hxw))

end GlobalTheory.CompanionTheory.Lat
