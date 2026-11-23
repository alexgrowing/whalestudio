import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedFrobeniusEigenvalueSizes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem IsPurePair.absSpace_neg_eq_bot_iff {V : Type*} [AddCommGroup V] [Module Complex V]
    {q : Real} {f N : Module.End Complex V} (hp : IsPurePair q f N) (n : Nat) :
    absSpace f (q ^ (-(n : Real) / 2)) = ⊥ ↔ absSpace f (q ^ ((n : Real) / 2)) = ⊥ := by
  constructor
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, hu, rfl⟩ := (hp.2 n).2.2 hv
    have : u = 0 := by
      have : u ∈ (⊥ : Submodule Complex V) := h0 ▸ hu
      simpa using this
    simp [this]
  · intro h0
    rw [eq_bot_iff]
    intro v hv
    have h1 : (N ^ n) v ∈ absSpace f (q ^ ((n : Real) / 2)) := (hp.2 n).1 hv
    rw [h0, Submodule.mem_bot] at h1
    have := (hp.2 n).2.1 hv (zero_mem _) (by simpa using h1)
    simp [this]

theorem exists_top_weight :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), a.Tempered →
      Nontrivial V → ∃ m : ℕ, wtSpace a (-(m : ℤ)) ≠ ⊥ ∧ ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥ := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a ha hV
  have hp := ha (frob h) deg_frob
  set q : ℝ := ((normV w : ℕ) : ℝ)
  have hw : ∀ k : ℤ, wtSpace a k = absSpace (a.ρ (frob h)) (q ^ ((k : ℝ) / 2)) := fun _ => rfl
  have hneg : ∀ n : ℕ, wtSpace a (-(n : ℤ)) = ⊥ ↔ wtSpace a (n : ℤ) = ⊥ := by
    intro n
    rw [hw, hw]
    push_cast
    exact IsPurePair.absSpace_neg_eq_bot_iff hp n
  set d := Module.finrank ℂ V
  have hbig : ∀ k : ℤ, (d : ℤ) ≤ |k| → wtSpace a k = ⊥ := fun k hk =>
    hp.absSpace_eq_bot_of_finrank_le a.nilpotent hk

  have hex : ∃ n : ℕ, wtSpace a (n : ℤ) ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    have hall : ∀ i : ℤ, wtSpace a i = ⊥ := by
      intro i
      rcases le_total 0 i with hi | hi
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        exact hc n
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
        exact (hneg n).2 (hc n)
    have htop := hp.1
    simp only [← hw, hall, iSup_bot] at htop
    exact bot_ne_top htop
  classical
  let P : ℕ → Prop := fun n => wtSpace a (n : ℤ) ≠ ⊥
  obtain ⟨n₀, hn₀⟩ := hex
  have hn₀d : n₀ ≤ d := by
    by_contra hc
    exact hn₀ (hbig _ (by rw [abs_of_nonneg (by positivity)]; omega))
  refine ⟨Nat.findGreatest P d, ?_, ?_⟩
  · rw [Ne, hneg]
    exact Nat.findGreatest_spec (P := P) hn₀d hn₀
  · intro k hk
    have hk0 : 0 ≤ k := le_trans (by positivity) hk.le
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hn : Nat.findGreatest P d < n := by exact_mod_cast hk
    by_cases hnd : n ≤ d
    · have := Nat.findGreatest_is_greatest (P := P) hn hnd
      simpa [P] using this
    · exact hbig _ (by rw [abs_of_nonneg (by positivity)]; omega)

end GlobalTheory.WeilDeligne.PrimDecomp
