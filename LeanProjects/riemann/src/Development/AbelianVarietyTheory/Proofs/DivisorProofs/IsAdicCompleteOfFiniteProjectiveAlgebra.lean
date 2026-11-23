import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.FinProjComplete

theorem smodEq_span_singleton_pow_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, x - y = a ^ n • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, hz⟩; exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩; exact ⟨z, Submodule.mem_top, hz.symm⟩

end GlobalTheory.FinProjComplete

namespace GlobalTheory.FinProjComplete

theorem isAdicComplete_of_finite_projective : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective O A
  have hfg' : ∀ x, f (g x) = x := fun x => LinearMap.congr_fun hfg x
  have key : ∀ (k : ℕ) (z : A), (p : A) ^ k • z = ((p : O) ^ k) • z := by
    intro k z
    rw [smul_eq_mul, Algebra.smul_def, map_pow, map_natCast]
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun s hs => ?_⟩ }
  · have hc : ∀ i, g x i = 0 := by
      intro i
      refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ (fun k => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ k x 0).1 (hx k)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [sub_zero, key, map_smul, Pi.smul_apply] using this
    have h0 : g x = 0 := funext hc
    rw [← hfg' x, h0, map_zero]
  · have hL : ∀ i, ∃ L : O, ∀ k,
        g (s k) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ k • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec' (I := Ideal.span {(p : O)}) _ (fun {m k} hmk => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ m _ _).1 (hs hmk)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [map_sub, key, map_smul, Pi.smul_apply, Pi.sub_apply] using this
    choose L hL using hL
    refine ⟨f L, fun k => ?_⟩
    have hz' : ∀ i, ∃ z : O, g (s k) i - L i = (p : O) ^ k • z :=
      fun i => (smodEq_span_singleton_pow_iff _ k _ _).1 (hL i k)
    choose z hz using hz'
    have h2 : g (s k) - L = (p : O) ^ k • z := funext fun i => by simpa using hz i
    rw [smodEq_span_singleton_pow_iff]
    refine ⟨f z, ?_⟩
    calc s k - f L = f (g (s k) - L) := by rw [map_sub, hfg']
      _ = (p : A) ^ k • f z := by rw [h2, map_smul, key]

end GlobalTheory.FinProjComplete
