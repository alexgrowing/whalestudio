import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormGal
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormLev
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SubOneMemOfPow
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DlogCmp
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresMono
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem map_dl_eq_dl_map_of_isUnit {R : Type} [CommRing R] (φ : R →+* R) (f : PowerSeries R) (hf : IsUnit f) :
    PowerSeries.map φ (dl f) = dl (PowerSeries.map φ f) := by
  have hd : PowerSeries.map φ (PowerSeries.derivative R f) = PowerSeries.derivative R (PowerSeries.map φ f) := by
    ext n
    simp [PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  obtain ⟨u, rfl⟩ := hf
  have hu : PowerSeries.map φ (u : PowerSeries R) = ((Units.map (PowerSeries.map φ).toMonoidHom u : (PowerSeries R)ˣ) : PowerSeries R) := rfl
  have hv : PowerSeries.map φ ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) = (((Units.map (PowerSeries.map φ).toMonoidHom u)⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := by
    rw [← map_inv]; rfl
  unfold dl dd
  rw [hu, Ring.inverse_unit, Ring.inverse_unit, map_mul, map_mul, hd, hv, ← hu]
  simp

private theorem pv_mem_ne_zero_inv_mem_of_bPres {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact (Nat.Prime l)] {c : Coef l}
    (β : Bas c) (A : ValuationSubring Ω) (ζ : ℕ → Ω) (Z : Sy Ω l) (m n : ℕ)
    (P : Fin β.d → Polynomial (R0 A)) (h : BPres β A ζ Z m n P) (i : Fin β.d) :
    pv (P i) (ζ m) ∈ A ∧ pv (P i) (ζ m) ≠ 0 ∧ (pv (P i) (ζ m))⁻¹ ∈ A := by
  unfold BPres GlobalTheory.Col.KumPres at h
  exact h.2.2.1 i

theorem UpperTheory.Kd.C7.pRepEx :
    UpperTheory.Kd.C7.SRepEx := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hm₀⟩ := hP
  have hch : ∀ m, ∃ P : Fin β.d → Polynomial (R0 A), m₀ ≤ m → BPres β A ζ Z m (m - c₀) P := by
    intro m
    by_cases h : m₀ ≤ m
    · obtain ⟨P, hP⟩ := hm₀ m h
      exact ⟨P, fun _ => hP⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose Pf hPf using hch
  have hCg : ∀ (n : ℕ) (a : Qbar l), Cg n a a := by
    intro n a
    unfold Cg
    simp
  have key : ∀ i : Fin β.d, ∃ f : PowerSeries Φ.R, IsUnit f ∧ ∀ m : ℕ, 1 ≤ m → max m₀ (c₀ + 1) ≤ m →
      ∀ N : ℕ, ∃ w, IsUnit w ∧ LC l m N ((PowerSeries.map (↑Φ.σ.symm ^ m)) f)
        (Φ.ser (Pf m i) * w ^ l ^ (m - (c₀ + 1))) := by
    intro i
    apply pExact Φ.R l Φ.σ Φ.fl Φ.unit (fun m => Φ.ser (Pf m i)) (c₀ + 1) (max m₀ (c₀ + 1))
    · intro m hm
      exact (pWD l hl Ω A hA j Φ ζ hζ m (by omega) (Pf m i)).2
        (pv_mem_ne_zero_inv_mem_of_bPres β A ζ Z m _ (Pf m) (hPf m (by omega)) i)
    · intro m hm1 hmM
      have h1 := hPf (m + 1) (by omega)
      have h0 := hPf m (by omega)
      have h1' : BPres β A ζ Z (m + 1) (m - c₀) (Pf (m + 1)) :=
        pPresMono l hl Ω A hA c β ζ hζ Z Z (m + 1) (m + 1 - c₀) (m - c₀) (Pf (m + 1)) (by omega)
          (fun s _ => hCg _ _) h1
      obtain ⟨Q, hQu, hQ⟩ := pNormGal l hl Ω A hA c β ζ hζ Z hZ m (m - c₀) (by omega) (by omega)
        (Pf (m + 1)) (Pf m) h1' h0 i
      refine ⟨Φ.ser Q, (pWD l hl Ω A hA j Φ ζ hζ m hm1 Q).2 hQu, ?_⟩
      have hN := pNormLev l hl Ω A hA j Φ ζ hζ m hm1 (Pf (m + 1) i) (Pf m i * Q ^ l ^ (m - c₀ - 1))
        (by rw [hQ]; simp [pv, Polynomial.eval₂_mul, Polynomial.eval₂_pow])
      have he : m - c₀ - 1 = m - (c₀ + 1) := by omega
      rw [hN, ← he]
      simp [Fr.ser, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.map_mul, Polynomial.map_pow]
  choose f hf using key
  refine ⟨fun i => dl (f i), c₀ + 1, max m₀ (c₀ + 1), fun m hm => ⟨Pf m, ?_, fun i => ?_⟩⟩
  · exact pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₀) (m - (c₀ + 1)) (Pf m) (by omega)
      (fun s _ => hCg _ _) (hPf m (by omega))
  · obtain ⟨w, hw, hLC⟩ := (hf i).2 m (by omega) hm m
    have hgu : IsUnit (Φ.ser (Pf m i)) :=
      (pWD l hl Ω A hA j Φ ζ hζ m (by omega) (Pf m i)).2
        (pv_mem_ne_zero_inv_mem_of_bPres β A ζ Z m _ (Pf m) (hPf m (by omega)) i)
    have hFu : IsUnit ((PowerSeries.map ((Φ.σ.symm : Φ.R →+* Φ.R) ^ m)) (f i)) := (hf i).1.map _
    have hD := pDlogCmp Φ.R l m (m - (c₀ + 1)) m (by omega) _ _ w hFu hgu hw hLC
    have hmin : min (m - (c₀ + 1)) (min (m - 1) m) = m - (c₀ + 1) := by omega
    rw [hmin] at hD
    unfold Fr.tw
    rw [map_dl_eq_dl_map_of_isUnit _ _ (hf i).1]
    exact hD
