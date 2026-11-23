import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem chrUnr_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {χ : Chr (maximalRealSubfield E) E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (k : ℕ) :
    UnrAt (χ ^ k) w := by
  induction k with
  | zero =>
    intro x _
    simp [locChar]
  | succ n ih =>
    rw [pow_succ]
    exact UnrAt.mul ih h

private theorem chrVal_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    (χ : Chr (maximalRealSubfield E) E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    ((val (χ ^ k) w : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ k := by
  induction k with
  | zero => simp [val_one]
  | succ n ih => rw [pow_succ, val_mul, Units.val_mul, ih, pow_succ]

theorem UpperTheory.Gal.TP.Chr.chrPairs :
    UpperTheory.Gal.TP.Chr.ChrEx → UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Sub.ChrPairs := by
  intro hEx hTyp E _ _ _ hunr n t hn ht emb b w₀ _
  obtain ⟨K, hKodd, hKb⟩ : ∃ K : ℕ, Odd K ∧ -(K : ℤ) ≤ b :=
    ⟨2 * b.natAbs + 1, ⟨b.natAbs, rfl⟩, by omega⟩
  obtain ⟨χ, ψ, hχ0, hH, hV, hA, hInj⟩ :=
    hEx E hunr emb w₀ (fun _ => -1) (fun _ => ⟨-1, by norm_num⟩)
  have hT := hTyp E emb
  have hnorm : ∀ w : HeightOneSpectrum (𝓞 E),
      ((normV w : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := by
    intro w
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨a, ha⟩ := hKodd
  obtain ⟨c, hc⟩ := ht
  obtain ⟨r, hr⟩ := hn
  have ht0 : 0 < t := by omega
  refine ⟨ψ K t,
    typ emb (fun _ => ((t : ℤ) + (K : ℤ) * -1) / 2) (fun _ => ((t : ℤ) - (K : ℤ) * -1) / 2),
    fun j => χ ^ (2 * (j : ℕ)), fun j => χ ^ (K + 2 * (j : ℕ)),
    fun j _ => ((2 * (j : ℕ) : ℕ) : ℤ) * -1, fun j _ => ((K + 2 * (j : ℕ) : ℕ) : ℤ) * -1,
    fun j i => ψ (2 * (j : ℕ)) (2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)),
    fun j i => typ emb
      (fun _ => ((2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)) + ((2 * (j : ℕ) : ℕ) : ℤ) * -1) / 2)
      (fun _ => ((2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)) - ((2 * (j : ℕ) : ℕ) : ℤ) * -1) / 2),
    hA _ _ ⟨a + c + 1, by subst ha hc; push_cast; ring⟩, ?_, ?_,
    (hV K t w₀).1.mpr (chrUnr_pow hχ0 K), fun i => (hV _ _ w₀).1.mpr (chrUnr_pow hχ0 _)⟩
  · intro j
    obtain ⟨h1, h2, h3⟩ := hH (2 * (j : ℕ))
    obtain ⟨h1', h2', h3'⟩ := hH (K + 2 * (j : ℕ))
    refine ⟨h1, h1', h3 n (by omega), h3' (n + t) (by omega), h2, h2', ?_, ?_⟩
    · intro w
      push_cast
      omega
    · refine ⟨fun i => hA _ _ ⟨((j : ℕ) : ℤ) + ((i : ℕ) : ℤ) - r - 2 * c, by push_cast; omega⟩,
        fun w => ?_, fun w => ?_, fun i w => ?_, fun i w => ?_, fun w hκ hψ => ?_⟩
      · dsimp only
        rw [(hT _ _ w).1]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).2]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).1]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).2]
        push_cast
        omega
      · dsimp only at hψ ⊢
        have u0 := (hV K t w).1.mp hκ
        have ux := (hV (2 * (j : ℕ)) _ w).1.mp (hψ ⟨0, ht0⟩)
        have hv : ((val χ w : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        refine ⟨ux, by rw [pow_add]; exact UnrAt.mul u0 ux, ?_, fun i => ?_⟩
        · rw [(hV K t w).2, chrVal_pow, chrVal_pow, hnorm, pow_add,
            mul_inv_cancel_right₀ (pow_ne_zero _ hv)]
          push_cast
          rw [neg_div]
        · rw [(hV _ _ w).2, chrVal_pow, hnorm]
          congr 2
          push_cast
          ring
  · intro i i' h
    have := hInj _ _ _ _ h
    simp at this
