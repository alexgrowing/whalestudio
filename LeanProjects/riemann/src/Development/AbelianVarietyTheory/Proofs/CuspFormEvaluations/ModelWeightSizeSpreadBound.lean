import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.RunIn.WtSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {M : Type} [AddCommMonoid M] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : (E →+* ℂ) → M) :
    ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) = ∑ τ, g τ := by
  classical
  have hs : ∑ τ : X.Ψ, (g τ.1 + g (ComplexEmbedding.conjugate τ.1)) =
      ∑ τ ∈ X.Ψ, (g τ + g (ComplexEmbedding.conjugate τ)) :=
    Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))
  rw [hs, Finset.sum_add_distrib, ← Finset.sum_add_sum_compl X.Ψ g]
  congr 1
  refine Finset.sum_nbij' (fun τ => ComplexEmbedding.conjugate τ) (fun τ => ComplexEmbedding.conjugate τ)
    ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    simpa [Finset.mem_compl] using (X.cmType τ).1 hτ
  · intro τ hτ
    have h1 : τ ∉ X.Ψ := by simpa [Finset.mem_compl] using hτ
    by_contra h2
    exact h1 ((X.cmType τ).2 (by simpa using h2))
  · intro τ _
    simp
  · intro τ _
    simp
  · intro τ _
    rfl

theorem two_mul_card_cm {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * Fintype.card X.Ψ = Module.finrank ℚ E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  rw [← NumberField.Embeddings.card E ℂ, ← h]
  ring

theorem sum_row_le (r p0 : ℕ) (hp : p0 ≤ r) (u v : ℕ → ℕ) :
    ∑ j : Fin r, (if p0 ≤ (j : ℕ) then u ((j : ℕ) - p0) else v (p0 - 1 - (j : ℕ))) ≤
      ∑ i ∈ Finset.range r, u i + ∑ i ∈ Finset.range r, v i := by
  classical
  rw [Finset.sum_ite]
  gcongr
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ)), u ((j : ℕ) - p0)
          = ∑ i ∈ Finset.image (fun j : Fin r => (j : ℕ) - p0) (Finset.univ.filter (fun j : Fin r => p0 ≤ (j : ℕ))), u i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, u i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, _, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega
  · calc ∑ j ∈ Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ)), v (p0 - 1 - (j : ℕ))
          = ∑ i ∈ Finset.image (fun j : Fin r => p0 - 1 - (j : ℕ)) (Finset.univ.filter (fun j : Fin r => ¬ p0 ≤ (j : ℕ))), v i := by
            refine (Finset.sum_image ?_).symm
            intro a ha b hb hab
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
            dsimp only at hab
            exact Fin.ext (by omega)
      _ ≤ ∑ i ∈ Finset.range r, v i := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            obtain ⟨j, hj, rfl⟩ := hi
            simp only [Finset.mem_range]
            have := j.isLt
            omega

theorem spread_le {r : ℕ} (x b : Fin r → ℝ) (m : ℝ) (hm : 0 ≤ m) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, |x i| = b i + m) : (⨆ i, x i) - ⨅ i, x i ≤ ∑ i, b i + 2 * m := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · rw [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
    have : 0 ≤ ∑ i, b i := Finset.sum_nonneg (fun i _ => hb i)
    linarith
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := x)
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, ← hj]
    have hxi : x i ≤ b i + m := (le_abs_self _).trans (hx i).le
    have hxj : -(b j + m) ≤ x j := by
      have := neg_abs_le (x j)
      rw [hx j] at this
      exact this
    by_cases hij : i = j
    · subst hij
      have : 0 ≤ ∑ k, b k := Finset.sum_nonneg (fun k _ => hb k)
      linarith
    · have hpair : b i + b j ≤ ∑ k, b k := by
        rw [← Finset.sum_pair hij]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hb k)
      linarith

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_bijective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Bijective (relab (E := E) c σ) := by
  have hinj : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' hττ'
    unfold relab embF at hττ'
    ext x
    have h1 := congrArg (fun f : E →+* ℂ => f x) hττ'
    simp only [RingHom.comp_apply] at h1
    exact congrArg Subtype.val (σ.injective h1)
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private lemma entry_abs (p0 j s t h : ℕ) :
    |(((if p0 ≤ j then (s : ℤ) + (h : ℤ) else -(t : ℤ) - (h : ℤ) : ℤ)) : ℝ)| =
      (((if p0 ≤ j then s else t : ℕ)) : ℝ) + (h : ℝ) := by
  split_ifs with hj
  · push_cast
    exact abs_of_nonneg (by positivity)
  · push_cast
    rw [abs_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) t, Nat.cast_nonneg (α := ℝ) h])]
    ring

theorem laU_bounds (U : Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) (B : ℕ)
    (hB : ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) ≤ B) :
    (∑ τ, (U.X k).spread (laU U a n k) τ) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n ∧
      (∑ τ, ∑ i, |((laU U a n k τ i : ℤ) : ℝ)|) ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
  unfold laU
  have hp : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hbij := relab_bijective (E := E) c σ
  have hm2 : 2 * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    exact_mod_cast this
  have htot : ∑ τ : (U.X k).Ψ, (∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) ≤ B := by
    have hinvb : Function.Bijective (Function.invFun (relab (E := E) c σ)) :=
      ⟨(Function.rightInverse_invFun hbij.2).injective, (Function.leftInverse_invFun hbij.1).surjective⟩
    calc _ = ∑ τ : (U.X k).Ψ, ((fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ.1 +
            (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) (ComplexEmbedding.conjugate τ.1)) := rfl
      _ = ∑ τ, (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i)) τ :=
          sum_cm (U.X k) (fun τ' => ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ', i))
      _ = ∑ τ, ∑ i ∈ Finset.range r, a (τ, i) := Fintype.sum_bijective _ hinvb _ _ (fun _ => rfl)
      _ ≤ B := hB
  have hsum : ∑ τ : (U.X k).Ψ, ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) ≤ (B : ℝ) := by
    calc _ ≤ ∑ τ : (U.X k).Ψ, (((∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) τ.1, i) + ∑ i ∈ Finset.range r, a (Function.invFun (relab c σ) (conjEmb τ.1), i)) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro τ _
          rw [← Nat.cast_sum]
          exact_mod_cast sum_row_le r (U.X k).p0 hp (fun i => a (Function.invFun (relab c σ) τ.1, i))
            (fun i => a (Function.invFun (relab c σ) (conjEmb τ.1), i))
      _ ≤ (B : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast htot
  have h0 : (0 : ℝ) ≤ Fintype.card (U.X k).Ψ := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  constructor
  · calc _ ≤ ∑ τ : (U.X k).Ψ, (∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + 2 * ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro τ _
          unfold ReciprocityTheory.ChartRestriction.G.FD.Data.spread
          exact spread_le _ _ _ (by positivity) (fun j => by positivity) (fun j => entry_abs _ _ _ _ _)
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * n := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 h0]
  · calc _ = ∑ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro τ _
          apply Finset.sum_congr rfl
          intro j _
          exact entry_abs _ _ _ _ _
      _ ≤ (B : ℝ) + Fintype.card (U.X k).Ψ * r * n / 2 := by
          have e : ∀ τ : (U.X k).Ψ, ∑ j : Fin r, ((((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ)) = ∑ j : Fin r, (((if (U.X k).p0 ≤ (j : ℕ) then a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0) else a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (j : ℕ)) : ℕ)) : ℝ) + r * ((n / 2 : ℕ) : ℝ) := by
            intro τ
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_congr rfl (fun τ _ => e τ), Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          nlinarith [hsum, mul_le_mul_of_nonneg_left hm2 (mul_nonneg h0 hr0)]

theorem sum_wtA_le {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (m : ℕ) :
    ∑ τ, ∑ i ∈ Finset.range m, wtA w (τ, i) ≤ WeightAlgebra.DF w := by
  classical
  unfold wtA WeightAlgebra.DF WeightAlgebra.degP ext0
  have key : ∀ (q : ℕ) (g : Fin q → ℕ),
      ∑ i ∈ Finset.range m, (if h : i < q then g ⟨i, h⟩ else 0) ≤ ∑ i, g i := by
    intro q g
    calc _ ≤ ∑ i ∈ Finset.range q, (if h : i < q then g ⟨i, h⟩ else 0) := by
          apply Finset.sum_le_sum_of_ne_zero
          intro i _ hi
          rw [Finset.mem_range]
          by_contra hc
          exact hi (dif_neg hc)
      _ = ∑ i, g i := by
          rw [Finset.sum_range]
          simp
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_le_sum (fun t _ => ?_)
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact add_le_add (key _ _) (key _ _)

theorem laU_wtA_size : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * w.n ∧ (∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ (WeightAlgebra.DF w : ℝ) + D.R.f * D.R.r * w.n / 2 := by
  intro D T h j hj w σ hσ k
  have h2 := two_mul_card_cm ((T.U j σ).X k)
  have h3 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h4 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.der.finrank_E
    rw [h4]
    simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hc : (Fintype.card ((T.U j σ).X k).Ψ : ℝ) = D.R.f := by
    have : Fintype.card ((T.U j σ).X k).Ψ = D.R.f := by omega
    exact_mod_cast this
  have hb := laU_bounds (T.U j σ) (wtA w) w.n k (WeightAlgebra.DF w) (sum_wtA_le w _)
  rw [hc] at hb
  exact hb

end GlobalTheory.RunIn.WtSize
