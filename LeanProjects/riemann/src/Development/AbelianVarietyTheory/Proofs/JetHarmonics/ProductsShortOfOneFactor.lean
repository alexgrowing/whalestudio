import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem pow_mul_short_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (ka wL : WeightFamilies.Wt D j) (hka : ka.n = D.R.nV)
    (step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      X.emb wL (X.thAll wL) * X.emb w (X.shortTh w) ≤ X.emb (WeightAlgebra.wadd w wL) (X.shortTh (WeightAlgebra.wadd w wL))) :
    ∀ (t : ℕ) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → deg w + t • deg wL = deg ka →
      X.emb wL (X.thAll wL) ^ t * X.emb w (X.shortTh w) ≤ X.emb ka (X.shortTh ka) := by
  intro t
  induction t with
  | zero =>
    intro w _ e
    rw [zero_smul, add_zero] at e
    obtain rfl := deg_inj e
    rw [pow_zero, one_mul]
  | succ t ih =>
    intro w hr e
    have hn : w.n + (t + 1) * wL.n = ka.n := congrArg (fun x : Deg D j => x.2.2) e
    rw [pow_succ, mul_assoc]
    refine le_trans (mul_le_mul' le_rfl (step w hr fun h0 => ?_)) (ih (WeightAlgebra.wadd w wL) (hr.trans (Nat.le_add_right _ _)) ?_)
    · have h1 : (t + 1) * wL.n = 0 := by omega
      exact (Nat.mul_eq_zero.1 h1).resolve_left (Nat.succ_ne_zero t)
    · rw [deg_wadd, ← e, succ_nsmul]
      abel

theorem emb_mul_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    {w w' w'' : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {N' : Submodule (𝓞 B.KO) (B.Cusp j w')}
    {N'' : Submodule (𝓞 B.KO) (B.Cusp j w'')}
    (h : ∀ G ∈ N', ∀ F ∈ N, ∃ H ∈ N'', X.inc w'' H = X.inc w' G * X.inc w F) :
    X.emb w N * X.emb w' N' ≤ X.emb w'' N'' := by
  rw [mul_comm, Submodule.mul_le]
  rintro _ ⟨G, hG, rfl⟩ _ ⟨F, hF, rfl⟩
  exact h G hG F hF

theorem mul_mem_span_of_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {s t : Set R} {N : Submodule O R}
    (h : ∀ g ∈ s, ∀ f ∈ t, g * f ∈ N) {x y : R} (hx : x ∈ Submodule.span O s) (hy : y ∈ Submodule.span O t) :
    x * y ∈ N := by
  have hle : Submodule.span O s * Submodule.span O t ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨g, hg, f, hf, rfl⟩
    exact h g hg f hf
  exact hle (Submodule.mul_mem_mul hx hy)

theorem productsShort_of_oneFactor (one : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL))) : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn := by
  intro hC D T h j hj hsh hone hA ka wL wF Tn hF hn hD hr hka
  have step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      (recPJ h j hj).emb wL ((recPJ h j hj).thAll wL) * (recPJ h j hj).emb w ((recPJ h j hj).shortTh w) ≤
        (recPJ h j hj).emb (WeightAlgebra.wadd w wL) ((recPJ h j hj).shortTh (WeightAlgebra.wadd w wL)) := by
    intro w hw h0
    refine emb_mul_le (recPJ h j hj) fun G hG F hF' => ?_
    have hc : (G.1 : T.R j) * F.1 ∈ cutR T.C j (WeightAlgebra.wadd w wL) := by
      rw [cutR_eq T.C hj]
      exact h.toLawsCore.mul j hj w wL _ (cutR_le T.C j w G.2) _ (cutR_le T.C j wL F.2)
    refine ⟨⟨_, hc⟩, ?_, ?_⟩
    · exact mul_mem_span_of_gen (one hC D T h j hj hsh hone hA w wL hw h0) hG hF'
    · exact (incG_mul deg (cutR T.C j) (deg_wadd w wL) G F _).symm
  have key := pow_mul_short_le (recPJ h j hj) ka wL hka step
  have hdeg : deg wF + Tn • deg wL = deg ka := by
    obtain ⟨_, hP, hM⟩ := hF
    refine Prod.ext (funext fun τ => funext fun i => ?_) (Prod.ext (funext fun τ => funext fun i => ?_) hn.symm)
    · change wF.aP τ i + Tn * wL.aP τ i = ka.aP τ i
      have := hP τ i
      zify
      linarith
    · change wF.aM τ i + Tn * wL.aM τ i = ka.aM τ i
      have := hM τ i
      zify
      linarith
  refine sup_le (sup_le (key Tn wF hr hdeg) (key _ _ (hr.trans (Nat.le_add_right _ _)) ?_)) le_rfl
  have e : deg ((recPJ h j hj).wF0 wL wF) = deg wF + WeightFamilies.dimY D j • deg wL := rfl
  rw [e, add_assoc, ← add_nsmul, Nat.add_sub_of_le hD, hdeg]

end GlobalTheory.FormTies
