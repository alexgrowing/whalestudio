import Formalism.LocalToGlobal.ProjectiveLattices.IntAtExtExtAll
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.LocalToGlobal.ProjectiveLattices.CurveInstSt

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

def PtOfSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) : Prop :=
  0 < wL.n → ∀ (L : Type) [Field L] [Algebra (Kp (recPlus h j hj) la G.N) L]
    (φ : OsK (recPlus h j hj) la G.w →ₐ[Kp (recPlus h j hj) la G.N] L),
    ∃ (alg : T.Q.c.F →+* L) (y : letI := alg.toAlgebra; FrPt (T.Q.Xo j) T.Q.c L),
      (letI := alg.toAlgebra; ∃ (Z : Comp (T.Q.Xo j) T.Q.c) (ψ : Om Z →ₐ[T.Q.c.F] L), FrMap ψ (genFr hG Z) y) ∧
      (∀ a : T.Q.c.F, alg a = algebraMap (Kp (recPlus h j hj) la G.N) L
        (@algebraMap ((recPlus h j hj).Kl la) (Kp (recPlus h j hj) la G.N) _ _ (Kp.algKl (recPlus h j hj) la G.N)
          (algebraMap T.Q.c.F ((recPlus h j hj).Kl la) a))) ∧
      letI := alg.toAlgebra
      (∑ k, algebraMap (Kp (recPlus h j hj) la G.N) L
          (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k))) *
          evR (T.Q.Xo j) T.Q.c ((G.w k : T.R j)) y) ≠ 0 ∧
      ∀ (k : ℕ) (g : (recB h.toLawsCore).Cusp j (addL (wt0 D j) wL k)),
        φ (toOsK (recPlus h j hj) la G.w (fr0 (recPlus h j hj) la G.w k
          ⟨emb (recPlus h j hj) la G.N ((recPlus h j hj).inc _ g), emb_mem_Vw (recPlus h j hj) la G.N _ g⟩)) =
        evR (T.Q.Xo j) T.Q.c ((g : T.R j)) y /
          (∑ k', algebraMap (Kp (recPlus h j hj) la G.N) L
            (algebraMap (Op (recPlus h j hj) la G.N) (Kp (recPlus h j hj) la G.N) (Tv (recPlus h j hj) la G.N (0, k'))) *
            evR (T.Q.Xo j) T.Q.c ((G.w k' : T.R j)) y) ^ k

def PtOfSInst (h : LawsP T) (j : ℕ) (hj : InR D j) : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore)),
    SpanW (recPlus h j hj) G.w S → BigAt h j hj hG G → PtOfSSt h j hj hG G la

end Formalism.L2.Pj
